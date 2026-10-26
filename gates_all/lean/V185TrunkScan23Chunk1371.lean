import V185TrunkScan23Chunk1370

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8119961 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 2, 4, 2]
def baseStart_8119961 : Nat := 118140960795 + 8119961 * 2 ^ 59
def prefixEnd_8119961 : Nat := 4983230072969 + 3 ^ 40 * 8119961 * 2
def baseEnd_8119961 : Nat := 4169442888762810348944485

theorem tailTrace_8119961 : CollatzResearch.WordTrace tailWord_8119961 prefixEnd_8119961 4169442888762810348944485 := by
  unfold tailWord_8119961
  simp only [CollatzResearch.WordTrace]
  refine ⟨296159308135775550776799737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197439538757183700517866491 296159308135775550776799737)
  ·
    refine ⟨222119481101831663082599803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296159308135775550776799737 222119481101831663082599803)
    ·
      refine ⟨333179221652747494623899705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222119481101831663082599803 333179221652747494623899705)
      ·
        refine ⟨249884416239560620967924779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333179221652747494623899705 249884416239560620967924779)
        ·
          refine ⟨374826624359340931451887169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249884416239560620967924779 374826624359340931451887169)
          ·
            refine ⟨281119968269505698588915377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374826624359340931451887169 281119968269505698588915377)
            ·
              refine ⟨210839976202129273941686533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281119968269505698588915377 210839976202129273941686533)
              ·
                refine ⟨39532495537899238864066225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210839976202129273941686533 39532495537899238864066225)
                ·
                  refine ⟨29649371653424429148049669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39532495537899238864066225 29649371653424429148049669)
                  ·
                    refine ⟨5559257185017080465259313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29649371653424429148049669 5559257185017080465259313)
                    ·
                      refine ⟨4169442888762810348944485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5559257185017080465259313 4169442888762810348944485)
                      ·
                        rfl

theorem cell23_8119961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 4, 2].length) (baseStart_8119961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119961 prefixEnd_8119961 := by exact prefixLift 8119961
  have htrace : WordTrace (prefixWord ++ tailWord_8119961) baseStart_8119961 baseEnd_8119961 := by
    simpa [prefixWord, tailWord_8119961, baseEnd_8119961] using wordTrace_append hprefix tailTrace_8119961
  have hstable : (prefixWord ++ tailWord_8119961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119961).length < 2 ^ (prefixWord ++ tailWord_8119961).sum := by decide
  have hdescent : baseEnd_8119961 < baseStart_8119961 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8119998 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_8119998 : Nat := 118140960795 + 8119998 * 2 ^ 59
def prefixEnd_8119998 : Nat := 4983230072969 + 3 ^ 40 * 8119998 * 2
def baseEnd_8119998 : Nat := 4169461887547026704181815

theorem tailTrace_8119998 : CollatzResearch.WordTrace tailWord_8119998 prefixEnd_8119998 4169461887547026704181815 := by
  unfold tailWord_8119998
  simp only [CollatzResearch.WordTrace]
  refine ⟨37020082204580188261987081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197440438424427670730597765 37020082204580188261987081)
  ·
    refine ⟨27765061653435141196490311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37020082204580188261987081 27765061653435141196490311)
    ·
      refine ⟨41647592480152711794735467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27765061653435141196490311 41647592480152711794735467)
      ·
        refine ⟨62471388720229067692103201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41647592480152711794735467 62471388720229067692103201)
        ·
          refine ⟨46853541540171800769077401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62471388720229067692103201 46853541540171800769077401)
          ·
            refine ⟨35140156155128850576808051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46853541540171800769077401 35140156155128850576808051)
            ·
              refine ⟨52710234232693275865212077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35140156155128850576808051 52710234232693275865212077)
              ·
                refine ⟨19766337837259978449454529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52710234232693275865212077 19766337837259978449454529)
                ·
                  refine ⟨14824753377944983837090897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19766337837259978449454529 14824753377944983837090897)
                  ·
                    refine ⟨11118565033458737877818173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14824753377944983837090897 11118565033458737877818173)
                    ·
                      refine ⟨4169461887547026704181815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11118565033458737877818173 4169461887547026704181815)
                      ·
                        rfl

theorem cell23_8119998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_8119998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8119998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8119998 prefixEnd_8119998 := by exact prefixLift 8119998
  have htrace : WordTrace (prefixWord ++ tailWord_8119998) baseStart_8119998 baseEnd_8119998 := by
    simpa [prefixWord, tailWord_8119998, baseEnd_8119998] using wordTrace_append hprefix tailTrace_8119998
  have hstable : (prefixWord ++ tailWord_8119998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8119998).length < 2 ^ (prefixWord ++ tailWord_8119998).sum := by decide
  have hdescent : baseEnd_8119998 < baseStart_8119998 := by decide
  rcases family_descends (prefixWord ++ tailWord_8119998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120018 : List Nat := [3, 2, 2, 2, 2, 2, 2, 2, 6]
def baseStart_8120018 : Nat := 118140960795 + 8120018 * 2 ^ 59
def prefixEnd_8120018 : Nat := 4983230072969 + 3 ^ 40 * 8120018 * 2
def baseEnd_8120018 : Nat := 463274684128901847325747

theorem tailTrace_8120018 : CollatzResearch.WordTrace tailWord_8120018 prefixEnd_8120018 463274684128901847325747 := by
  unfold tailWord_8120018
  simp only [CollatzResearch.WordTrace]
  refine ⟨74040346774142262377906177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197440924731046033007749805 74040346774142262377906177)
  ·
    refine ⟨55530260080606696783429633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74040346774142262377906177 55530260080606696783429633)
    ·
      refine ⟨41647695060455022587572225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55530260080606696783429633 41647695060455022587572225)
      ·
        refine ⟨31235771295341266940679169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41647695060455022587572225 31235771295341266940679169)
        ·
          refine ⟨23426828471505950205509377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31235771295341266940679169 23426828471505950205509377)
          ·
            refine ⟨17570121353629462654132033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23426828471505950205509377 17570121353629462654132033)
            ·
              refine ⟨13177591015222096990599025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17570121353629462654132033 13177591015222096990599025)
              ·
                refine ⟨9883193261416572742949269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13177591015222096990599025 9883193261416572742949269)
                ·
                  refine ⟨463274684128901847325747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9883193261416572742949269 463274684128901847325747)
                  ·
                    rfl

theorem cell23_8120018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_8120018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120018 prefixEnd_8120018 := by exact prefixLift 8120018
  have htrace : WordTrace (prefixWord ++ tailWord_8120018) baseStart_8120018 baseEnd_8120018 := by
    simpa [prefixWord, tailWord_8120018, baseEnd_8120018] using wordTrace_append hprefix tailTrace_8120018
  have hstable : (prefixWord ++ tailWord_8120018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120018).length < 2 ^ (prefixWord ++ tailWord_8120018).sum := by decide
  have hdescent : baseEnd_8120018 < baseStart_8120018 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120045 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_8120045 : Nat := 118140960795 + 8120045 * 2 ^ 59
def prefixEnd_8120045 : Nat := 4983230072969 + 3 ^ 40 * 8120045 * 2
def baseEnd_8120045 : Nat := 4169486021137788020294099

theorem tailTrace_8120045 : CollatzResearch.WordTrace tailWord_8120045 prefixEnd_8120045 4169486021137788020294099 := by
  unfold tailWord_8120045
  simp only [CollatzResearch.WordTrace]
  refine ⟨296162371867471233122857589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197441581244980822081905059 296162371867471233122857589)
  ·
    refine ⟨27765222362575428105267899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 296162371867471233122857589 27765222362575428105267899)
    ·
      refine ⟨41647833543863142157901849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27765222362575428105267899 41647833543863142157901849)
      ·
        refine ⟨31235875157897356618426387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41647833543863142157901849 31235875157897356618426387)
        ·
          refine ⟨46853812736846034927639581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31235875157897356618426387 46853812736846034927639581)
          ·
            refine ⟨17570179776317263097864843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46853812736846034927639581 17570179776317263097864843)
            ·
              refine ⟨26355269664475894646797265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17570179776317263097864843 26355269664475894646797265)
              ·
                refine ⟨19766452248356920985097949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26355269664475894646797265 19766452248356920985097949)
                ·
                  refine ⟨7412419593133845369411731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19766452248356920985097949 7412419593133845369411731)
                  ·
                    refine ⟨11118629389700768054117597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7412419593133845369411731 11118629389700768054117597)
                    ·
                      refine ⟨4169486021137788020294099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11118629389700768054117597 4169486021137788020294099)
                      ·
                        rfl

theorem cell23_8120045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_8120045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120045 prefixEnd_8120045 := by exact prefixLift 8120045
  have htrace : WordTrace (prefixWord ++ tailWord_8120045) baseStart_8120045 baseEnd_8120045 := by
    simpa [prefixWord, tailWord_8120045, baseEnd_8120045] using wordTrace_append hprefix tailTrace_8120045
  have hstable : (prefixWord ++ tailWord_8120045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120045).length < 2 ^ (prefixWord ++ tailWord_8120045).sum := by decide
  have hdescent : baseEnd_8120045 < baseStart_8120045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120051 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 4]
def baseStart_8120051 : Nat := 118140960795 + 8120051 * 2 ^ 59
def prefixEnd_8120051 : Nat := 4983230072969 + 3 ^ 40 * 8120051 * 2
def baseEnd_8120051 : Nat := 4169489102021714996819071

theorem tailTrace_8120051 : CollatzResearch.WordTrace tailWord_8120051 prefixEnd_8120051 4169489102021714996819071 := by
  unfold tailWord_8120051
  simp only [CollatzResearch.WordTrace]
  refine ⟨296162590705449496147576007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197441727136966330765050671 296162590705449496147576007)
  ·
    refine ⟨444243886058174244221364011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296162590705449496147576007 444243886058174244221364011)
    ·
      refine ⟨666365829087261366332046017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444243886058174244221364011 666365829087261366332046017)
      ·
        refine ⟨499774371815446024749034513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666365829087261366332046017 499774371815446024749034513)
        ·
          refine ⟨374830778861584518561775885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499774371815446024749034513 374830778861584518561775885)
          ·
            refine ⟨140561542073094194460665957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374830778861584518561775885 140561542073094194460665957)
            ·
              refine ⟨26355289138705161461374867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140561542073094194460665957 26355289138705161461374867)
              ·
                refine ⟨39532933708057742192062301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26355289138705161461374867 39532933708057742192062301)
                ·
                  refine ⟨14824850140521653322023363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39532933708057742192062301 14824850140521653322023363)
                  ·
                    refine ⟨22237275210782479983035045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14824850140521653322023363 22237275210782479983035045)
                    ·
                      refine ⟨4169489102021714996819071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22237275210782479983035045 4169489102021714996819071)
                      ·
                        rfl

theorem cell23_8120051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 4].length) (baseStart_8120051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120051 prefixEnd_8120051 := by exact prefixLift 8120051
  have htrace : WordTrace (prefixWord ++ tailWord_8120051) baseStart_8120051 baseEnd_8120051 := by
    simpa [prefixWord, tailWord_8120051, baseEnd_8120051] using wordTrace_append hprefix tailTrace_8120051
  have hstable : (prefixWord ++ tailWord_8120051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120051).length < 2 ^ (prefixWord ++ tailWord_8120051).sum := by decide
  have hdescent : baseEnd_8120051 < baseStart_8120051 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120085 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 3, 2, 2]
def baseStart_8120085 : Nat := 118140960795 + 8120085 * 2 ^ 59
def prefixEnd_8120085 : Nat := 4983230072969 + 3 ^ 40 * 8120085 * 2
def baseEnd_8120085 : Nat := 4169506560363967863793915

theorem tailTrace_8120085 : CollatzResearch.WordTrace tailWord_8120085 prefixEnd_8120085 4169506560363967863793915 := by
  unfold tailWord_8120085
  simp only [CollatzResearch.WordTrace]
  refine ⟨296163830787326319954313709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197442553858217546636209139 296163830787326319954313709)
  ·
    refine ⟨111061436545247369982867641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296163830787326319954313709 111061436545247369982867641)
    ·
      refine ⟨83296077408935527487150731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111061436545247369982867641 83296077408935527487150731)
      ·
        refine ⟨124944116113403291230726097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83296077408935527487150731 124944116113403291230726097)
        ·
          refine ⟨93708087085052468423044573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124944116113403291230726097 93708087085052468423044573)
          ·
            refine ⟨35140532656894675658641715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93708087085052468423044573 35140532656894675658641715)
            ·
              refine ⟨52710798985342013487962573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35140532656894675658641715 52710798985342013487962573)
              ·
                refine ⟨19766549619503255057985965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52710798985342013487962573 19766549619503255057985965)
                ·
                  refine ⟨7412456107313720646744737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19766549619503255057985965 7412456107313720646744737)
                  ·
                    refine ⟨5559342080485290485058553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7412456107313720646744737 5559342080485290485058553)
                    ·
                      refine ⟨4169506560363967863793915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5559342080485290485058553 4169506560363967863793915)
                      ·
                        rfl

theorem cell23_8120085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_8120085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120085 prefixEnd_8120085 := by exact prefixLift 8120085
  have htrace : WordTrace (prefixWord ++ tailWord_8120085) baseStart_8120085 baseEnd_8120085 := by
    simpa [prefixWord, tailWord_8120085, baseEnd_8120085] using wordTrace_append hprefix tailTrace_8120085
  have hstable : (prefixWord ++ tailWord_8120085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120085).length < 2 ^ (prefixWord ++ tailWord_8120085).sum := by decide
  have hdescent : baseEnd_8120085 < baseStart_8120085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120095 : List Nat := [1, 1, 2, 4, 2, 1, 5, 1, 2, 4]
def baseStart_8120095 : Nat := 118140960795 + 8120095 * 2 ^ 59
def prefixEnd_8120095 : Nat := 4983230072969 + 3 ^ 40 * 8120095 * 2
def baseEnd_8120095 : Nat := 1389837231723504274889623

theorem tailTrace_8120095 : CollatzResearch.WordTrace tailWord_8120095 prefixEnd_8120095 1389837231723504274889623 := by
  unfold tailWord_8120095
  simp only [CollatzResearch.WordTrace]
  refine ⟨296164195517290091662177739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197442797011526727774785159 296164195517290091662177739)
  ·
    refine ⟨444246293275935137493266609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296164195517290091662177739 444246293275935137493266609)
    ·
      refine ⟨333184719956951353119949957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444246293275935137493266609 333184719956951353119949957)
      ·
        refine ⟨62472134991928378709990617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333184719956951353119949957 62472134991928378709990617)
        ·
          refine ⟨46854101243946284032492963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62472134991928378709990617 46854101243946284032492963)
          ·
            refine ⟨70281151865919426048739445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46854101243946284032492963 70281151865919426048739445)
            ·
              refine ⟨6588857987429946192069323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70281151865919426048739445 6588857987429946192069323)
              ·
                refine ⟨9883286981144919288103985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6588857987429946192069323 9883286981144919288103985)
                ·
                  refine ⟨7412465235858689466077989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9883286981144919288103985 7412465235858689466077989)
                  ·
                    refine ⟨1389837231723504274889623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7412465235858689466077989 1389837231723504274889623)
                    ·
                      rfl

theorem cell23_8120095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 2, 4].length) (baseStart_8120095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120095 prefixEnd_8120095 := by exact prefixLift 8120095
  have htrace : WordTrace (prefixWord ++ tailWord_8120095) baseStart_8120095 baseEnd_8120095 := by
    simpa [prefixWord, tailWord_8120095, baseEnd_8120095] using wordTrace_append hprefix tailTrace_8120095
  have hstable : (prefixWord ++ tailWord_8120095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120095).length < 2 ^ (prefixWord ++ tailWord_8120095).sum := by decide
  have hdescent : baseEnd_8120095 < baseStart_8120095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120108 : List Nat := [2, 2, 1, 1, 1, 7, 2, 7]
def baseStart_8120108 : Nat := 118140960795 + 8120108 * 2 ^ 59
def prefixEnd_8120108 : Nat := 4983230072969 + 3 ^ 40 * 8120108 * 2
def baseEnd_8120108 : Nat := 154426606311815602733567

theorem tailTrace_8120108 : CollatzResearch.WordTrace tailWord_8120108 prefixEnd_8120108 154426606311815602733567 := by
  unfold tailWord_8120108
  simp only [CollatzResearch.WordTrace]
  refine ⟨148082334833121497441200489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197443113110828663254933985 148082334833121497441200489)
  ·
    refine ⟨111061751124841123080900367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148082334833121497441200489 111061751124841123080900367)
    ·
      refine ⟨166592626687261684621350551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111061751124841123080900367 166592626687261684621350551)
      ·
        refine ⟨249888940030892526932025827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166592626687261684621350551 249888940030892526932025827)
        ·
          refine ⟨374833410046338790398038741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249888940030892526932025827 374833410046338790398038741)
          ·
            refine ⟨8785158047961065399954033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 374833410046338790398038741 8785158047961065399954033)
            ·
              refine ⟨6588868535970799049965525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8785158047961065399954033 6588868535970799049965525)
              ·
                refine ⟨154426606311815602733567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6588868535970799049965525 154426606311815602733567)
                ·
                  rfl

theorem cell23_8120108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 7].length) (baseStart_8120108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120108 prefixEnd_8120108 := by exact prefixLift 8120108
  have htrace : WordTrace (prefixWord ++ tailWord_8120108) baseStart_8120108 baseEnd_8120108 := by
    simpa [prefixWord, tailWord_8120108, baseEnd_8120108] using wordTrace_append hprefix tailTrace_8120108
  have hstable : (prefixWord ++ tailWord_8120108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120108).length < 2 ^ (prefixWord ++ tailWord_8120108).sum := by decide
  have hdescent : baseEnd_8120108 < baseStart_8120108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120128 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 7, 3, 2]
def baseStart_8120128 : Nat := 118140960795 + 8120128 * 2 ^ 59
def prefixEnd_8120128 : Nat := 4983230072969 + 3 ^ 40 * 8120128 * 2
def baseEnd_8120128 : Nat := 4169528640032111195556217

theorem tailTrace_8120128 : CollatzResearch.WordTrace tailWord_8120128 prefixEnd_8120128 4169528640032111195556217 := by
  unfold tailWord_8120128
  simp only [CollatzResearch.WordTrace]
  refine ⟨148082699563085269149064519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197443599417447025532086025 148082699563085269149064519)
  ·
    refine ⟨222124049344627903723596779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148082699563085269149064519 222124049344627903723596779)
    ·
      refine ⟨333186074016941855585395169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222124049344627903723596779 333186074016941855585395169)
      ·
        refine ⟨249889555512706391689046377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333186074016941855585395169 249889555512706391689046377)
        ·
          refine ⟨187417166634529793766784783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249889555512706391689046377 187417166634529793766784783)
          ·
            refine ⟨281125749951794690650177175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187417166634529793766784783 281125749951794690650177175)
            ·
              refine ⟨421688624927692035975265763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281125749951794690650177175 421688624927692035975265763)
              ·
                refine ⟨632532937391538053962898645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421688624927692035975265763 632532937391538053962898645)
                ·
                  refine ⟨14824990720114173139755437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 632532937391538053962898645 14824990720114173139755437)
                  ·
                    refine ⟨5559371520042814927408289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14824990720114173139755437 5559371520042814927408289)
                    ·
                      refine ⟨4169528640032111195556217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5559371520042814927408289 4169528640032111195556217)
                      ·
                        rfl

theorem cell23_8120128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 7, 3, 2].length) (baseStart_8120128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120128 prefixEnd_8120128 := by exact prefixLift 8120128
  have htrace : WordTrace (prefixWord ++ tailWord_8120128) baseStart_8120128 baseEnd_8120128 := by
    simpa [prefixWord, tailWord_8120128, baseEnd_8120128] using wordTrace_append hprefix tailTrace_8120128
  have hstable : (prefixWord ++ tailWord_8120128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120128).length < 2 ^ (prefixWord ++ tailWord_8120128).sum := by decide
  have hdescent : baseEnd_8120128 < baseStart_8120128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120161 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_8120161 : Nat := 118140960795 + 8120161 * 2 ^ 59
def prefixEnd_8120161 : Nat := 4983230072969 + 3 ^ 40 * 8120161 * 2
def baseEnd_8120161 : Nat := 4169545584893709566443565

theorem tailTrace_8120161 : CollatzResearch.WordTrace tailWord_8120161 prefixEnd_8120161 4169545584893709566443565 := by
  unfold tailWord_8120161
  simp only [CollatzResearch.WordTrace]
  refine ⟨296166602735050984934080337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197444401823367323289386891 296166602735050984934080337)
  ·
    refine ⟨222124952051288238700560253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296166602735050984934080337 222124952051288238700560253)
    ·
      refine ⟨83296857019233089512710095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222124952051288238700560253 83296857019233089512710095)
      ·
        refine ⟨124945285528849634269065143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83296857019233089512710095 124945285528849634269065143)
        ·
          refine ⟨187417928293274451403597715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124945285528849634269065143 187417928293274451403597715)
          ·
            refine ⟨281126892439911677105396573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187417928293274451403597715 281126892439911677105396573)
            ·
              refine ⟨105422584664966878914523715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281126892439911677105396573 105422584664966878914523715)
              ·
                refine ⟨158133876997450318371785573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105422584664966878914523715 158133876997450318371785573)
                ·
                  refine ⟨29650101937021934694709795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158133876997450318371785573 29650101937021934694709795)
                  ·
                    refine ⟨44475152905532902042064693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29650101937021934694709795 44475152905532902042064693)
                    ·
                      refine ⟨4169545584893709566443565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44475152905532902042064693 4169545584893709566443565)
                      ·
                        rfl

theorem cell23_8120161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_8120161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120161 prefixEnd_8120161 := by exact prefixLift 8120161
  have htrace : WordTrace (prefixWord ++ tailWord_8120161) baseStart_8120161 baseEnd_8120161 := by
    simpa [prefixWord, tailWord_8120161, baseEnd_8120161] using wordTrace_append hprefix tailTrace_8120161
  have hstable : (prefixWord ++ tailWord_8120161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120161).length < 2 ^ (prefixWord ++ tailWord_8120161).sum := by decide
  have hdescent : baseEnd_8120161 < baseStart_8120161 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120162 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_8120162 : Nat := 118140960795 + 8120162 * 2 ^ 59
def prefixEnd_8120162 : Nat := 4983230072969 + 3 ^ 40 * 8120162 * 2
def baseEnd_8120162 : Nat := 4169546098374364062531061

theorem tailTrace_8120162 : CollatzResearch.WordTrace tailWord_8120162 prefixEnd_8120162 4169546098374364062531061 := by
  unfold tailWord_8120162
  simp only [CollatzResearch.WordTrace]
  refine ⟨74041659802011840526216685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197444426138698241403244493 74041659802011840526216685)
  ·
    refine ⟨27765622425754440197331257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74041659802011840526216685 27765622425754440197331257)
    ·
      refine ⟨20824216819315830147998443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27765622425754440197331257 20824216819315830147998443)
      ·
        refine ⟨31236325228973745221997665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20824216819315830147998443 31236325228973745221997665)
        ·
          refine ⟨23427243921730308916498249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31236325228973745221997665 23427243921730308916498249)
          ·
            refine ⟨17570432941297731687373687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23427243921730308916498249 17570432941297731687373687)
            ·
              refine ⟨26355649411946597531060531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17570432941297731687373687 26355649411946597531060531)
              ·
                refine ⟨39533474117919896296590797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26355649411946597531060531 39533474117919896296590797)
                ·
                  refine ⟨14825052794219961111221549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39533474117919896296590797 14825052794219961111221549)
                  ·
                    refine ⟨5559394797832485416708081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14825052794219961111221549 5559394797832485416708081)
                    ·
                      refine ⟨4169546098374364062531061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5559394797832485416708081 4169546098374364062531061)
                      ·
                        rfl

theorem cell23_8120162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_8120162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120162 prefixEnd_8120162 := by exact prefixLift 8120162
  have htrace : WordTrace (prefixWord ++ tailWord_8120162) baseStart_8120162 baseEnd_8120162 := by
    simpa [prefixWord, tailWord_8120162, baseEnd_8120162] using wordTrace_append hprefix tailTrace_8120162
  have hstable : (prefixWord ++ tailWord_8120162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120162).length < 2 ^ (prefixWord ++ tailWord_8120162).sum := by decide
  have hdescent : baseEnd_8120162 < baseStart_8120162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120171 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 4]
def baseStart_8120171 : Nat := 118140960795 + 8120171 * 2 ^ 59
def prefixEnd_8120171 : Nat := 4983230072969 + 3 ^ 40 * 8120171 * 2
def baseEnd_8120171 : Nat := 4169550719700254527318519

theorem tailTrace_8120171 : CollatzResearch.WordTrace tailWord_8120171 prefixEnd_8120171 4169550719700254527318519 := by
  unfold tailWord_8120171
  simp only [CollatzResearch.WordTrace]
  refine ⟨296166967465014756641944367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197444644976676504427962911 296166967465014756641944367)
  ·
    refine ⟨444250451197522134962916551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296166967465014756641944367 444250451197522134962916551)
    ·
      refine ⟨666375676796283202444374827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444250451197522134962916551 666375676796283202444374827)
      ·
        refine ⟨999563515194424803666562241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666375676796283202444374827 999563515194424803666562241)
        ·
          refine ⟨749672636395818602749921681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 999563515194424803666562241 749672636395818602749921681)
          ·
            refine ⟨562254477296863952062441261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 749672636395818602749921681 562254477296863952062441261)
            ·
              refine ⟨210845428986323982023415473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 562254477296863952062441261 210845428986323982023415473)
              ·
                refine ⟨158134071739742986517561605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210845428986323982023415473 158134071739742986517561605)
                ·
                  refine ⟨29650138451201809972042801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158134071739742986517561605 29650138451201809972042801)
                  ·
                    refine ⟨22237603838401357479032101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29650138451201809972042801 22237603838401357479032101)
                    ·
                      refine ⟨4169550719700254527318519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22237603838401357479032101 4169550719700254527318519)
                      ·
                        rfl

theorem cell23_8120171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 4].length) (baseStart_8120171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120171 prefixEnd_8120171 := by exact prefixLift 8120171
  have htrace : WordTrace (prefixWord ++ tailWord_8120171) baseStart_8120171 baseEnd_8120171 := by
    simpa [prefixWord, tailWord_8120171, baseEnd_8120171] using wordTrace_append hprefix tailTrace_8120171
  have hstable : (prefixWord ++ tailWord_8120171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120171).length < 2 ^ (prefixWord ++ tailWord_8120171).sum := by decide
  have hdescent : baseEnd_8120171 < baseStart_8120171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120192 : List Nat := [2, 1, 1, 2, 1, 2, 6, 2, 2, 2, 2]
def baseStart_8120192 : Nat := 118140960795 + 8120192 * 2 ^ 59
def prefixEnd_8120192 : Nat := 4983230072969 + 3 ^ 40 * 8120192 * 2
def baseEnd_8120192 : Nat := 4169561502793998945155923

theorem tailTrace_8120192 : CollatzResearch.WordTrace tailWord_8120192 prefixEnd_8120192 4169561502793998945155923 := by
  unfold tailWord_8120192
  simp only [CollatzResearch.WordTrace]
  refine ⟨148083866698969338614229415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197445155598625784818972553 148083866698969338614229415)
  ·
    refine ⟨222125800048454007921344123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148083866698969338614229415 222125800048454007921344123)
    ·
      refine ⟨333188700072681011882016185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222125800048454007921344123 333188700072681011882016185)
      ·
        refine ⟨249891525054510758911512139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333188700072681011882016185 249891525054510758911512139)
        ·
          refine ⟨374837287581766138367268209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249891525054510758911512139 374837287581766138367268209)
          ·
            refine ⟨281127965686324603775451157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374837287581766138367268209 281127965686324603775451157)
            ·
              refine ⟨13177873391546465801974273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 281127965686324603775451157 13177873391546465801974273)
              ·
                refine ⟨9883405043659849351480705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13177873391546465801974273 9883405043659849351480705)
                ·
                  refine ⟨7412553782744887013610529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9883405043659849351480705 7412553782744887013610529)
                  ·
                    refine ⟨5559415337058665260207897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7412553782744887013610529 5559415337058665260207897)
                    ·
                      refine ⟨4169561502793998945155923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5559415337058665260207897 4169561502793998945155923)
                      ·
                        rfl

theorem cell23_8120192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 2, 2, 2].length) (baseStart_8120192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120192 prefixEnd_8120192 := by exact prefixLift 8120192
  have htrace : WordTrace (prefixWord ++ tailWord_8120192) baseStart_8120192 baseEnd_8120192 := by
    simpa [prefixWord, tailWord_8120192, baseEnd_8120192] using wordTrace_append hprefix tailTrace_8120192
  have hstable : (prefixWord ++ tailWord_8120192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120192).length < 2 ^ (prefixWord ++ tailWord_8120192).sum := by decide
  have hdescent : baseEnd_8120192 < baseStart_8120192 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120228 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 1, 7]
def baseStart_8120228 : Nat := 118140960795 + 8120228 * 2 ^ 59
def prefixEnd_8120228 : Nat := 4983230072969 + 3 ^ 40 * 8120228 * 2
def baseEnd_8120228 : Nat := 1389859996032520268101919

theorem tailTrace_8120228 : CollatzResearch.WordTrace tailWord_8120228 prefixEnd_8120228 1389859996032520268101919 := by
  unfold tailWord_8120228
  simp only [CollatzResearch.WordTrace]
  refine ⟨148084523212904127688384669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197446030950538836917846225 148084523212904127688384669)
  ·
    refine ⟨55531696204839047883144251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148084523212904127688384669 55531696204839047883144251)
    ·
      refine ⟨83297544307258571824716377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55531696204839047883144251 83297544307258571824716377)
      ·
        refine ⟨62473158230443928868537283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83297544307258571824716377 62473158230443928868537283)
        ·
          refine ⟨93709737345665893302805925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62473158230443928868537283 93709737345665893302805925)
          ·
            refine ⟨17570575752312354994276111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93709737345665893302805925 17570575752312354994276111)
            ·
              refine ⟨26355863628468532491414167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17570575752312354994276111 26355863628468532491414167)
              ·
                refine ⟨39533795442702798737121251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26355863628468532491414167 39533795442702798737121251)
                ·
                  refine ⟨59300693164054198105681877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39533795442702798737121251 59300693164054198105681877)
                  ·
                    refine ⟨1389859996032520268101919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59300693164054198105681877 1389859996032520268101919)
                    ·
                      rfl

theorem cell23_8120228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_8120228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120228 prefixEnd_8120228 := by exact prefixLift 8120228
  have htrace : WordTrace (prefixWord ++ tailWord_8120228) baseStart_8120228 baseEnd_8120228 := by
    simpa [prefixWord, tailWord_8120228, baseEnd_8120228] using wordTrace_append hprefix tailTrace_8120228
  have hstable : (prefixWord ++ tailWord_8120228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120228).length < 2 ^ (prefixWord ++ tailWord_8120228).sum := by decide
  have hdescent : baseEnd_8120228 < baseStart_8120228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120248 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 4, 1, 4]
def baseStart_8120248 : Nat := 118140960795 + 8120248 * 2 ^ 59
def prefixEnd_8120248 : Nat := 4983230072969 + 3 ^ 40 * 8120248 * 2
def baseEnd_8120248 : Nat := 4169590257710650726055665

theorem tailTrace_8120248 : CollatzResearch.WordTrace tailWord_8120248 prefixEnd_8120248 4169590257710650726055665 := by
  unfold tailWord_8120248
  simp only [CollatzResearch.WordTrace]
  refine ⟨148084887942867899396248699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197446517257157199194998265 148084887942867899396248699)
  ·
    refine ⟨222127331914301849094373049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148084887942867899396248699 222127331914301849094373049)
    ·
      refine ⟨166595498935726386820779787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222127331914301849094373049 166595498935726386820779787)
      ·
        refine ⟨249893248403589580231169681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166595498935726386820779787 249893248403589580231169681)
        ·
          refine ⟨187419936302692185173377261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249893248403589580231169681 187419936302692185173377261)
          ·
            refine ⟨70282476113509569440016473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187419936302692185173377261 70282476113509569440016473)
            ·
              refine ⟨52711857085132177080012355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70282476113509569440016473 52711857085132177080012355)
              ·
                refine ⟨79067785627698265620018533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52711857085132177080012355 79067785627698265620018533)
                ·
                  refine ⟨14825209805193424803753475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79067785627698265620018533 14825209805193424803753475)
                  ·
                    refine ⟨22237814707790137205630213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14825209805193424803753475 22237814707790137205630213)
                    ·
                      refine ⟨4169590257710650726055665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22237814707790137205630213 4169590257710650726055665)
                      ·
                        rfl

theorem cell23_8120248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_8120248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120248 prefixEnd_8120248 := by exact prefixLift 8120248
  have htrace : WordTrace (prefixWord ++ tailWord_8120248) baseStart_8120248 baseEnd_8120248 := by
    simpa [prefixWord, tailWord_8120248, baseEnd_8120248] using wordTrace_append hprefix tailTrace_8120248
  have hstable : (prefixWord ++ tailWord_8120248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120248).length < 2 ^ (prefixWord ++ tailWord_8120248).sum := by decide
  have hdescent : baseEnd_8120248 < baseStart_8120248 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120251 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 5]
def baseStart_8120251 : Nat := 118140960795 + 8120251 * 2 ^ 59
def prefixEnd_8120251 : Nat := 4983230072969 + 3 ^ 40 * 8120251 * 2
def baseEnd_8120251 : Nat := 4169591798152614214318151

theorem tailTrace_8120251 : CollatzResearch.WordTrace tailWord_8120251 prefixEnd_8120251 4169591798152614214318151 := by
  unfold tailWord_8120251
  simp only [CollatzResearch.WordTrace]
  refine ⟨296169885304724930304856607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197446590203149953536571071 296169885304724930304856607)
  ·
    refine ⟨444254827957087395457284911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296169885304724930304856607 444254827957087395457284911)
    ·
      refine ⟨666382241935631093185927367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444254827957087395457284911 666382241935631093185927367)
      ·
        refine ⟨999573362903446639778891051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666382241935631093185927367 999573362903446639778891051)
        ·
          refine ⟨1499360044355169959668336577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999573362903446639778891051 1499360044355169959668336577)
          ·
            refine ⟨1124520033266377469751252433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1499360044355169959668336577 1124520033266377469751252433)
            ·
              refine ⟨843390024949783102313439325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1124520033266377469751252433 843390024949783102313439325)
              ·
                refine ⟨316271259356168663367539747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 843390024949783102313439325 316271259356168663367539747)
                ·
                  refine ⟨474406889034252995051309621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316271259356168663367539747 474406889034252995051309621)
                  ·
                    refine ⟨44475645846961218286060277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 474406889034252995051309621 44475645846961218286060277)
                    ·
                      refine ⟨4169591798152614214318151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44475645846961218286060277 4169591798152614214318151)
                      ·
                        rfl

theorem cell23_8120251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 5].length) (baseStart_8120251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120251 prefixEnd_8120251 := by exact prefixLift 8120251
  have htrace : WordTrace (prefixWord ++ tailWord_8120251) baseStart_8120251 baseEnd_8120251 := by
    simpa [prefixWord, tailWord_8120251, baseEnd_8120251] using wordTrace_append hprefix tailTrace_8120251
  have hstable : (prefixWord ++ tailWord_8120251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120251).length < 2 ^ (prefixWord ++ tailWord_8120251).sum := by decide
  have hdescent : baseEnd_8120251 < baseStart_8120251 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120302 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_8120302 : Nat := 118140960795 + 8120302 * 2 ^ 59
def prefixEnd_8120302 : Nat := 4983230072969 + 3 ^ 40 * 8120302 * 2
def baseEnd_8120302 : Nat := 4169617985665993514780417

theorem tailTrace_8120302 : CollatzResearch.WordTrace tailWord_8120302 prefixEnd_8120302 4169617985665993514780417 := by
  unfold tailWord_8120302
  simp only [CollatzResearch.WordTrace]
  refine ⟨37021468178442520751870395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197447830285026777343308773 37021468178442520751870395)
  ·
    refine ⟨55532202267663781127805593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37021468178442520751870395 55532202267663781127805593)
    ·
      refine ⟨41649151700747835845854195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55532202267663781127805593 41649151700747835845854195)
      ·
        refine ⟨62473727551121753768781293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41649151700747835845854195 62473727551121753768781293)
        ·
          refine ⟨23427647831670657663292985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62473727551121753768781293 23427647831670657663292985)
          ·
            refine ⟨17570735873752993247469739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23427647831670657663292985 17570735873752993247469739)
            ·
              refine ⟨26356103810629489871204609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17570735873752993247469739 26356103810629489871204609)
              ·
                refine ⟨19767077857972117403403457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26356103810629489871204609 19767077857972117403403457)
                ·
                  refine ⟨14825308393479088052552593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19767077857972117403403457 14825308393479088052552593)
                  ·
                    refine ⟨11118981295109316039414445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14825308393479088052552593 11118981295109316039414445)
                    ·
                      refine ⟨4169617985665993514780417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11118981295109316039414445 4169617985665993514780417)
                      ·
                        rfl

theorem cell23_8120302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_8120302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120302 prefixEnd_8120302 := by exact prefixLift 8120302
  have htrace : WordTrace (prefixWord ++ tailWord_8120302) baseStart_8120302 baseEnd_8120302 := by
    simpa [prefixWord, tailWord_8120302, baseEnd_8120302] using wordTrace_append hprefix tailTrace_8120302
  have hstable : (prefixWord ++ tailWord_8120302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120302).length < 2 ^ (prefixWord ++ tailWord_8120302).sum := by decide
  have hdescent : baseEnd_8120302 < baseStart_8120302 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120360 : List Nat := [2, 1, 5, 3, 2, 1, 2, 2, 1, 4]
def baseStart_8120360 : Nat := 118140960795 + 8120360 * 2 ^ 59
def prefixEnd_8120360 : Nat := 4983230072969 + 3 ^ 40 * 8120360 * 2
def baseEnd_8120360 : Nat := 1389882589181318095951717

theorem tailTrace_8120360 : CollatzResearch.WordTrace tailWord_8120360 prefixEnd_8120360 1389882589181318095951717 := by
  unfold tailWord_8120360
  simp only [CollatzResearch.WordTrace]
  refine ⟨148086930430665020960287267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197449240574220027947049689 148086930430665020960287267)
  ·
    refine ⟨222130395645997531440430901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148086930430665020960287267 222130395645997531440430901)
    ·
      refine ⟨20824724591812268572540397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222130395645997531440430901 20824724591812268572540397)
      ·
        refine ⟨7809271721929600714702649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20824724591812268572540397 7809271721929600714702649)
        ·
          refine ⟨5856953791447200536026987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7809271721929600714702649 5856953791447200536026987)
          ·
            refine ⟨8785430687170800804040481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5856953791447200536026987 8785430687170800804040481)
            ·
              refine ⟨6589073015378100603030361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8785430687170800804040481 6589073015378100603030361)
              ·
                refine ⟨4941804761533575452272771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6589073015378100603030361 4941804761533575452272771)
                ·
                  refine ⟨7412707142300363178409157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4941804761533575452272771 7412707142300363178409157)
                  ·
                    refine ⟨1389882589181318095951717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7412707142300363178409157 1389882589181318095951717)
                    ·
                      rfl

theorem cell23_8120360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_8120360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120360 prefixEnd_8120360 := by exact prefixLift 8120360
  have htrace : WordTrace (prefixWord ++ tailWord_8120360) baseStart_8120360 baseEnd_8120360 := by
    simpa [prefixWord, tailWord_8120360, baseEnd_8120360] using wordTrace_append hprefix tailTrace_8120360
  have hstable : (prefixWord ++ tailWord_8120360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120360).length < 2 ^ (prefixWord ++ tailWord_8120360).sum := by decide
  have hdescent : baseEnd_8120360 < baseStart_8120360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120366 : List Nat := [4, 1, 3, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_8120366 : Nat := 118140960795 + 8120366 * 2 ^ 59
def prefixEnd_8120366 : Nat := 4983230072969 + 3 ^ 40 * 8120366 * 2
def baseEnd_8120366 : Nat := 4169650848427881264380123

theorem tailTrace_8120366 : CollatzResearch.WordTrace tailWord_8120366 prefixEnd_8120366 4169650848427881264380123 := by
  unfold tailWord_8120366
  simp only [CollatzResearch.WordTrace]
  refine ⟨37021759962413538118161619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197449386466205536630195301 37021759962413538118161619)
  ·
    refine ⟨55532639943620307177242429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37021759962413538118161619 55532639943620307177242429)
    ·
      refine ⟨20824739978857615191465911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55532639943620307177242429 20824739978857615191465911)
      ·
        refine ⟨31237109968286422787198867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20824739978857615191465911 31237109968286422787198867)
        ·
          refine ⟨46855664952429634180798301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31237109968286422787198867 46855664952429634180798301)
          ·
            refine ⟨17570874357161112817799363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46855664952429634180798301 17570874357161112817799363)
            ·
              refine ⟨26356311535741669226699045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17570874357161112817799363 26356311535741669226699045)
              ·
                refine ⟨4941808412951562980006071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26356311535741669226699045 4941808412951562980006071)
                ·
                  refine ⟨7412712619427344470009107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4941808412951562980006071 7412712619427344470009107)
                  ·
                    refine ⟨11119068929141016705013661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7412712619427344470009107 11119068929141016705013661)
                    ·
                      refine ⟨4169650848427881264380123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11119068929141016705013661 4169650848427881264380123)
                      ·
                        rfl

theorem cell23_8120366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_8120366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120366 prefixEnd_8120366 := by exact prefixLift 8120366
  have htrace : WordTrace (prefixWord ++ tailWord_8120366) baseStart_8120366 baseEnd_8120366 := by
    simpa [prefixWord, tailWord_8120366, baseEnd_8120366] using wordTrace_append hprefix tailTrace_8120366
  have hstable : (prefixWord ++ tailWord_8120366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120366).length < 2 ^ (prefixWord ++ tailWord_8120366).sum := by decide
  have hdescent : baseEnd_8120366 < baseStart_8120366 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120375 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 3]
def baseStart_8120375 : Nat := 118140960795 + 8120375 * 2 ^ 59
def prefixEnd_8120375 : Nat := 4983230072969 + 3 ^ 40 * 8120375 * 2
def baseEnd_8120375 : Nat := 4169655469753771729167581

theorem tailTrace_8120375 : CollatzResearch.WordTrace tailWord_8120375 prefixEnd_8120375 4169655469753771729167581 := by
  unfold tailWord_8120375
  simp only [CollatzResearch.WordTrace]
  refine ⟨296174407956275699482370579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197449605304183799654913719 296174407956275699482370579)
  ·
    refine ⟨444261611934413549223555869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296174407956275699482370579 444261611934413549223555869)
    ·
      refine ⟨166598104475405080958833451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444261611934413549223555869 166598104475405080958833451)
      ·
        refine ⟨249897156713107621438250177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166598104475405080958833451 249897156713107621438250177)
        ·
          refine ⟨187422867534830716078687633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249897156713107621438250177 187422867534830716078687633)
          ·
            refine ⟨140567150651123037059015725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187422867534830716078687633 140567150651123037059015725)
            ·
              refine ⟨52712681494171138897130897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140567150651123037059015725 52712681494171138897130897)
              ·
                refine ⟨39534511120628354172848173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52712681494171138897130897 39534511120628354172848173)
                ·
                  refine ⟨14825441670235632814818065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39534511120628354172848173 14825441670235632814818065)
                  ·
                    refine ⟨11119081252676724611113549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14825441670235632814818065 11119081252676724611113549)
                    ·
                      refine ⟨4169655469753771729167581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11119081252676724611113549 4169655469753771729167581)
                      ·
                        rfl

theorem cell23_8120375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_8120375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120375 prefixEnd_8120375 := by exact prefixLift 8120375
  have htrace : WordTrace (prefixWord ++ tailWord_8120375) baseStart_8120375 baseEnd_8120375 := by
    simpa [prefixWord, tailWord_8120375, baseEnd_8120375] using wordTrace_append hprefix tailTrace_8120375
  have hstable : (prefixWord ++ tailWord_8120375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120375).length < 2 ^ (prefixWord ++ tailWord_8120375).sum := by decide
  have hdescent : baseEnd_8120375 < baseStart_8120375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120406 : List Nat := [5, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_8120406 : Nat := 118140960795 + 8120406 * 2 ^ 59
def prefixEnd_8120406 : Nat := 4983230072969 + 3 ^ 40 * 8120406 * 2
def baseEnd_8120406 : Nat := 4169671387654061107879939

theorem tailTrace_8120406 : CollatzResearch.WordTrace tailWord_8120406 prefixEnd_8120406 4169671387654061107879939 := by
  unfold tailWord_8120406
  simp only [CollatzResearch.WordTrace]
  refine ⟨18510971163697711986046817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197450359079442261184499381 18510971163697711986046817)
  ·
    refine ⟨13883228372773283989535113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18510971163697711986046817 13883228372773283989535113)
    ·
      refine ⟨10412421279579962992151335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13883228372773283989535113 10412421279579962992151335)
      ·
        refine ⟨15618631919369944488227003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10412421279579962992151335 15618631919369944488227003)
        ·
          refine ⟨23427947879054916732340505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15618631919369944488227003 23427947879054916732340505)
          ·
            refine ⟨17570960909291187549255379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23427947879054916732340505 17570960909291187549255379)
            ·
              refine ⟨26356441363936781323883069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17570960909291187549255379 26356441363936781323883069)
              ·
                refine ⟨9883665511476292996456151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26356441363936781323883069 9883665511476292996456151)
                ·
                  refine ⟨14825498267214439494684227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9883665511476292996456151 14825498267214439494684227)
                  ·
                    refine ⟨22238247400821659242026341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14825498267214439494684227 22238247400821659242026341)
                    ·
                      refine ⟨4169671387654061107879939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22238247400821659242026341 4169671387654061107879939)
                      ·
                        rfl

theorem cell23_8120406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_8120406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120406 prefixEnd_8120406 := by exact prefixLift 8120406
  have htrace : WordTrace (prefixWord ++ tailWord_8120406) baseStart_8120406 baseEnd_8120406 := by
    simpa [prefixWord, tailWord_8120406, baseEnd_8120406] using wordTrace_append hprefix tailTrace_8120406
  have hstable : (prefixWord ++ tailWord_8120406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120406).length < 2 ^ (prefixWord ++ tailWord_8120406).sum := by decide
  have hdescent : baseEnd_8120406 < baseStart_8120406 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120490 : List Nat := [3, 1, 5, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_8120490 : Nat := 118140960795 + 8120490 * 2 ^ 59
def prefixEnd_8120490 : Nat := 4983230072969 + 3 ^ 40 * 8120490 * 2
def baseEnd_8120490 : Nat := 4169714520029038779229553

theorem tailTrace_8120490 : CollatzResearch.WordTrace tailWord_8120490 prefixEnd_8120490 4169714520029038779229553 := by
  unfold tailWord_8120490
  simp only [CollatzResearch.WordTrace]
  refine ⟨74044650587714768530701731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197452401567239382748537949 74044650587714768530701731)
  ·
    refine ⟨111066975881572152796052597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74044650587714768530701731 111066975881572152796052597)
    ·
      refine ⟨10412528988897389324629931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111066975881572152796052597 10412528988897389324629931)
      ·
        refine ⟨15618793483346083986944897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10412528988897389324629931 15618793483346083986944897)
        ·
          refine ⟨11714095112509562990208673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15618793483346083986944897 11714095112509562990208673)
          ·
            refine ⟨8785571334382172242656505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11714095112509562990208673 8785571334382172242656505)
            ·
              refine ⟨6589178500786629181992379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8785571334382172242656505 6589178500786629181992379)
              ·
                refine ⟨9883767751179943772988569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6589178500786629181992379 9883767751179943772988569)
                ·
                  refine ⟨7412825813384957829741427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9883767751179943772988569 7412825813384957829741427)
                  ·
                    refine ⟨11119238720077436744612141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7412825813384957829741427 11119238720077436744612141)
                    ·
                      refine ⟨4169714520029038779229553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11119238720077436744612141 4169714520029038779229553)
                      ·
                        rfl

theorem cell23_8120490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_8120490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120490 prefixEnd_8120490 := by exact prefixLift 8120490
  have htrace : WordTrace (prefixWord ++ tailWord_8120490) baseStart_8120490 baseEnd_8120490 := by
    simpa [prefixWord, tailWord_8120490, baseEnd_8120490] using wordTrace_append hprefix tailTrace_8120490
  have hstable : (prefixWord ++ tailWord_8120490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120490).length < 2 ^ (prefixWord ++ tailWord_8120490).sum := by decide
  have hdescent : baseEnd_8120490 < baseStart_8120490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120495 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 3]
def baseStart_8120495 : Nat := 118140960795 + 8120495 * 2 ^ 59
def prefixEnd_8120495 : Nat := 4983230072969 + 3 ^ 40 * 8120495 * 2
def baseEnd_8120495 : Nat := 4169717087432311259667029

theorem tailTrace_8120495 : CollatzResearch.WordTrace tailWord_8120495 prefixEnd_8120495 4169717087432311259667029 := by
  unfold tailWord_8120495
  simp only [CollatzResearch.WordTrace]
  refine ⟨296178784715840959976738939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197452523143893973317825959 296178784715840959976738939)
  ·
    refine ⟨444268177073761439965108409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296178784715840959976738939 444268177073761439965108409)
    ·
      refine ⟨333201132805321079973831307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444268177073761439965108409 333201132805321079973831307)
      ·
        refine ⟨499801699207981619960746961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333201132805321079973831307 499801699207981619960746961)
        ·
          refine ⟨374851274405986214970560221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499801699207981619960746961 374851274405986214970560221)
          ·
            refine ⟨140569227902244830613960083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374851274405986214970560221 140569227902244830613960083)
            ·
              refine ⟨210853841853367245920940125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140569227902244830613960083 210853841853367245920940125)
              ·
                refine ⟨79070190695012717220352547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210853841853367245920940125 79070190695012717220352547)
                ·
                  refine ⟨118605286042519075830528821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79070190695012717220352547 118605286042519075830528821)
                  ·
                    refine ⟨11119245566486163359112077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118605286042519075830528821 11119245566486163359112077)
                    ·
                      refine ⟨4169717087432311259667029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11119245566486163359112077 4169717087432311259667029)
                      ·
                        rfl

theorem cell23_8120495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 3].length) (baseStart_8120495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120495 prefixEnd_8120495 := by exact prefixLift 8120495
  have htrace : WordTrace (prefixWord ++ tailWord_8120495) baseStart_8120495 baseEnd_8120495 := by
    simpa [prefixWord, tailWord_8120495, baseEnd_8120495] using wordTrace_append hprefix tailTrace_8120495
  have hstable : (prefixWord ++ tailWord_8120495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120495).length < 2 ^ (prefixWord ++ tailWord_8120495).sum := by decide
  have hdescent : baseEnd_8120495 < baseStart_8120495 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120500 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_8120500 : Nat := 118140960795 + 8120500 * 2 ^ 59
def prefixEnd_8120500 : Nat := 4983230072969 + 3 ^ 40 * 8120500 * 2
def baseEnd_8120500 : Nat := 4169719654835583740104507

theorem tailTrace_8120500 : CollatzResearch.WordTrace tailWord_8120500 prefixEnd_8120500 4169719654835583740104507 := by
  unfold tailWord_8120500
  simp only [CollatzResearch.WordTrace]
  refine ⟨148089483540411422915335477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197452644720548563887113969 148089483540411422915335477)
  ·
    refine ⟨13883389081913570898312701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148089483540411422915335477 13883389081913570898312701)
    ·
      refine ⟨5206270905717589086867263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13883389081913570898312701 5206270905717589086867263)
      ·
        refine ⟨7809406358576383630300895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5206270905717589086867263 7809406358576383630300895)
        ·
          refine ⟨11714109537864575445451343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7809406358576383630300895 11714109537864575445451343)
          ·
            refine ⟨17571164306796863168177015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11714109537864575445451343 17571164306796863168177015)
            ·
              refine ⟨26356746460195294752265523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17571164306796863168177015 26356746460195294752265523)
              ·
                refine ⟨39535119690292942128398285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26356746460195294752265523 39535119690292942128398285)
                ·
                  refine ⟨14825669883859853298149357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39535119690292942128398285 14825669883859853298149357)
                  ·
                    refine ⟨5559626206447444986806009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14825669883859853298149357 5559626206447444986806009)
                    ·
                      refine ⟨4169719654835583740104507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5559626206447444986806009 4169719654835583740104507)
                      ·
                        rfl

theorem cell23_8120500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_8120500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120500 prefixEnd_8120500 := by exact prefixLift 8120500
  have htrace : WordTrace (prefixWord ++ tailWord_8120500) baseStart_8120500 baseEnd_8120500 := by
    simpa [prefixWord, tailWord_8120500, baseEnd_8120500] using wordTrace_append hprefix tailTrace_8120500
  have hstable : (prefixWord ++ tailWord_8120500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120500).length < 2 ^ (prefixWord ++ tailWord_8120500).sum := by decide
  have hdescent : baseEnd_8120500 < baseStart_8120500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120535 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 4]
def baseStart_8120535 : Nat := 118140960795 + 8120535 * 2 ^ 59
def prefixEnd_8120535 : Nat := 4983230072969 + 3 ^ 40 * 8120535 * 2
def baseEnd_8120535 : Nat := 4169737626658491103166845

theorem tailTrace_8120535 : CollatzResearch.WordTrace tailWord_8120535 prefixEnd_8120535 4169737626658491103166845 := by
  unfold tailWord_8120535
  simp only [CollatzResearch.WordTrace]
  refine ⟨296180243635696046808195059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197453495757130697872130039 296180243635696046808195059)
  ·
    refine ⟨444270365453544070212292589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296180243635696046808195059 444270365453544070212292589)
    ·
      refine ⟨166601387045079026329609721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444270365453544070212292589 166601387045079026329609721)
      ·
        refine ⟨124951040283809269747207291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166601387045079026329609721 124951040283809269747207291)
        ·
          refine ⟨187426560425713904620810937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124951040283809269747207291 187426560425713904620810937)
          ·
            refine ⟨140569920319285428465608203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187426560425713904620810937 140569920319285428465608203)
            ·
              refine ⟨210854880478928142698412305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140569920319285428465608203 210854880478928142698412305)
              ·
                refine ⟨158141160359196107023809229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210854880478928142698412305 158141160359196107023809229)
                ·
                  refine ⟨59302935134698540133928461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158141160359196107023809229 59302935134698540133928461)
                  ·
                    refine ⟨22238600675511952550223173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59302935134698540133928461 22238600675511952550223173)
                    ·
                      refine ⟨4169737626658491103166845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22238600675511952550223173 4169737626658491103166845)
                      ·
                        rfl

theorem cell23_8120535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_8120535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120535 prefixEnd_8120535 := by exact prefixLift 8120535
  have htrace : WordTrace (prefixWord ++ tailWord_8120535) baseStart_8120535 baseEnd_8120535 := by
    simpa [prefixWord, tailWord_8120535, baseEnd_8120535] using wordTrace_append hprefix tailTrace_8120535
  have hstable : (prefixWord ++ tailWord_8120535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120535).length < 2 ^ (prefixWord ++ tailWord_8120535).sum := by decide
  have hdescent : baseEnd_8120535 < baseStart_8120535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120536 : List Nat := [2, 1, 2, 2, 4, 3, 2, 2, 5]
def baseStart_8120536 : Nat := 118140960795 + 8120536 * 2 ^ 59
def prefixEnd_8120536 : Nat := 4983230072969 + 3 ^ 40 * 8120536 * 2
def baseEnd_8120536 : Nat := 463304237793238399917149

theorem tailTrace_8120536 : CollatzResearch.WordTrace tailWord_8120536 prefixEnd_8120536 463304237793238399917149 := by
  unfold tailWord_8120536
  simp only [CollatzResearch.WordTrace]
  refine ⟨148090140054346211989490731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197453520072461615985987641 148090140054346211989490731)
  ·
    refine ⟨222135210081519317984236097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148090140054346211989490731 222135210081519317984236097)
    ·
      refine ⟨166601407561139488488177073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222135210081519317984236097 166601407561139488488177073)
      ·
        refine ⟨124951055670854616366132805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166601407561139488488177073 124951055670854616366132805)
        ·
          refine ⟨23428322938285240568649901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124951055670854616366132805 23428322938285240568649901)
          ·
            refine ⟨8785621101856965213243713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23428322938285240568649901 8785621101856965213243713)
            ·
              refine ⟨6589215826392723909932785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8785621101856965213243713 6589215826392723909932785)
              ·
                refine ⟨4941911869794542932449589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6589215826392723909932785 4941911869794542932449589)
                ·
                  refine ⟨463304237793238399917149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4941911869794542932449589 463304237793238399917149)
                  ·
                    rfl

theorem cell23_8120536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 5].length) (baseStart_8120536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120536 prefixEnd_8120536 := by exact prefixLift 8120536
  have htrace : WordTrace (prefixWord ++ tailWord_8120536) baseStart_8120536 baseEnd_8120536 := by
    simpa [prefixWord, tailWord_8120536, baseEnd_8120536] using wordTrace_append hprefix tailTrace_8120536
  have hstable : (prefixWord ++ tailWord_8120536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120536).length < 2 ^ (prefixWord ++ tailWord_8120536).sum := by decide
  have hdescent : baseEnd_8120536 < baseStart_8120536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120575 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 8]
def baseStart_8120575 : Nat := 118140960795 + 8120575 * 2 ^ 59
def prefixEnd_8120575 : Nat := 4983230072969 + 3 ^ 40 * 8120575 * 2
def baseEnd_8120575 : Nat := 463306462876074549629629

theorem tailTrace_8120575 : CollatzResearch.WordTrace tailWord_8120575 prefixEnd_8120575 463306462876074549629629 := by
  unfold tailWord_8120575
  simp only [CollatzResearch.WordTrace]
  refine ⟨296181702555551133639651179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197454468370367422426434119 296181702555551133639651179)
  ·
    refine ⟨444272553833326700459476769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296181702555551133639651179 444272553833326700459476769)
    ·
      refine ⟨333204415374995025344607577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444272553833326700459476769 333204415374995025344607577)
      ·
        refine ⟨249903311531246269008455683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333204415374995025344607577 249903311531246269008455683)
        ·
          refine ⟨374854967296869403512683525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249903311531246269008455683 374854967296869403512683525)
          ·
            refine ⟨70285306368163013158628161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 374854967296869403512683525 70285306368163013158628161)
            ·
              refine ⟨52713979776122259868971121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70285306368163013158628161 52713979776122259868971121)
              ·
                refine ⟨39535484832091694901728341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52713979776122259868971121 39535484832091694901728341)
                ·
                  refine ⟨463306462876074549629629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39535484832091694901728341 463306462876074549629629)
                  ·
                    rfl

theorem cell23_8120575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 8].length) (baseStart_8120575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120575 prefixEnd_8120575 := by exact prefixLift 8120575
  have htrace : WordTrace (prefixWord ++ tailWord_8120575) baseStart_8120575 baseEnd_8120575 := by
    simpa [prefixWord, tailWord_8120575, baseEnd_8120575] using wordTrace_append hprefix tailTrace_8120575
  have hstable : (prefixWord ++ tailWord_8120575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120575).length < 2 ^ (prefixWord ++ tailWord_8120575).sum := by decide
  have hdescent : baseEnd_8120575 < baseStart_8120575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120606 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_8120606 : Nat := 118140960795 + 8120606 * 2 ^ 59
def prefixEnd_8120606 : Nat := 4983230072969 + 3 ^ 40 * 8120606 * 2
def baseEnd_8120606 : Nat := 4169774083784960325379019

theorem tailTrace_8120606 : CollatzResearch.WordTrace tailWord_8120606 prefixEnd_8120606 4169774083784960325379019 := by
  unfold tailWord_8120606
  simp only [CollatzResearch.WordTrace]
  refine ⟨37022854152304853241753709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197455222145625883956019781 37022854152304853241753709)
  ·
    refine ⟨13883570307114319965657641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37022854152304853241753709 13883570307114319965657641)
    ·
      refine ⟨10412677730335739974243231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13883570307114319965657641 10412677730335739974243231)
      ·
        refine ⟨15619016595503609961364847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10412677730335739974243231 15619016595503609961364847)
        ·
          refine ⟨23428524893255414942047271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15619016595503609961364847 23428524893255414942047271)
          ·
            refine ⟨35142787339883122413070907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23428524893255414942047271 35142787339883122413070907)
            ·
              refine ⟨52714181009824683619606361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35142787339883122413070907 52714181009824683619606361)
              ·
                refine ⟨39535635757368512714704771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52714181009824683619606361 39535635757368512714704771)
                ·
                  refine ⟨59303453636052769072057157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39535635757368512714704771 59303453636052769072057157)
                  ·
                    refine ⟨11119397556759894201010717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59303453636052769072057157 11119397556759894201010717)
                    ·
                      refine ⟨4169774083784960325379019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11119397556759894201010717 4169774083784960325379019)
                      ·
                        rfl

theorem cell23_8120606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_8120606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120606 prefixEnd_8120606 := by exact prefixLift 8120606
  have htrace : WordTrace (prefixWord ++ tailWord_8120606) baseStart_8120606 baseEnd_8120606 := by
    simpa [prefixWord, tailWord_8120606, baseEnd_8120606] using wordTrace_append hprefix tailTrace_8120606
  have hstable : (prefixWord ++ tailWord_8120606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120606).length < 2 ^ (prefixWord ++ tailWord_8120606).sum := by decide
  have hdescent : baseEnd_8120606 < baseStart_8120606 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120629 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 1, 5, 2]
def baseStart_8120629 : Nat := 118140960795 + 8120629 * 2 ^ 59
def prefixEnd_8120629 : Nat := 4983230072969 + 3 ^ 40 * 8120629 * 2
def baseEnd_8120629 : Nat := 4169785893840013735391413

theorem tailTrace_8120629 : CollatzResearch.WordTrace tailWord_8120629 prefixEnd_8120629 4169785893840013735391413 := by
  unfold tailWord_8120629
  simp only [CollatzResearch.WordTrace]
  refine ⟨296183672097355500862116941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197455781398237000574744627 296183672097355500862116941)
  ·
    refine ⟨111068877036508312823293853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296183672097355500862116941 111068877036508312823293853)
    ·
      refine ⟨41650828888690617308735195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111068877036508312823293853 41650828888690617308735195)
      ·
        refine ⟨62476243333035925963102793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41650828888690617308735195 62476243333035925963102793)
        ·
          refine ⟨46857182499776944472327095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62476243333035925963102793 46857182499776944472327095)
          ·
            refine ⟨70285773749665416708490643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46857182499776944472327095 70285773749665416708490643)
            ·
              refine ⟨105428660624498125062735965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70285773749665416708490643 105428660624498125062735965)
              ·
                refine ⟨39535747734186796898525987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105428660624498125062735965 39535747734186796898525987)
                ·
                  refine ⟨59303621601280195347788981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39535747734186796898525987 59303621601280195347788981)
                  ·
                    refine ⟨5559714525120018313855217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59303621601280195347788981 5559714525120018313855217)
                    ·
                      refine ⟨4169785893840013735391413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5559714525120018313855217 4169785893840013735391413)
                      ·
                        rfl

theorem cell23_8120629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_8120629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120629 prefixEnd_8120629 := by exact prefixLift 8120629
  have htrace : WordTrace (prefixWord ++ tailWord_8120629) baseStart_8120629 baseEnd_8120629 := by
    simpa [prefixWord, tailWord_8120629, baseEnd_8120629] using wordTrace_append hprefix tailTrace_8120629
  have hstable : (prefixWord ++ tailWord_8120629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120629).length < 2 ^ (prefixWord ++ tailWord_8120629).sum := by decide
  have hdescent : baseEnd_8120629 < baseStart_8120629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120676 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 5, 2, 2]
def baseStart_8120676 : Nat := 118140960795 + 8120676 * 2 ^ 59
def prefixEnd_8120676 : Nat := 4983230072969 + 3 ^ 40 * 8120676 * 2
def baseEnd_8120676 : Nat := 4169810027430775051503697

theorem tailTrace_8120676 : CollatzResearch.WordTrace tailWord_8120676 prefixEnd_8120676 4169810027430775051503697 := by
  unfold tailWord_8120676
  simp only [CollatzResearch.WordTrace]
  refine ⟨148092693164092613944538941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197456924218790151926051921 148092693164092613944538941)
  ·
    refine ⟨55534759936534730229202103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148092693164092613944538941 55534759936534730229202103)
    ·
      refine ⟨83302139904802095343803155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55534759936534730229202103 83302139904802095343803155)
      ·
        refine ⟨124953209857203143015704733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83302139904802095343803155 124953209857203143015704733)
        ·
          refine ⟨46857453696451178630889275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124953209857203143015704733 46857453696451178630889275)
          ·
            refine ⟨70286180544676767946333913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46857453696451178630889275 70286180544676767946333913)
            ·
              refine ⟨52714635408507575959750435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70286180544676767946333913 52714635408507575959750435)
              ·
                refine ⟨79071953112761363939625653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52714635408507575959750435 79071953112761363939625653)
                ·
                  refine ⟨7412995604321377869339905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79071953112761363939625653 7412995604321377869339905)
                  ·
                    refine ⟨5559746703241033402004929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7412995604321377869339905 5559746703241033402004929)
                    ·
                      refine ⟨4169810027430775051503697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5559746703241033402004929 4169810027430775051503697)
                      ·
                        rfl

theorem cell23_8120676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_8120676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120676 prefixEnd_8120676 := by exact prefixLift 8120676
  have htrace : WordTrace (prefixWord ++ tailWord_8120676) baseStart_8120676 baseEnd_8120676 := by
    simpa [prefixWord, tailWord_8120676, baseEnd_8120676] using wordTrace_append hprefix tailTrace_8120676
  have hstable : (prefixWord ++ tailWord_8120676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120676).length < 2 ^ (prefixWord ++ tailWord_8120676).sum := by decide
  have hdescent : baseEnd_8120676 < baseStart_8120676 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120693 : List Nat := [1, 3, 4, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_8120693 : Nat := 118140960795 + 8120693 * 2 ^ 59
def prefixEnd_8120693 : Nat := 4983230072969 + 3 ^ 40 * 8120693 * 2
def baseEnd_8120693 : Nat := 4169818756601901484991119

theorem tailTrace_8120693 : CollatzResearch.WordTrace tailWord_8120693 prefixEnd_8120693 4169818756601901484991119 := by
  unfold tailWord_8120693
  simp only [CollatzResearch.WordTrace]
  refine ⟨296186006369123639792446733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197457337579415759861631155 296186006369123639792446733)
  ·
    refine ⟨111069752388421364922167525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296186006369123639792446733 111069752388421364922167525)
    ·
      refine ⟨20825578572829005922906411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111069752388421364922167525 20825578572829005922906411)
      ·
        refine ⟨31238367859243508884359617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20825578572829005922906411 31238367859243508884359617)
        ·
          refine ⟨23428775894432631663269713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31238367859243508884359617 23428775894432631663269713)
          ·
            refine ⟨17571581920824473747452285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23428775894432631663269713 17571581920824473747452285)
            ·
              refine ⟨6589343220309177655294607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17571581920824473747452285 6589343220309177655294607)
              ·
                refine ⟨9884014830463766482941911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6589343220309177655294607 9884014830463766482941911)
                ·
                  refine ⟨14826022245695649724412867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9884014830463766482941911 14826022245695649724412867)
                  ·
                    refine ⟨22239033368543474586619301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14826022245695649724412867 22239033368543474586619301)
                    ·
                      refine ⟨4169818756601901484991119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22239033368543474586619301 4169818756601901484991119)
                      ·
                        rfl

theorem cell23_8120693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_8120693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120693 prefixEnd_8120693 := by exact prefixLift 8120693
  have htrace : WordTrace (prefixWord ++ tailWord_8120693) baseStart_8120693 baseEnd_8120693 := by
    simpa [prefixWord, tailWord_8120693, baseEnd_8120693] using wordTrace_append hprefix tailTrace_8120693
  have hstable : (prefixWord ++ tailWord_8120693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120693).length < 2 ^ (prefixWord ++ tailWord_8120693).sum := by decide
  have hdescent : baseEnd_8120693 < baseStart_8120693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120712 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 1, 9]
def baseStart_8120712 : Nat := 118140960795 + 8120712 * 2 ^ 59
def prefixEnd_8120712 : Nat := 4983230072969 + 3 ^ 40 * 8120712 * 2
def baseEnd_8120712 : Nat := 1389942837578112303551177

theorem tailTrace_8120712 : CollatzResearch.WordTrace tailWord_8120712 prefixEnd_8120712 1389942837578112303551177 := by
  unfold tailWord_8120712
  simp only [CollatzResearch.WordTrace]
  refine ⟨148093349678027403018694195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197457799570703204024925593 148093349678027403018694195)
  ·
    refine ⟨222140024517041104528041293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148093349678027403018694195 222140024517041104528041293)
    ·
      refine ⟨83302509193890414198015485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222140024517041104528041293 83302509193890414198015485)
      ·
        refine ⟨31238440947708905324255807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83302509193890414198015485 31238440947708905324255807)
        ·
          refine ⟨46857661421563357986383711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31238440947708905324255807 46857661421563357986383711)
          ·
            refine ⟨70286492132345036979575567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46857661421563357986383711 70286492132345036979575567)
            ·
              refine ⟨105429738198517555469363351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70286492132345036979575567 105429738198517555469363351)
              ·
                refine ⟨158144607297776333204045027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105429738198517555469363351 158144607297776333204045027)
                ·
                  refine ⟨237216910946664499806067541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158144607297776333204045027 237216910946664499806067541)
                  ·
                    refine ⟨1389942837578112303551177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 237216910946664499806067541 1389942837578112303551177)
                    ·
                      rfl

theorem cell23_8120712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_8120712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120712 prefixEnd_8120712 := by exact prefixLift 8120712
  have htrace : WordTrace (prefixWord ++ tailWord_8120712) baseStart_8120712 baseEnd_8120712 := by
    simpa [prefixWord, tailWord_8120712, baseEnd_8120712] using wordTrace_append hprefix tailTrace_8120712
  have hstable : (prefixWord ++ tailWord_8120712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120712).length < 2 ^ (prefixWord ++ tailWord_8120712).sum := by decide
  have hdescent : baseEnd_8120712 < baseStart_8120712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120736 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 3, 3, 2]
def baseStart_8120736 : Nat := 118140960795 + 8120736 * 2 ^ 59
def prefixEnd_8120736 : Nat := 4983230072969 + 3 ^ 40 * 8120736 * 2
def baseEnd_8120736 : Nat := 4169840836270044816753421

theorem tailTrace_8120736 : CollatzResearch.WordTrace tailWord_8120736 prefixEnd_8120736 4169840836270044816753421 := by
  unfold tailWord_8120736
  simp only [CollatzResearch.WordTrace]
  refine ⟨148093787353983929068131031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197458383138645238757508041 148093787353983929068131031)
  ·
    refine ⟨222140681030975893602196547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148093787353983929068131031 222140681030975893602196547)
    ·
      refine ⟨333211021546463840403294821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222140681030975893602196547 333211021546463840403294821)
      ·
        refine ⟨62477066539961970075617779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333211021546463840403294821 62477066539961970075617779)
        ·
          refine ⟨93715599809942955113426669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62477066539961970075617779 93715599809942955113426669)
          ·
            refine ⟨35143349928728608167535001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93715599809942955113426669 35143349928728608167535001)
            ·
              refine ⟨26357512446546456125651251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35143349928728608167535001 26357512446546456125651251)
              ·
                refine ⟨39536268669819684188476877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26357512446546456125651251 39536268669819684188476877)
                ·
                  refine ⟨14826100751182381570678829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39536268669819684188476877 14826100751182381570678829)
                  ·
                    refine ⟨5559787781693393089004561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14826100751182381570678829 5559787781693393089004561)
                    ·
                      refine ⟨4169840836270044816753421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5559787781693393089004561 4169840836270044816753421)
                      ·
                        rfl

theorem cell23_8120736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_8120736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120736 prefixEnd_8120736 := by exact prefixLift 8120736
  have htrace : WordTrace (prefixWord ++ tailWord_8120736) baseStart_8120736 baseEnd_8120736 := by
    simpa [prefixWord, tailWord_8120736, baseEnd_8120736] using wordTrace_append hprefix tailTrace_8120736
  have hstable : (prefixWord ++ tailWord_8120736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120736).length < 2 ^ (prefixWord ++ tailWord_8120736).sum := by decide
  have hdescent : baseEnd_8120736 < baseStart_8120736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120752 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 5]
def baseStart_8120752 : Nat := 118140960795 + 8120752 * 2 ^ 59
def prefixEnd_8120752 : Nat := 4983230072969 + 3 ^ 40 * 8120752 * 2
def baseEnd_8120752 : Nat := 4169849051960516754153347

theorem tailTrace_8120752 : CollatzResearch.WordTrace tailWord_8120752 prefixEnd_8120752 4169849051960516754153347 := by
  unfold tailWord_8120752
  simp only [CollatzResearch.WordTrace]
  refine ⟨148094079137954946434422255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197458772183939928579229673 148094079137954946434422255)
  ·
    refine ⟨222141118706932419651633383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148094079137954946434422255 222141118706932419651633383)
    ·
      refine ⟨333211678060398629477450075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222141118706932419651633383 333211678060398629477450075)
      ·
        refine ⟨499817517090597944216175113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333211678060398629477450075 499817517090597944216175113)
        ·
          refine ⟨374863137817948458162131335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499817517090597944216175113 374863137817948458162131335)
          ·
            refine ⟨562294706726922687243197003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374863137817948458162131335 562294706726922687243197003)
            ·
              refine ⟨843442060090384030864795505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562294706726922687243197003 843442060090384030864795505)
              ·
                refine ⟨632581545067788023148596629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843442060090384030864795505 632581545067788023148596629)
                ·
                  refine ⟨29652259925052563585090467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 632581545067788023148596629 29652259925052563585090467)
                  ·
                    refine ⟨44478389887578845377635701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29652259925052563585090467 44478389887578845377635701)
                    ·
                      refine ⟨4169849051960516754153347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44478389887578845377635701 4169849051960516754153347)
                      ·
                        rfl

theorem cell23_8120752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_8120752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120752 prefixEnd_8120752 := by exact prefixLift 8120752
  have htrace : WordTrace (prefixWord ++ tailWord_8120752) baseStart_8120752 baseEnd_8120752 := by
    simpa [prefixWord, tailWord_8120752, baseEnd_8120752] using wordTrace_append hprefix tailTrace_8120752
  have hstable : (prefixWord ++ tailWord_8120752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120752).length < 2 ^ (prefixWord ++ tailWord_8120752).sum := by decide
  have hdescent : baseEnd_8120752 < baseStart_8120752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120753 : List Nat := [1, 2, 2, 4, 1, 3, 1, 3, 1, 3, 2]
def baseStart_8120753 : Nat := 118140960795 + 8120753 * 2 ^ 59
def prefixEnd_8120753 : Nat := 4983230072969 + 3 ^ 40 * 8120753 * 2
def baseEnd_8120753 : Nat := 4169849565441171250240843

theorem tailTrace_8120753 : CollatzResearch.WordTrace tailWord_8120753 prefixEnd_8120753 4169849565441171250240843 := by
  unfold tailWord_8120753
  simp only [CollatzResearch.WordTrace]
  refine ⟨296188194748906270039630913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197458796499270846693087275 296188194748906270039630913)
  ·
    refine ⟨222141146061679702529723185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296188194748906270039630913 222141146061679702529723185)
    ·
      refine ⟨166605859546259776897292389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222141146061679702529723185 166605859546259776897292389)
      ·
        refine ⟨31238598664923708168242323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166605859546259776897292389 31238598664923708168242323)
        ·
          refine ⟨46857897997385562252363485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31238598664923708168242323 46857897997385562252363485)
          ·
            refine ⟨17571711749019585844636307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46857897997385562252363485 17571711749019585844636307)
            ·
              refine ⟨26357567623529378766954461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17571711749019585844636307 26357567623529378766954461)
              ·
                refine ⟨9884087858823517037607923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26357567623529378766954461 9884087858823517037607923)
                ·
                  refine ⟨14826131788235275556411885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9884087858823517037607923 14826131788235275556411885)
                  ·
                    refine ⟨5559799420588228333654457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14826131788235275556411885 5559799420588228333654457)
                    ·
                      refine ⟨4169849565441171250240843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5559799420588228333654457 4169849565441171250240843)
                      ·
                        rfl

theorem cell23_8120753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_8120753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120753 prefixEnd_8120753 := by exact prefixLift 8120753
  have htrace : WordTrace (prefixWord ++ tailWord_8120753) baseStart_8120753 baseEnd_8120753 := by
    simpa [prefixWord, tailWord_8120753, baseEnd_8120753] using wordTrace_append hprefix tailTrace_8120753
  have hstable : (prefixWord ++ tailWord_8120753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120753).length < 2 ^ (prefixWord ++ tailWord_8120753).sum := by decide
  have hdescent : baseEnd_8120753 < baseStart_8120753 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120766 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2]
def baseStart_8120766 : Nat := 118140960795 + 8120766 * 2 ^ 59
def prefixEnd_8120766 : Nat := 4983230072969 + 3 ^ 40 * 8120766 * 2
def baseEnd_8120766 : Nat := 4169856240689679699378283

theorem tailTrace_8120766 : CollatzResearch.WordTrace tailWord_8120766 prefixEnd_8120766 4169856240689679699378283 := by
  unfold tailWord_8120766
  simp only [CollatzResearch.WordTrace]
  refine ⟨37023583612232396657481769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197459112598572782173236101 37023583612232396657481769)
  ·
    refine ⟨27767687709174297493111327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37023583612232396657481769 27767687709174297493111327)
    ·
      refine ⟨41651531563761446239666991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27767687709174297493111327 41651531563761446239666991)
      ·
        refine ⟨62477297345642169359500487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41651531563761446239666991 62477297345642169359500487)
        ·
          refine ⟨93715946018463254039250731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62477297345642169359500487 93715946018463254039250731)
          ·
            refine ⟨140573919027694881058876097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93715946018463254039250731 140573919027694881058876097)
            ·
              refine ⟨105430439270771160794157073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140573919027694881058876097 105430439270771160794157073)
              ·
                refine ⟨79072829453078370595617805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105430439270771160794157073 79072829453078370595617805)
                ·
                  refine ⟨29652311044904388973356677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79072829453078370595617805 29652311044904388973356677)
                  ·
                    refine ⟨5559808320919572932504377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29652311044904388973356677 5559808320919572932504377)
                    ·
                      refine ⟨4169856240689679699378283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5559808320919572932504377 4169856240689679699378283)
                      ·
                        rfl

theorem cell23_8120766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_8120766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120766 prefixEnd_8120766 := by exact prefixLift 8120766
  have htrace : WordTrace (prefixWord ++ tailWord_8120766) baseStart_8120766 baseEnd_8120766 := by
    simpa [prefixWord, tailWord_8120766, baseEnd_8120766] using wordTrace_append hprefix tailTrace_8120766
  have hstable : (prefixWord ++ tailWord_8120766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120766).length < 2 ^ (prefixWord ++ tailWord_8120766).sum := by decide
  have hdescent : baseEnd_8120766 < baseStart_8120766 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120789 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 7]
def baseStart_8120789 : Nat := 118140960795 + 8120789 * 2 ^ 59
def prefixEnd_8120789 : Nat := 4983230072969 + 3 ^ 40 * 8120789 * 2
def baseEnd_8120789 : Nat := 463318672304970345487853

theorem tailTrace_8120789 : CollatzResearch.WordTrace tailWord_8120789 prefixEnd_8120789 463318672304970345487853 := by
  unfold tailWord_8120789
  simp only [CollatzResearch.WordTrace]
  refine ⟨296189507776775848187941421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197459671851183898791960947 296189507776775848187941421)
  ·
    refine ⟨111071065416290943070478033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296189507776775848187941421 111071065416290943070478033)
    ·
      refine ⟨83303299062218207302858525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111071065416290943070478033 83303299062218207302858525)
      ·
        refine ⟨31238737148331827738571947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83303299062218207302858525 31238737148331827738571947)
        ·
          refine ⟨46858105722497741607857921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31238737148331827738571947 46858105722497741607857921)
          ·
            refine ⟨35143579291873306205893441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46858105722497741607857921 35143579291873306205893441)
            ·
              refine ⟨26357684468904979654420081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35143579291873306205893441 26357684468904979654420081)
              ·
                refine ⟨19768263351678734740815061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26357684468904979654420081 19768263351678734740815061)
                ·
                  refine ⟨463318672304970345487853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19768263351678734740815061 463318672304970345487853)
                  ·
                    rfl

theorem cell23_8120789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 7].length) (baseStart_8120789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120789 prefixEnd_8120789 := by exact prefixLift 8120789
  have htrace : WordTrace (prefixWord ++ tailWord_8120789) baseStart_8120789 baseEnd_8120789 := by
    simpa [prefixWord, tailWord_8120789, baseEnd_8120789] using wordTrace_append hprefix tailTrace_8120789
  have hstable : (prefixWord ++ tailWord_8120789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120789).length < 2 ^ (prefixWord ++ tailWord_8120789).sum := by decide
  have hdescent : baseEnd_8120789 < baseStart_8120789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120819 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 2, 5]
def baseStart_8120819 : Nat := 118140960795 + 8120819 * 2 ^ 59
def prefixEnd_8120819 : Nat := 4983230072969 + 3 ^ 40 * 8120819 * 2
def baseEnd_8120819 : Nat := 1389961151721455997338513

theorem tailTrace_8120819 : CollatzResearch.WordTrace tailWord_8120819 prefixEnd_8120819 1389961151721455997338513 := by
  unfold tailWord_8120819
  simp only [CollatzResearch.WordTrace]
  refine ⟨296190601966667163311533511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197460401311111442207689007 296190601966667163311533511)
  ·
    refine ⟨444285902950000744967300267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296190601966667163311533511 444285902950000744967300267)
    ·
      refine ⟨666428854425001117450950401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444285902950000744967300267 666428854425001117450950401)
      ·
        refine ⟨499821640818750838088212801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666428854425001117450950401 499821640818750838088212801)
        ·
          refine ⟨374866230614063128566159601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499821640818750838088212801 374866230614063128566159601)
          ·
            refine ⟨281149672960547346424619701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374866230614063128566159601 281149672960547346424619701)
            ·
              refine ⟨26357781840051313727308097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 281149672960547346424619701 26357781840051313727308097)
              ·
                refine ⟨19768336380038485295481073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26357781840051313727308097 19768336380038485295481073)
                ·
                  refine ⟨14826252285028863971610805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19768336380038485295481073 14826252285028863971610805)
                  ·
                    refine ⟨1389961151721455997338513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14826252285028863971610805 1389961151721455997338513)
                    ·
                      rfl

theorem cell23_8120819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 5].length) (baseStart_8120819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120819 prefixEnd_8120819 := by exact prefixLift 8120819
  have htrace : WordTrace (prefixWord ++ tailWord_8120819) baseStart_8120819 baseEnd_8120819 := by
    simpa [prefixWord, tailWord_8120819, baseEnd_8120819] using wordTrace_append hprefix tailTrace_8120819
  have hstable : (prefixWord ++ tailWord_8120819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120819).length < 2 ^ (prefixWord ++ tailWord_8120819).sum := by decide
  have hdescent : baseEnd_8120819 < baseStart_8120819 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120829 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_8120829 : Nat := 118140960795 + 8120829 * 2 ^ 59
def prefixEnd_8120829 : Nat := 4983230072969 + 3 ^ 40 * 8120829 * 2
def baseEnd_8120829 : Nat := 4169888589970912952890493

theorem tailTrace_8120829 : CollatzResearch.WordTrace tailWord_8120829 prefixEnd_8120829 4169888589970912952890493 := by
  unfold tailWord_8120829
  simp only [CollatzResearch.WordTrace]
  refine ⟨296190966696630935019397541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197460644464420623346265027 296190966696630935019397541)
  ·
    refine ⟨55535806255618300316137039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296190966696630935019397541 55535806255618300316137039)
    ·
      refine ⟨83303709383427450474205559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55535806255618300316137039 83303709383427450474205559)
      ·
        refine ⟨124955564075141175711308339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83303709383427450474205559 124955564075141175711308339)
        ·
          refine ⟨187433346112711763566962509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124955564075141175711308339 187433346112711763566962509)
          ·
            refine ⟨70287504792266911337610941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187433346112711763566962509 70287504792266911337610941)
            ·
              refine ⟨26357814297100091751604103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70287504792266911337610941 26357814297100091751604103)
              ·
                refine ⟨39536721445650137627406155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26357814297100091751604103 39536721445650137627406155)
                ·
                  refine ⟨59305082168475206441109233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39536721445650137627406155 59305082168475206441109233)
                  ·
                    refine ⟨44478811626356404830831925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59305082168475206441109233 44478811626356404830831925)
                    ·
                      refine ⟨4169888589970912952890493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44478811626356404830831925 4169888589970912952890493)
                      ·
                        rfl

theorem cell23_8120829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_8120829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120829 prefixEnd_8120829 := by exact prefixLift 8120829
  have htrace : WordTrace (prefixWord ++ tailWord_8120829) baseStart_8120829 baseEnd_8120829 := by
    simpa [prefixWord, tailWord_8120829, baseEnd_8120829] using wordTrace_append hprefix tailTrace_8120829
  have hstable : (prefixWord ++ tailWord_8120829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120829).length < 2 ^ (prefixWord ++ tailWord_8120829).sum := by decide
  have hdescent : baseEnd_8120829 < baseStart_8120829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120856 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 2, 1, 4]
def baseStart_8120856 : Nat := 118140960795 + 8120856 * 2 ^ 59
def prefixEnd_8120856 : Nat := 4983230072969 + 3 ^ 40 * 8120856 * 2
def baseEnd_8120856 : Nat := 4169902453948584347252869

theorem tailTrace_8120856 : CollatzResearch.WordTrace tailWord_8120856 prefixEnd_8120856 4169902453948584347252869 := by
  unfold tailWord_8120856
  simp only [CollatzResearch.WordTrace]
  refine ⟨148095975733766559315315211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197461300978355412420420281 148095975733766559315315211)
  ·
    refine ⟨222143963600649838972972817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148095975733766559315315211 222143963600649838972972817)
    ·
      refine ⟨166607972700487379229729613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222143963600649838972972817 166607972700487379229729613)
      ·
        refine ⟨62477989762682767211148605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166607972700487379229729613 62477989762682767211148605)
        ·
          refine ⟨23429246161006037704180727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62477989762682767211148605 23429246161006037704180727)
          ·
            refine ⟨35143869241509056556271091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23429246161006037704180727 35143869241509056556271091)
            ·
              refine ⟨52715803862263584834406637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35143869241509056556271091 52715803862263584834406637)
              ·
                refine ⟨19768426448348844312902489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52715803862263584834406637 19768426448348844312902489)
                ·
                  refine ⟨14826319836261633234676867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19768426448348844312902489 14826319836261633234676867)
                  ·
                    refine ⟨22239479754392449852015301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14826319836261633234676867 22239479754392449852015301)
                    ·
                      refine ⟨4169902453948584347252869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22239479754392449852015301 4169902453948584347252869)
                      ·
                        rfl

theorem cell23_8120856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_8120856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120856 prefixEnd_8120856 := by exact prefixLift 8120856
  have htrace : WordTrace (prefixWord ++ tailWord_8120856) baseStart_8120856 baseEnd_8120856 := by
    simpa [prefixWord, tailWord_8120856, baseEnd_8120856] using wordTrace_append hprefix tailTrace_8120856
  have hstable : (prefixWord ++ tailWord_8120856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120856).length < 2 ^ (prefixWord ++ tailWord_8120856).sum := by decide
  have hdescent : baseEnd_8120856 < baseStart_8120856 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120883 : List Nat := [1, 1, 1, 2, 4, 2, 3, 4, 1, 4]
def baseStart_8120883 : Nat := 118140960795 + 8120883 * 2 ^ 59
def prefixEnd_8120883 : Nat := 4983230072969 + 3 ^ 40 * 8120883 * 2
def baseEnd_8120883 : Nat := 1389972105975418580538415

theorem tailTrace_8120883 : CollatzResearch.WordTrace tailWord_8120883 prefixEnd_8120883 1389972105975418580538415 := by
  unfold tailWord_8120883
  simp only [CollatzResearch.WordTrace]
  refine ⟨296192936238435302241863303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197461957492290201494575535 296192936238435302241863303)
  ·
    refine ⟨444289404357652953362794955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296192936238435302241863303 444289404357652953362794955)
    ·
      refine ⟨666434106536479430044192433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444289404357652953362794955 666434106536479430044192433)
      ·
        refine ⟨499825579902359572533144325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666434106536479430044192433 499825579902359572533144325)
        ·
          refine ⟨93717296231692419849964561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 499825579902359572533144325 93717296231692419849964561)
          ·
            refine ⟨70287972173769314887473421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93717296231692419849964561 70287972173769314887473421)
            ·
              refine ⟨26357989565163493082802533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70287972173769314887473421 26357989565163493082802533)
              ·
                refine ⟨4942123043468154953025475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26357989565163493082802533 4942123043468154953025475)
                ·
                  refine ⟨7413184565202232429538213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4942123043468154953025475 7413184565202232429538213)
                  ·
                    refine ⟨1389972105975418580538415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7413184565202232429538213 1389972105975418580538415)
                    ·
                      rfl

theorem cell23_8120883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 1, 4].length) (baseStart_8120883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120883 prefixEnd_8120883 := by exact prefixLift 8120883
  have htrace : WordTrace (prefixWord ++ tailWord_8120883) baseStart_8120883 baseEnd_8120883 := by
    simpa [prefixWord, tailWord_8120883, baseEnd_8120883] using wordTrace_append hprefix tailTrace_8120883
  have hstable : (prefixWord ++ tailWord_8120883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120883).length < 2 ^ (prefixWord ++ tailWord_8120883).sum := by decide
  have hdescent : baseEnd_8120883 < baseStart_8120883 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120940 : List Nat := [2, 2, 1, 1, 3, 1, 4, 4, 1, 1, 3]
def baseStart_8120940 : Nat := 118140960795 + 8120940 * 2 ^ 59
def prefixEnd_8120940 : Nat := 4983230072969 + 3 ^ 40 * 8120940 * 2
def baseEnd_8120940 : Nat := 4169945586323562018602483

theorem tailTrace_8120940 : CollatzResearch.WordTrace tailWord_8120940 prefixEnd_8120940 4169945586323562018602483 := by
  unfold tailWord_8120940
  simp only [CollatzResearch.WordTrace]
  refine ⟨148097507599614400488344137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197463343466152533984458849 148097507599614400488344137)
  ·
    refine ⟨111073130699710800366258103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148097507599614400488344137 111073130699710800366258103)
    ·
      refine ⟨166609696049566200549387155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111073130699710800366258103 166609696049566200549387155)
      ·
        refine ⟨249914544074349300824080733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166609696049566200549387155 249914544074349300824080733)
        ·
          refine ⟨93717954027880987809030275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249914544074349300824080733 93717954027880987809030275)
          ·
            refine ⟨140576931041821481713545413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93717954027880987809030275 140576931041821481713545413)
            ·
              refine ⟨26358174570341527821289765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140576931041821481713545413 26358174570341527821289765)
              ·
                refine ⟨4942157731939036466491831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26358174570341527821289765 4942157731939036466491831)
                ·
                  refine ⟨7413236597908554699737747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4942157731939036466491831 7413236597908554699737747)
                  ·
                    refine ⟨11119854896862832049606621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7413236597908554699737747 11119854896862832049606621)
                    ·
                      refine ⟨4169945586323562018602483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11119854896862832049606621 4169945586323562018602483)
                      ·
                        rfl

theorem cell23_8120940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 1, 1, 3].length) (baseStart_8120940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120940 prefixEnd_8120940 := by exact prefixLift 8120940
  have htrace : WordTrace (prefixWord ++ tailWord_8120940) baseStart_8120940 baseEnd_8120940 := by
    simpa [prefixWord, tailWord_8120940, baseEnd_8120940] using wordTrace_append hprefix tailTrace_8120940
  have hstable : (prefixWord ++ tailWord_8120940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120940).length < 2 ^ (prefixWord ++ tailWord_8120940).sum := by decide
  have hdescent : baseEnd_8120940 < baseStart_8120940 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120956 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 1, 6]
def baseStart_8120956 : Nat := 118140960795 + 8120956 * 2 ^ 59
def prefixEnd_8120956 : Nat := 4983230072969 + 3 ^ 40 * 8120956 * 2
def baseEnd_8120956 : Nat := 1389984600671344652000803

theorem tailTrace_8120956 : CollatzResearch.WordTrace tailWord_8120956 prefixEnd_8120956 1389984600671344652000803 := by
  unfold tailWord_8120956
  simp only [CollatzResearch.WordTrace]
  refine ⟨148097799383585417854635361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197463732511447223806180481 148097799383585417854635361)
  ·
    refine ⟨111073349537689063390976521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148097799383585417854635361 111073349537689063390976521)
    ·
      refine ⟨83305012153266797543232391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111073349537689063390976521 83305012153266797543232391)
      ·
        refine ⟨124957518229900196314848587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83305012153266797543232391 124957518229900196314848587)
        ·
          refine ⟨187436277344850294472272881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124957518229900196314848587 187436277344850294472272881)
          ·
            refine ⟨140577208008637720854204661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187436277344850294472272881 140577208008637720854204661)
            ·
              refine ⟨13179113250809786330081687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140577208008637720854204661 13179113250809786330081687)
              ·
                refine ⟨19768669876214679495122531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13179113250809786330081687 19768669876214679495122531)
                ·
                  refine ⟨29653004814322019242683797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19768669876214679495122531 29653004814322019242683797)
                  ·
                    refine ⟨1389984600671344652000803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29653004814322019242683797 1389984600671344652000803)
                    ·
                      rfl

theorem cell23_8120956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_8120956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120956 prefixEnd_8120956 := by exact prefixLift 8120956
  have htrace : WordTrace (prefixWord ++ tailWord_8120956) baseStart_8120956 baseEnd_8120956 := by
    simpa [prefixWord, tailWord_8120956, baseEnd_8120956] using wordTrace_append hprefix tailTrace_8120956
  have hstable : (prefixWord ++ tailWord_8120956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120956).length < 2 ^ (prefixWord ++ tailWord_8120956).sum := by decide
  have hdescent : baseEnd_8120956 < baseStart_8120956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120980 : List Nat := [2, 4, 2, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_8120980 : Nat := 118140960795 + 8120980 * 2 ^ 59
def prefixEnd_8120980 : Nat := 4983230072969 + 3 ^ 40 * 8120980 * 2
def baseEnd_8120980 : Nat := 4169966125549741862102299

theorem tailTrace_8120980 : CollatzResearch.WordTrace tailWord_8120980 prefixEnd_8120980 4169966125549741862102299 := by
  unfold tailWord_8120980
  simp only [CollatzResearch.WordTrace]
  refine ⟨148098237059541943904072197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197464316079389258538762929 148098237059541943904072197)
  ·
    refine ⟨27768419448664114482013537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148098237059541943904072197 27768419448664114482013537)
    ·
      refine ⟨20826314586498085861510153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27768419448664114482013537 20826314586498085861510153)
      ·
        refine ⟨15619735939873564396132615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20826314586498085861510153 15619735939873564396132615)
        ·
          refine ⟨23429603909810346594198923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15619735939873564396132615 23429603909810346594198923)
          ·
            refine ⟨35144405864715519891298385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23429603909810346594198923 35144405864715519891298385)
            ·
              refine ⟨26358304398536639918473789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35144405864715519891298385 26358304398536639918473789)
              ·
                refine ⟨9884364149451239969427671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26358304398536639918473789 9884364149451239969427671)
                ·
                  refine ⟨14826546224176859954141507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9884364149451239969427671 14826546224176859954141507)
                  ·
                    refine ⟨22239819336265289931212261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14826546224176859954141507 22239819336265289931212261)
                    ·
                      refine ⟨4169966125549741862102299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22239819336265289931212261 4169966125549741862102299)
                      ·
                        rfl

theorem cell23_8120980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_8120980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120980 prefixEnd_8120980 := by exact prefixLift 8120980
  have htrace : WordTrace (prefixWord ++ tailWord_8120980) baseStart_8120980 baseEnd_8120980 := by
    simpa [prefixWord, tailWord_8120980, baseEnd_8120980] using wordTrace_append hprefix tailTrace_8120980
  have hstable : (prefixWord ++ tailWord_8120980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120980).length < 2 ^ (prefixWord ++ tailWord_8120980).sum := by decide
  have hdescent : baseEnd_8120980 < baseStart_8120980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120983 : List Nat := [1, 1, 3, 3, 2, 1, 1, 5, 1, 2, 3]
def baseStart_8120983 : Nat := 118140960795 + 8120983 * 2 ^ 59
def prefixEnd_8120983 : Nat := 4983230072969 + 3 ^ 40 * 8120983 * 2
def baseEnd_8120983 : Nat := 4169967665991705350364785

theorem tailTrace_8120983 : CollatzResearch.WordTrace tailWord_8120983 prefixEnd_8120983 4169967665991705350364785 := by
  unfold tailWord_8120983
  simp only [CollatzResearch.WordTrace]
  refine ⟨296196583538073019320503603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197464389025382012880335735 296196583538073019320503603)
  ·
    refine ⟨444294875307109528980755405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296196583538073019320503603 444294875307109528980755405)
    ·
      refine ⟨166610578240166073367783277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444294875307109528980755405 166610578240166073367783277)
      ·
        refine ⟨62478966840062277512918729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166610578240166073367783277 62478966840062277512918729)
        ·
          refine ⟨46859225130046708134689047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62478966840062277512918729 46859225130046708134689047)
          ·
            refine ⟨70288837695070062202033571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46859225130046708134689047 70288837695070062202033571)
            ·
              refine ⟨105433256542605093303050357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70288837695070062202033571 105433256542605093303050357)
              ·
                refine ⟨9884367800869227497160971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105433256542605093303050357 9884367800869227497160971)
                ·
                  refine ⟨14826551701303841245741457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9884367800869227497160971 14826551701303841245741457)
                  ·
                    refine ⟨11119913775977880934306093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14826551701303841245741457 11119913775977880934306093)
                    ·
                      refine ⟨4169967665991705350364785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11119913775977880934306093 4169967665991705350364785)
                      ·
                        rfl

theorem cell23_8120983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_8120983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120983 prefixEnd_8120983 := by exact prefixLift 8120983
  have htrace : WordTrace (prefixWord ++ tailWord_8120983) baseStart_8120983 baseEnd_8120983 := by
    simpa [prefixWord, tailWord_8120983, baseEnd_8120983] using wordTrace_append hprefix tailTrace_8120983
  have hstable : (prefixWord ++ tailWord_8120983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120983).length < 2 ^ (prefixWord ++ tailWord_8120983).sum := by decide
  have hdescent : baseEnd_8120983 < baseStart_8120983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8120990 : List Nat := [4, 3, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_8120990 : Nat := 118140960795 + 8120990 * 2 ^ 59
def prefixEnd_8120990 : Nat := 4983230072969 + 3 ^ 40 * 8120990 * 2
def baseEnd_8120990 : Nat := 1389990420118762274325751

theorem tailTrace_8120990 : CollatzResearch.WordTrace tailWord_8120990 prefixEnd_8120990 1389990420118762274325751 := by
  unfold tailWord_8120990
  simp only [CollatzResearch.WordTrace]
  refine ⟨37024604856130957439501053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197464559232698439677338949 37024604856130957439501053)
  ·
    refine ⟨13884226821049109039812895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37024604856130957439501053 13884226821049109039812895)
    ·
      refine ⟨20826340231573663559719343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13884226821049109039812895 20826340231573663559719343)
      ·
        refine ⟨31239510347360495339579015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20826340231573663559719343 31239510347360495339579015)
        ·
          refine ⟨46859265521040743009368523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31239510347360495339579015 46859265521040743009368523)
          ·
            refine ⟨70288898281561114514052785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46859265521040743009368523 70288898281561114514052785)
            ·
              refine ⟨52716673711170835885539589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70288898281561114514052785 52716673711170835885539589)
              ·
                refine ⟨9884376320844531728538673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52716673711170835885539589 9884376320844531728538673)
                ·
                  refine ⟨7413282240633398796404005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9884376320844531728538673 7413282240633398796404005)
                  ·
                    refine ⟨1389990420118762274325751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7413282240633398796404005 1389990420118762274325751)
                    ·
                      rfl

theorem cell23_8120990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_8120990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8120990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8120990 prefixEnd_8120990 := by exact prefixLift 8120990
  have htrace : WordTrace (prefixWord ++ tailWord_8120990) baseStart_8120990 baseEnd_8120990 := by
    simpa [prefixWord, tailWord_8120990, baseEnd_8120990] using wordTrace_append hprefix tailTrace_8120990
  have hstable : (prefixWord ++ tailWord_8120990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8120990).length < 2 ^ (prefixWord ++ tailWord_8120990).sum := by decide
  have hdescent : baseEnd_8120990 < baseStart_8120990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8120990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121014 : List Nat := [5, 1, 3, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_8121014 : Nat := 118140960795 + 8121014 * 2 ^ 59
def prefixEnd_8121014 : Nat := 4983230072969 + 3 ^ 40 * 8121014 * 2
def baseEnd_8121014 : Nat := 4169983583891994729077143

theorem tailTrace_8121014 : CollatzResearch.WordTrace tailWord_8121014 prefixEnd_8121014 4169983583891994729077143 := by
  unfold tailWord_8121014
  simp only [CollatzResearch.WordTrace]
  refine ⟨18512357137560044475930131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197465142800640474409921397 18512357137560044475930131)
  ·
    refine ⟨27768535706340066713895197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18512357137560044475930131 27768535706340066713895197)
    ·
      refine ⟨10413200889877525017710699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27768535706340066713895197 10413200889877525017710699)
      ·
        refine ⟨15619801334816287526566049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10413200889877525017710699 15619801334816287526566049)
        ·
          refine ⟨11714851001112215644924537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15619801334816287526566049 11714851001112215644924537)
          ·
            refine ⟨8786138250834161733693403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11714851001112215644924537 8786138250834161733693403)
            ·
              refine ⟨13179207376251242600540105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8786138250834161733693403 13179207376251242600540105)
              ·
                refine ⟨9884405532188431950405079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13179207376251242600540105 9884405532188431950405079)
                ·
                  refine ⟨14826608298282647925607619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9884405532188431950405079 14826608298282647925607619)
                  ·
                    refine ⟨22239912447423971888411429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14826608298282647925607619 22239912447423971888411429)
                    ·
                      refine ⟨4169983583891994729077143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22239912447423971888411429 4169983583891994729077143)
                      ·
                        rfl

theorem cell23_8121014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_8121014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121014 prefixEnd_8121014 := by exact prefixLift 8121014
  have htrace : WordTrace (prefixWord ++ tailWord_8121014) baseStart_8121014 baseEnd_8121014 := by
    simpa [prefixWord, tailWord_8121014, baseEnd_8121014] using wordTrace_append hprefix tailTrace_8121014
  have hstable : (prefixWord ++ tailWord_8121014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121014).length < 2 ^ (prefixWord ++ tailWord_8121014).sum := by decide
  have hdescent : baseEnd_8121014 < baseStart_8121014 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121019 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 10]
def baseStart_8121019 : Nat := 118140960795 + 8121019 * 2 ^ 59
def prefixEnd_8121019 : Nat := 4983230072969 + 3 ^ 40 * 8121019 * 2
def baseEnd_8121019 : Nat := 4169986151295267209514619

theorem tailTrace_8121019 : CollatzResearch.WordTrace tailWord_8121019 prefixEnd_8121019 4169986151295267209514619 := by
  unfold tailWord_8121019
  simp only [CollatzResearch.WordTrace]
  refine ⟨296197896565942597468814111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197465264377295064979209407 296197896565942597468814111)
  ·
    refine ⟨444296844848913896203221167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296197896565942597468814111 444296844848913896203221167)
    ·
      refine ⟨666445267273370844304831751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444296844848913896203221167 666445267273370844304831751)
      ·
        refine ⟨999667900910056266457247627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666445267273370844304831751 999667900910056266457247627)
        ·
          refine ⟨1499501851365084399685871441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999667900910056266457247627 1499501851365084399685871441)
          ·
            refine ⟨1124626388523813299764403581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1499501851365084399685871441 1124626388523813299764403581)
            ·
              refine ⟨421734895696429987411651343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1124626388523813299764403581 421734895696429987411651343)
              ·
                refine ⟨632602343544644981117477015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421734895696429987411651343 632602343544644981117477015)
                ·
                  refine ⟨948903515316967471676215523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632602343544644981117477015 948903515316967471676215523)
                  ·
                    refine ⟨1423355272975451207514323285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 948903515316967471676215523 1423355272975451207514323285)
                    ·
                      refine ⟨4169986151295267209514619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1423355272975451207514323285 4169986151295267209514619)
                      ·
                        rfl

theorem cell23_8121019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 10].length) (baseStart_8121019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121019 prefixEnd_8121019 := by exact prefixLift 8121019
  have htrace : WordTrace (prefixWord ++ tailWord_8121019) baseStart_8121019 baseEnd_8121019 := by
    simpa [prefixWord, tailWord_8121019, baseEnd_8121019] using wordTrace_append hprefix tailTrace_8121019
  have hstable : (prefixWord ++ tailWord_8121019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121019).length < 2 ^ (prefixWord ++ tailWord_8121019).sum := by decide
  have hdescent : baseEnd_8121019 < baseStart_8121019 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121070 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 1, 4, 2]
def baseStart_8121070 : Nat := 118140960795 + 8121070 * 2 ^ 59
def prefixEnd_8121070 : Nat := 4983230072969 + 3 ^ 40 * 8121070 * 2
def baseEnd_8121070 : Nat := 4170012338808646509976885

theorem tailTrace_8121070 : CollatzResearch.WordTrace tailWord_8121070 prefixEnd_8121070 4170012338808646509976885 := by
  unfold tailWord_8121070
  simp only [CollatzResearch.WordTrace]
  refine ⟨37024969586094729147365083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197466504459171888785947109 37024969586094729147365083)
  ·
    refine ⟨55537454379142093721047625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37024969586094729147365083 55537454379142093721047625)
    ·
      refine ⟨41653090784356570290785719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55537454379142093721047625 41653090784356570290785719)
      ·
        refine ⟨62479636176534855436178579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41653090784356570290785719 62479636176534855436178579)
        ·
          refine ⟨93719454264802283154267869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62479636176534855436178579 93719454264802283154267869)
          ·
            refine ⟨35144795349300856182850451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93719454264802283154267869 35144795349300856182850451)
            ·
              refine ⟨52717193023951284274275677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35144795349300856182850451 52717193023951284274275677)
              ·
                refine ⟨19768947383981731602853379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52717193023951284274275677 19768947383981731602853379)
                ·
                  refine ⟨29653421075972597404280069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19768947383981731602853379 29653421075972597404280069)
                  ·
                    refine ⟨5560016451744862013302513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29653421075972597404280069 5560016451744862013302513)
                    ·
                      refine ⟨4170012338808646509976885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5560016451744862013302513 4170012338808646509976885)
                      ·
                        rfl

theorem cell23_8121070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_8121070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121070 prefixEnd_8121070 := by exact prefixLift 8121070
  have htrace : WordTrace (prefixWord ++ tailWord_8121070) baseStart_8121070 baseEnd_8121070 := by
    simpa [prefixWord, tailWord_8121070, baseEnd_8121070] using wordTrace_append hprefix tailTrace_8121070
  have hstable : (prefixWord ++ tailWord_8121070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121070).length < 2 ^ (prefixWord ++ tailWord_8121070).sum := by decide
  have hdescent : baseEnd_8121070 < baseStart_8121070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121113 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 2, 5, 2]
def baseStart_8121113 : Nat := 118140960795 + 8121113 * 2 ^ 59
def prefixEnd_8121113 : Nat := 4983230072969 + 3 ^ 40 * 8121113 * 2
def baseEnd_8121113 : Nat := 4170034418476789841739187

theorem tailTrace_8121113 : CollatzResearch.WordTrace tailWord_8121113 prefixEnd_8121113 4170034418476789841739187 := by
  unfold tailWord_8121113
  simp only [CollatzResearch.WordTrace]
  refine ⟨296201325027602051522735993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197467550018401367681823995 296201325027602051522735993)
  ·
    refine ⟨222150993770701538642051995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296201325027602051522735993 222150993770701538642051995)
    ·
      refine ⟨333226490656052307963077993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222150993770701538642051995 333226490656052307963077993)
      ·
        refine ⟨249919867992039230972308495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333226490656052307963077993 249919867992039230972308495)
        ·
          refine ⟨374879801988058846458462743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249919867992039230972308495 374879801988058846458462743)
          ·
            refine ⟨562319702982088269687694115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374879801988058846458462743 562319702982088269687694115)
            ·
              refine ⟨843479554473132404531541173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562319702982088269687694115 843479554473132404531541173)
              ·
                refine ⟨79076208231856162924831985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 843479554473132404531541173 79076208231856162924831985)
                ·
                  refine ⟨59307156173892122193623989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79076208231856162924831985 59307156173892122193623989)
                  ·
                    refine ⟨5560045891302386455652249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59307156173892122193623989 5560045891302386455652249)
                    ·
                      refine ⟨4170034418476789841739187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5560045891302386455652249 4170034418476789841739187)
                      ·
                        rfl

theorem cell23_8121113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 5, 2].length) (baseStart_8121113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121113 prefixEnd_8121113 := by exact prefixLift 8121113
  have htrace : WordTrace (prefixWord ++ tailWord_8121113) baseStart_8121113 baseEnd_8121113 := by
    simpa [prefixWord, tailWord_8121113, baseEnd_8121113] using wordTrace_append hprefix tailTrace_8121113
  have hstable : (prefixWord ++ tailWord_8121113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121113).length < 2 ^ (prefixWord ++ tailWord_8121113).sum := by decide
  have hdescent : baseEnd_8121113 < baseStart_8121113 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121143 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 4]
def baseStart_8121143 : Nat := 118140960795 + 8121143 * 2 ^ 59
def prefixEnd_8121143 : Nat := 4983230072969 + 3 ^ 40 * 8121143 * 2
def baseEnd_8121143 : Nat := 4170049822896424724364049

theorem tailTrace_8121143 : CollatzResearch.WordTrace tailWord_8121143 prefixEnd_8121143 4170049822896424724364049 := by
  unfold tailWord_8121143
  simp only [CollatzResearch.WordTrace]
  refine ⟨296202419217493366646328083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197468279478328911097552055 296202419217493366646328083)
  ·
    refine ⟨444303628826240049969492125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296202419217493366646328083 444303628826240049969492125)
    ·
      refine ⟨166613860809840018738559547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444303628826240049969492125 166613860809840018738559547)
      ·
        refine ⟨249920791214760028107839321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166613860809840018738559547 249920791214760028107839321)
        ·
          refine ⟨187440593411070021080879491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249920791214760028107839321 187440593411070021080879491)
          ·
            refine ⟨281160890116605031621319237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187440593411070021080879491 281160890116605031621319237)
            ·
              refine ⟨52717666896863443428997357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281160890116605031621319237 52717666896863443428997357)
              ·
                refine ⟨19769125086323791285874009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52717666896863443428997357 19769125086323791285874009)
                ·
                  refine ⟨14826843814742843464405507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19769125086323791285874009 14826843814742843464405507)
                  ·
                    refine ⟨22240265722114265196608261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14826843814742843464405507 22240265722114265196608261)
                    ·
                      refine ⟨4170049822896424724364049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22240265722114265196608261 4170049822896424724364049)
                      ·
                        rfl

theorem cell23_8121143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_8121143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121143 prefixEnd_8121143 := by exact prefixLift 8121143
  have htrace : WordTrace (prefixWord ++ tailWord_8121143) baseStart_8121143 baseEnd_8121143 := by
    simpa [prefixWord, tailWord_8121143, baseEnd_8121143] using wordTrace_append hprefix tailTrace_8121143
  have hstable : (prefixWord ++ tailWord_8121143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121143).length < 2 ^ (prefixWord ++ tailWord_8121143).sum := by decide
  have hdescent : baseEnd_8121143 < baseStart_8121143 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121183 : List Nat := [1, 1, 2, 3, 1, 3, 3, 3, 6]
def baseStart_8121183 : Nat := 118140960795 + 8121183 * 2 ^ 59
def prefixEnd_8121183 : Nat := 4983230072969 + 3 ^ 40 * 8121183 * 2
def baseEnd_8121183 : Nat := 463341151346956063095985

theorem tailTrace_8121183 : CollatzResearch.WordTrace tailWord_8121183 prefixEnd_8121183 463341151346956063095985 := by
  unfold tailWord_8121183
  simp only [CollatzResearch.WordTrace]
  refine ⟨296203878137348453477784203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197469252091565635651856135 296203878137348453477784203)
  ·
    refine ⟨444305817206022680216676305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296203878137348453477784203 444305817206022680216676305)
    ·
      refine ⟨333229362904517010162507229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444305817206022680216676305 333229362904517010162507229)
      ·
        refine ⟨124961011089193878810940211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333229362904517010162507229 124961011089193878810940211)
        ·
          refine ⟨187441516633790818216410317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124961011089193878810940211 187441516633790818216410317)
          ·
            refine ⟨70290568737671556831153869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187441516633790818216410317 70290568737671556831153869)
            ·
              refine ⟨26358963276626833811682701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70290568737671556831153869 26358963276626833811682701)
              ·
                refine ⟨9884611228735062679381013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26358963276626833811682701 9884611228735062679381013)
                ·
                  refine ⟨463341151346956063095985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9884611228735062679381013 463341151346956063095985)
                  ·
                    rfl

theorem cell23_8121183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 6].length) (baseStart_8121183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121183 prefixEnd_8121183 := by exact prefixLift 8121183
  have htrace : WordTrace (prefixWord ++ tailWord_8121183) baseStart_8121183 baseEnd_8121183 := by
    simpa [prefixWord, tailWord_8121183, baseEnd_8121183] using wordTrace_append hprefix tailTrace_8121183
  have hstable : (prefixWord ++ tailWord_8121183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121183).length < 2 ^ (prefixWord ++ tailWord_8121183).sum := by decide
  have hdescent : baseEnd_8121183 < baseStart_8121183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121220 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 3, 5, 2]
def baseStart_8121220 : Nat := 118140960795 + 8121220 * 2 ^ 59
def prefixEnd_8121220 : Nat := 4983230072969 + 3 ^ 40 * 8121220 * 2
def baseEnd_8121220 : Nat := 4170089360906820923101195

theorem tailTrace_8121220 : CollatzResearch.WordTrace tailWord_8121220 prefixEnd_8121220 4170089360906820923101195 := by
  unfold tailWord_8121220
  simp only [CollatzResearch.WordTrace]
  refine ⟨148102613819107204398440557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197470151758809605864587409 148102613819107204398440557)
  ·
    refine ⟨55538480182165201649415209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148102613819107204398440557 55538480182165201649415209)
    ·
      refine ⟨41653860136623901237061407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55538480182165201649415209 41653860136623901237061407)
      ·
        refine ⟨62480790204935851855592111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41653860136623901237061407 62480790204935851855592111)
        ·
          refine ⟨93721185307403777783388167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62480790204935851855592111 93721185307403777783388167)
          ·
            refine ⟨140581777961105666675082251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93721185307403777783388167 140581777961105666675082251)
            ·
              refine ⟨210872666941658500012623377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140581777961105666675082251 210872666941658500012623377)
              ·
                refine ⟨158154500206243875009467533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210872666941658500012623377 158154500206243875009467533)
                ·
                  refine ⟨59307937577341453128550325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158154500206243875009467533 59307937577341453128550325)
                  ·
                    refine ⟨5560119147875761230801593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59307937577341453128550325 5560119147875761230801593)
                    ·
                      refine ⟨4170089360906820923101195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5560119147875761230801593 4170089360906820923101195)
                      ·
                        rfl

theorem cell23_8121220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_8121220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121220 prefixEnd_8121220 := by exact prefixLift 8121220
  have htrace : WordTrace (prefixWord ++ tailWord_8121220) baseStart_8121220 baseEnd_8121220 := by
    simpa [prefixWord, tailWord_8121220, baseEnd_8121220] using wordTrace_append hprefix tailTrace_8121220
  have hstable : (prefixWord ++ tailWord_8121220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121220).length < 2 ^ (prefixWord ++ tailWord_8121220).sum := by decide
  have hdescent : baseEnd_8121220 < baseStart_8121220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121244 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_8121244 : Nat := 118140960795 + 8121244 * 2 ^ 59
def prefixEnd_8121244 : Nat := 4983230072969 + 3 ^ 40 * 8121244 * 2
def baseEnd_8121244 : Nat := 4170101684442528829201085

theorem tailTrace_8121244 : CollatzResearch.WordTrace tailWord_8121244 prefixEnd_8121244 4170101684442528829201085 := by
  unfold tailWord_8121244
  simp only [CollatzResearch.WordTrace]
  refine ⟨148103051495063730447877393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197470735326751640597169857 148103051495063730447877393)
  ·
    refine ⟨111077288621297797835908045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148103051495063730447877393 111077288621297797835908045)
    ·
      refine ⟨41653983232986674188465517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111077288621297797835908045 41653983232986674188465517)
      ·
        refine ⟨15620243712370002820674569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41653983232986674188465517 15620243712370002820674569)
        ·
          refine ⟨11715182784277502115505927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15620243712370002820674569 11715182784277502115505927)
          ·
            refine ⟨17572774176416253173258891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11715182784277502115505927 17572774176416253173258891)
            ·
              refine ⟨26359161264624379759888337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17572774176416253173258891 26359161264624379759888337)
              ·
                refine ⟨19769370948468284819916253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26359161264624379759888337 19769370948468284819916253)
                ·
                  refine ⟨7413514105675606807468595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19769370948468284819916253 7413514105675606807468595)
                  ·
                    refine ⟨11120271158513410211202893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7413514105675606807468595 11120271158513410211202893)
                    ·
                      refine ⟨4170101684442528829201085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11120271158513410211202893 4170101684442528829201085)
                      ·
                        rfl

theorem cell23_8121244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_8121244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121244 prefixEnd_8121244 := by exact prefixLift 8121244
  have htrace : WordTrace (prefixWord ++ tailWord_8121244) baseStart_8121244 baseEnd_8121244 := by
    simpa [prefixWord, tailWord_8121244, baseEnd_8121244] using wordTrace_append hprefix tailTrace_8121244
  have hstable : (prefixWord ++ tailWord_8121244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121244).length < 2 ^ (prefixWord ++ tailWord_8121244).sum := by decide
  have hdescent : baseEnd_8121244 < baseStart_8121244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121263 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 4]
def baseStart_8121263 : Nat := 118140960795 + 8121263 * 2 ^ 59
def prefixEnd_8121263 : Nat := 4983230072969 + 3 ^ 40 * 8121263 * 2
def baseEnd_8121263 : Nat := 4170111440574964254863497

theorem tailTrace_8121263 : CollatzResearch.WordTrace tailWord_8121263 prefixEnd_8121263 4170111440574964254863497 := by
  unfold tailWord_8121263
  simp only [CollatzResearch.WordTrace]
  refine ⟨296206795977058627140696443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197471197318039084760464295 296206795977058627140696443)
  ·
    refine ⟨444310193965587940711044665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296206795977058627140696443 444310193965587940711044665)
    ·
      refine ⟨333232645474190955533283499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444310193965587940711044665 333232645474190955533283499)
      ·
        refine ⟨499848968211286433299925249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333232645474190955533283499 499848968211286433299925249)
        ·
          refine ⟨374886726158464824974943937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499848968211286433299925249 374886726158464824974943937)
          ·
            refine ⟨281165044618848618731207953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374886726158464824974943937 281165044618848618731207953)
            ·
              refine ⟨210873783464136464048405965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281165044618848618731207953 210873783464136464048405965)
              ·
                refine ⟨79077668799051174018152237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210873783464136464048405965 79077668799051174018152237)
                ·
                  refine ⟨29654125799644190256807089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79077668799051174018152237 29654125799644190256807089)
                  ·
                    refine ⟨22240594349733142692605317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29654125799644190256807089 22240594349733142692605317)
                    ·
                      refine ⟨4170111440574964254863497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22240594349733142692605317 4170111440574964254863497)
                      ·
                        rfl

theorem cell23_8121263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_8121263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121263 prefixEnd_8121263 := by exact prefixLift 8121263
  have htrace : WordTrace (prefixWord ++ tailWord_8121263) baseStart_8121263 baseEnd_8121263 := by
    simpa [prefixWord, tailWord_8121263, baseEnd_8121263] using wordTrace_append hprefix tailTrace_8121263
  have hstable : (prefixWord ++ tailWord_8121263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121263).length < 2 ^ (prefixWord ++ tailWord_8121263).sum := by decide
  have hdescent : baseEnd_8121263 < baseStart_8121263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121273 : List Nat := [1, 2, 1, 4, 2, 3, 10]
def baseStart_8121273 : Nat := 118140960795 + 8121273 * 2 ^ 59
def prefixEnd_8121273 : Nat := 4983230072969 + 3 ^ 40 * 8121273 * 2
def baseEnd_8121273 : Nat := 51482920683722335996771

theorem tailTrace_8121273 : CollatzResearch.WordTrace tailWord_8121273 prefixEnd_8121273 51482920683722335996771 := by
  unfold tailWord_8121273
  simp only [CollatzResearch.WordTrace]
  refine ⟨296207160707022398848560473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197471440471348265899040315 296207160707022398848560473)
  ·
    refine ⟨222155370530266799136420355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296207160707022398848560473 222155370530266799136420355)
    ·
      refine ⟨333233055795400198704630533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222155370530266799136420355 333233055795400198704630533)
      ·
        refine ⟨62481197961637537257118225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333233055795400198704630533 62481197961637537257118225)
        ·
          refine ⟨46860898471228152942838669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62481197961637537257118225 46860898471228152942838669)
          ·
            refine ⟨17572836926710557353564501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46860898471228152942838669 17572836926710557353564501)
            ·
              refine ⟨51482920683722335996771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17572836926710557353564501 51482920683722335996771)
              ·
                rfl

theorem cell23_8121273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 10].length) (baseStart_8121273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121273 prefixEnd_8121273 := by exact prefixLift 8121273
  have htrace : WordTrace (prefixWord ++ tailWord_8121273) baseStart_8121273 baseEnd_8121273 := by
    simpa [prefixWord, tailWord_8121273, baseEnd_8121273] using wordTrace_append hprefix tailTrace_8121273
  have hstable : (prefixWord ++ tailWord_8121273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121273).length < 2 ^ (prefixWord ++ tailWord_8121273).sum := by decide
  have hdescent : baseEnd_8121273 < baseStart_8121273 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121277 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 4, 4]
def baseStart_8121277 : Nat := 118140960795 + 8121277 * 2 ^ 59
def prefixEnd_8121277 : Nat := 4983230072969 + 3 ^ 40 * 8121277 * 2
def baseEnd_8121277 : Nat := 1390039543101375733362811

theorem tailTrace_8121277 : CollatzResearch.WordTrace tailWord_8121277 prefixEnd_8121277 1390039543101375733362811 := by
  unfold tailWord_8121277
  simp only [CollatzResearch.WordTrace]
  refine ⟨296207306599007907531706085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197471537732671938354470723 296207306599007907531706085)
  ·
    refine ⟨55538869987313982662194891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296207306599007907531706085 55538869987313982662194891)
    ·
      refine ⟨83308304980970973993292337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55538869987313982662194891 83308304980970973993292337)
      ·
        refine ⟨62481228735728230494969253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83308304980970973993292337 62481228735728230494969253)
        ·
          refine ⟨11715230387949043217806735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62481228735728230494969253 11715230387949043217806735)
          ·
            refine ⟨17572845581923564826710103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11715230387949043217806735 17572845581923564826710103)
            ·
              refine ⟨26359268372885347240065155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17572845581923564826710103 26359268372885347240065155)
              ·
                refine ⟨39538902559328020860097733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26359268372885347240065155 39538902559328020860097733)
                ·
                  refine ⟨7413544229874003911268325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39538902559328020860097733 7413544229874003911268325)
                  ·
                    refine ⟨1390039543101375733362811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7413544229874003911268325 1390039543101375733362811)
                    ·
                      rfl

theorem cell23_8121277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_8121277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121277 prefixEnd_8121277 := by exact prefixLift 8121277
  have htrace : WordTrace (prefixWord ++ tailWord_8121277) baseStart_8121277 baseEnd_8121277 := by
    simpa [prefixWord, tailWord_8121277, baseEnd_8121277] using wordTrace_append hprefix tailTrace_8121277
  have hstable : (prefixWord ++ tailWord_8121277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121277).length < 2 ^ (prefixWord ++ tailWord_8121277).sum := by decide
  have hdescent : baseEnd_8121277 < baseStart_8121277 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121294 : List Nat := [4, 1, 1, 1, 2, 4, 3, 1, 2, 4]
def baseStart_8121294 : Nat := 118140960795 + 8121294 * 2 ^ 59
def prefixEnd_8121294 : Nat := 4983230072969 + 3 ^ 40 * 8121294 * 2
def baseEnd_8121294 : Nat := 1390042452825084544525285

theorem tailTrace_8121294 : CollatzResearch.WordTrace tailWord_8121294 prefixEnd_8121294 1390042452825084544525285 := by
  unfold tailWord_8121294
  simp only [CollatzResearch.WordTrace]
  refine ⟨37025990829993289929384367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197471951093297546290049957 37025990829993289929384367)
  ·
    refine ⟨55538986244989934894076551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37025990829993289929384367 55538986244989934894076551)
    ·
      refine ⟨83308479367484902341114827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55538986244989934894076551 83308479367484902341114827)
      ·
        refine ⟨124962719051227353511672241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83308479367484902341114827 124962719051227353511672241)
        ·
          refine ⟨93722039288420515133754181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124962719051227353511672241 93722039288420515133754181)
          ·
            refine ⟨17572882366578846587578909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93722039288420515133754181 17572882366578846587578909)
            ·
              refine ⟨6589830887467067470342091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17572882366578846587578909 6589830887467067470342091)
              ·
                refine ⟨9884746331200601205513137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6589830887467067470342091 9884746331200601205513137)
                ·
                  refine ⟨7413559748400450904134853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9884746331200601205513137 7413559748400450904134853)
                  ·
                    refine ⟨1390042452825084544525285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7413559748400450904134853 1390042452825084544525285)
                    ·
                      rfl

theorem cell23_8121294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_8121294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121294 prefixEnd_8121294 := by exact prefixLift 8121294
  have htrace : WordTrace (prefixWord ++ tailWord_8121294) baseStart_8121294 baseEnd_8121294 := by
    simpa [prefixWord, tailWord_8121294, baseEnd_8121294] using wordTrace_append hprefix tailTrace_8121294
  have hstable : (prefixWord ++ tailWord_8121294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121294).length < 2 ^ (prefixWord ++ tailWord_8121294).sum := by decide
  have hdescent : baseEnd_8121294 < baseStart_8121294 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121323 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 4]
def baseStart_8121323 : Nat := 118140960795 + 8121323 * 2 ^ 59
def prefixEnd_8121323 : Nat := 4983230072969 + 3 ^ 40 * 8121323 * 2
def baseEnd_8121323 : Nat := 4170142249414234020113221

theorem tailTrace_8121323 : CollatzResearch.WordTrace tailWord_8121323 prefixEnd_8121323 4170142249414234020113221 := by
  unfold tailWord_8121323
  simp only [CollatzResearch.WordTrace]
  refine ⟨296208984356841257387880623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197472656237894171591920415 296208984356841257387880623)
  ·
    refine ⟨444313476535261886081820935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296208984356841257387880623 444313476535261886081820935)
    ·
      refine ⟨666470214802892829122731403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444313476535261886081820935 666470214802892829122731403)
      ·
        refine ⟨999705322204339243684097105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666470214802892829122731403 999705322204339243684097105)
        ·
          refine ⟨749778991653254432763072829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 999705322204339243684097105 749778991653254432763072829)
          ·
            refine ⟨281167121869970412286152311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 749778991653254432763072829 281167121869970412286152311)
            ·
              refine ⟨421750682804955618429228467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281167121869970412286152311 421750682804955618429228467)
              ·
                refine ⟨632626024207433427643842701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421750682804955618429228467 632626024207433427643842701)
                ·
                  refine ⟨237234759077787535366441013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632626024207433427643842701 237234759077787535366441013)
                  ·
                    refine ⟨22240758663542581440603845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 237234759077787535366441013 22240758663542581440603845)
                    ·
                      refine ⟨4170142249414234020113221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22240758663542581440603845 4170142249414234020113221)
                      ·
                        rfl

theorem cell23_8121323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 4].length) (baseStart_8121323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121323 prefixEnd_8121323 := by exact prefixLift 8121323
  have htrace : WordTrace (prefixWord ++ tailWord_8121323) baseStart_8121323 baseEnd_8121323 := by
    simpa [prefixWord, tailWord_8121323, baseEnd_8121323] using wordTrace_append hprefix tailTrace_8121323
  have hstable : (prefixWord ++ tailWord_8121323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121323).length < 2 ^ (prefixWord ++ tailWord_8121323).sum := by decide
  have hdescent : baseEnd_8121323 < baseStart_8121323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121334 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_8121334 : Nat := 118140960795 + 8121334 * 2 ^ 59
def prefixEnd_8121334 : Nat := 4983230072969 + 3 ^ 40 * 8121334 * 2
def baseEnd_8121334 : Nat := 4170147897701433477075671

theorem tailTrace_8121334 : CollatzResearch.WordTrace tailWord_8121334 prefixEnd_8121334 4170147897701433477075671 := by
  unfold tailWord_8121334
  simp only [CollatzResearch.WordTrace]
  refine ⟨18513086597487587891658191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197472923706534270844354037 18513086597487587891658191)
  ·
    refine ⟨27769629896231381837487287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18513086597487587891658191 27769629896231381837487287)
    ·
      refine ⟨41654444844347072756230931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27769629896231381837487287 41654444844347072756230931)
      ·
        refine ⟨62481667266520609134346397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41654444844347072756230931 62481667266520609134346397)
        ·
          refine ⟨23430625224945228425379899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62481667266520609134346397 23430625224945228425379899)
          ·
            refine ⟨35145937837417842638069849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23430625224945228425379899 35145937837417842638069849)
            ·
              refine ⟨26359453378063381978552387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35145937837417842638069849 26359453378063381978552387)
              ·
                refine ⟨39539180067095072967828581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26359453378063381978552387 39539180067095072967828581)
                ·
                  refine ⟨7413596262580326181467859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39539180067095072967828581 7413596262580326181467859)
                  ·
                    refine ⟨11120394393870489272201789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7413596262580326181467859 11120394393870489272201789)
                    ·
                      refine ⟨4170147897701433477075671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11120394393870489272201789 4170147897701433477075671)
                      ·
                        rfl

theorem cell23_8121334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_8121334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121334 prefixEnd_8121334 := by exact prefixLift 8121334
  have htrace : WordTrace (prefixWord ++ tailWord_8121334) baseStart_8121334 baseEnd_8121334 := by
    simpa [prefixWord, tailWord_8121334, baseEnd_8121334] using wordTrace_append hprefix tailTrace_8121334
  have hstable : (prefixWord ++ tailWord_8121334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121334).length < 2 ^ (prefixWord ++ tailWord_8121334).sum := by decide
  have hdescent : baseEnd_8121334 < baseStart_8121334 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121353 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 2, 3, 6]
def baseStart_8121353 : Nat := 118140960795 + 8121353 * 2 ^ 59
def prefixEnd_8121353 : Nat := 4983230072969 + 3 ^ 40 * 8121353 * 2
def baseEnd_8121353 : Nat := 4170157653833868902738083

theorem tailTrace_8121353 : CollatzResearch.WordTrace tailWord_8121353 prefixEnd_8121353 4170157653833868902738083 := by
  unfold tailWord_8121353
  simp only [CollatzResearch.WordTrace]
  refine ⟨296210078546732572511472713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197473385697821715007648475 296210078546732572511472713)
  ·
    refine ⟨222157558910049429383604535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296210078546732572511472713 222157558910049429383604535)
    ·
      refine ⟨333236338365074144075406803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222157558910049429383604535 333236338365074144075406803)
      ·
        refine ⟨499854507547611216113110205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333236338365074144075406803 499854507547611216113110205)
        ·
          refine ⟨187445440330354206042416327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 499854507547611216113110205 187445440330354206042416327)
          ·
            refine ⟨281168160495531309063624491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187445440330354206042416327 281168160495531309063624491)
            ·
              refine ⟨421752240743296963595436737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281168160495531309063624491 421752240743296963595436737)
              ·
                refine ⟨316314180557472722696577553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421752240743296963595436737 316314180557472722696577553)
                ·
                  refine ⟨237235635418104542022433165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316314180557472722696577553 237235635418104542022433165)
                  ·
                    refine ⟨88963363281789203258412437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237235635418104542022433165 88963363281789203258412437)
                    ·
                      refine ⟨4170157653833868902738083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88963363281789203258412437 4170157653833868902738083)
                      ·
                        rfl

theorem cell23_8121353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_8121353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121353 prefixEnd_8121353 := by exact prefixLift 8121353
  have htrace : WordTrace (prefixWord ++ tailWord_8121353) baseStart_8121353 baseEnd_8121353 := by
    simpa [prefixWord, tailWord_8121353, baseEnd_8121353] using wordTrace_append hprefix tailTrace_8121353
  have hstable : (prefixWord ++ tailWord_8121353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121353).length < 2 ^ (prefixWord ++ tailWord_8121353).sum := by decide
  have hdescent : baseEnd_8121353 < baseStart_8121353 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121363 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 9]
def baseStart_8121363 : Nat := 118140960795 + 8121363 * 2 ^ 59
def prefixEnd_8121363 : Nat := 4983230072969 + 3 ^ 40 * 8121363 * 2
def baseEnd_8121363 : Nat := 463351420960045984845893

theorem tailTrace_8121363 : CollatzResearch.WordTrace tailWord_8121363 prefixEnd_8121363 463351420960045984845893 := by
  unfold tailWord_8121363
  simp only [CollatzResearch.WordTrace]
  refine ⟨296210443276696344219336743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197473628851130896146224495 296210443276696344219336743)
  ·
    refine ⟨444315664915044516329005115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296210443276696344219336743 444315664915044516329005115)
    ·
      refine ⟨666473497372566774493507673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444315664915044516329005115 666473497372566774493507673)
      ·
        refine ⟨499855123029425080870130755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666473497372566774493507673 499855123029425080870130755)
        ·
          refine ⟨749782684544137621305196133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499855123029425080870130755 749782684544137621305196133)
          ·
            refine ⟨140584253352025803994724275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 749782684544137621305196133 140584253352025803994724275)
            ·
              refine ⟨210876380028038705992086413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140584253352025803994724275 210876380028038705992086413)
              ·
                refine ⟨79078642510514514747032405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210876380028038705992086413 79078642510514514747032405)
                ·
                  refine ⟨463351420960045984845893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79078642510514514747032405 463351420960045984845893)
                  ·
                    rfl

theorem cell23_8121363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 9].length) (baseStart_8121363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121363 prefixEnd_8121363 := by exact prefixLift 8121363
  have htrace : WordTrace (prefixWord ++ tailWord_8121363) baseStart_8121363 baseEnd_8121363 := by
    simpa [prefixWord, tailWord_8121363, baseEnd_8121363] using wordTrace_append hprefix tailTrace_8121363
  have hstable : (prefixWord ++ tailWord_8121363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121363).length < 2 ^ (prefixWord ++ tailWord_8121363).sum := by decide
  have hdescent : baseEnd_8121363 < baseStart_8121363 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121414 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_8121414 : Nat := 118140960795 + 8121414 * 2 ^ 59
def prefixEnd_8121414 : Nat := 4983230072969 + 3 ^ 40 * 8121414 * 2
def baseEnd_8121414 : Nat := 463354330683754796008367

theorem tailTrace_8121414 : CollatzResearch.WordTrace tailWord_8121414 prefixEnd_8121414 463354330683754796008367 := by
  unfold tailWord_8121414
  simp only [CollatzResearch.WordTrace]
  refine ⟨9256634481234736872795103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 197474868933007719952962197 9256634481234736872795103)
  ·
    refine ⟨13884951721852105309192655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9256634481234736872795103 13884951721852105309192655)
    ·
      refine ⟨20827427582778157963788983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13884951721852105309192655 20827427582778157963788983)
      ·
        refine ⟨31241141374167236945683475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20827427582778157963788983 31241141374167236945683475)
        ·
          refine ⟨46861712061250855418525213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31241141374167236945683475 46861712061250855418525213)
          ·
            refine ⟨17573142022969070781946955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46861712061250855418525213 17573142022969070781946955)
            ·
              refine ⟨26359713034453606172920433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17573142022969070781946955 26359713034453606172920433)
              ·
                refine ⟨19769784775840204629690325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26359713034453606172920433 19769784775840204629690325)
                ·
                  refine ⟨463354330683754796008367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19769784775840204629690325 463354330683754796008367)
                  ·
                    rfl

theorem cell23_8121414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_8121414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121414 prefixEnd_8121414 := by exact prefixLift 8121414
  have htrace : WordTrace (prefixWord ++ tailWord_8121414) baseStart_8121414 baseEnd_8121414 := by
    simpa [prefixWord, tailWord_8121414, baseEnd_8121414] using wordTrace_append hprefix tailTrace_8121414
  have hstable : (prefixWord ++ tailWord_8121414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121414).length < 2 ^ (prefixWord ++ tailWord_8121414).sum := by decide
  have hdescent : baseEnd_8121414 < baseStart_8121414 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121508 : List Nat := [2, 3, 1, 2, 3, 2, 3, 2, 1, 4]
def baseStart_8121508 : Nat := 118140960795 + 8121508 * 2 ^ 59
def prefixEnd_8121508 : Nat := 4983230072969 + 3 ^ 40 * 8121508 * 2
def baseEnd_8121508 : Nat := 1390079081111771932099957

theorem tailTrace_8121508 : CollatzResearch.WordTrace tailWord_8121508 prefixEnd_8121508 1390079081111771932099957 := by
  unfold tailWord_8121508
  simp only [CollatzResearch.WordTrace]
  refine ⟨148107865930585516991682589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197477154574114022655576785 148107865930585516991682589)
  ·
    refine ⟨55540449723969568871880971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148107865930585516991682589 55540449723969568871880971)
    ·
      refine ⟨83310674585954353307821457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55540449723969568871880971 83310674585954353307821457)
      ·
        refine ⟨62483005939465764980866093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83310674585954353307821457 62483005939465764980866093)
        ·
          refine ⟨23431127227299661867824785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62483005939465764980866093 23431127227299661867824785)
          ·
            refine ⟨17573345420474746400868589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23431127227299661867824785 17573345420474746400868589)
            ·
              refine ⟨6590004532678029900325721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17573345420474746400868589 6590004532678029900325721)
              ·
                refine ⟨4942503399508522425244291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6590004532678029900325721 4942503399508522425244291)
                ·
                  refine ⟨7413755099262783637866437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4942503399508522425244291 7413755099262783637866437)
                  ·
                    refine ⟨1390079081111771932099957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7413755099262783637866437 1390079081111771932099957)
                    ·
                      rfl

theorem cell23_8121508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_8121508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121508 prefixEnd_8121508 := by exact prefixLift 8121508
  have htrace : WordTrace (prefixWord ++ tailWord_8121508) baseStart_8121508 baseEnd_8121508 := by
    simpa [prefixWord, tailWord_8121508, baseEnd_8121508] using wordTrace_append hprefix tailTrace_8121508
  have hstable : (prefixWord ++ tailWord_8121508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121508).length < 2 ^ (prefixWord ++ tailWord_8121508).sum := by decide
  have hdescent : baseEnd_8121508 < baseStart_8121508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121521 : List Nat := [1, 2, 2, 5, 1, 3, 2, 1, 6]
def baseStart_8121521 : Nat := 118140960795 + 8121521 * 2 ^ 59
def prefixEnd_8121521 : Nat := 4983230072969 + 3 ^ 40 * 8121521 * 2
def baseEnd_8121521 : Nat := 463360435398202693937479

theorem tailTrace_8121521 : CollatzResearch.WordTrace tailWord_8121521 prefixEnd_8121521 463360435398202693937479 := by
  unfold tailWord_8121521
  simp only [CollatzResearch.WordTrace]
  refine ⟨296216206010123937203588417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197477470673415958135725611 296216206010123937203588417)
  ·
    refine ⟨222162154507592952902691313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296216206010123937203588417 222162154507592952902691313)
    ·
      refine ⟨166621615880694714677018485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222162154507592952902691313 166621615880694714677018485)
      ·
        refine ⟨15620776488815129500970483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166621615880694714677018485 15620776488815129500970483)
        ·
          refine ⟨23431164733222694251455725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15620776488815129500970483 23431164733222694251455725)
          ·
            refine ⟨8786686774958510344295897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23431164733222694251455725 8786686774958510344295897)
            ·
              refine ⟨6590015081218882758221923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8786686774958510344295897 6590015081218882758221923)
              ·
                refine ⟨9885022621828324137332885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6590015081218882758221923 9885022621828324137332885)
                ·
                  refine ⟨463360435398202693937479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9885022621828324137332885 463360435398202693937479)
                  ·
                    rfl

theorem cell23_8121521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 6].length) (baseStart_8121521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121521 prefixEnd_8121521 := by exact prefixLift 8121521
  have htrace : WordTrace (prefixWord ++ tailWord_8121521) baseStart_8121521 baseEnd_8121521 := by
    simpa [prefixWord, tailWord_8121521, baseEnd_8121521] using wordTrace_append hprefix tailTrace_8121521
  have hstable : (prefixWord ++ tailWord_8121521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121521).length < 2 ^ (prefixWord ++ tailWord_8121521).sum := by decide
  have hdescent : baseEnd_8121521 < baseStart_8121521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121534 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_8121534 : Nat := 118140960795 + 8121534 * 2 ^ 59
def prefixEnd_8121534 : Nat := 4983230072969 + 3 ^ 40 * 8121534 * 2
def baseEnd_8121534 : Nat := 1390083531277444231524917

theorem tailTrace_8121534 : CollatzResearch.WordTrace tailWord_8121534 prefixEnd_8121534 1390083531277444231524917 := by
  unfold tailWord_8121534
  simp only [CollatzResearch.WordTrace]
  refine ⟨37027085019884605052976457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197477786772717893615874437 37027085019884605052976457)
  ·
    refine ⟨27770313764913453789732343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37027085019884605052976457 27770313764913453789732343)
    ·
      refine ⟨41655470647370180684598515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27770313764913453789732343 41655470647370180684598515)
      ·
        refine ⟨62483205971055271026897773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41655470647370180684598515 62483205971055271026897773)
        ·
          refine ⟨23431202239145726635086665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62483205971055271026897773 23431202239145726635086665)
          ·
            refine ⟨17573401679359294976314999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23431202239145726635086665 17573401679359294976314999)
            ·
              refine ⟨26360102519038942464472499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17573401679359294976314999 26360102519038942464472499)
              ·
                refine ⟨39540153778558413696708749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26360102519038942464472499 39540153778558413696708749)
                ·
                  refine ⟨14827557666959405136265781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39540153778558413696708749 14827557666959405136265781)
                  ·
                    refine ⟨1390083531277444231524917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14827557666959405136265781 1390083531277444231524917)
                    ·
                      rfl

theorem cell23_8121534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_8121534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121534 prefixEnd_8121534 := by exact prefixLift 8121534
  have htrace : WordTrace (prefixWord ++ tailWord_8121534) baseStart_8121534 baseEnd_8121534 := by
    simpa [prefixWord, tailWord_8121534, baseEnd_8121534] using wordTrace_append hprefix tailTrace_8121534
  have hstable : (prefixWord ++ tailWord_8121534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121534).length < 2 ^ (prefixWord ++ tailWord_8121534).sum := by decide
  have hdescent : baseEnd_8121534 < baseStart_8121534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121547 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 4, 4]
def baseStart_8121547 : Nat := 118140960795 + 8121547 * 2 ^ 59
def prefixEnd_8121547 : Nat := 4983230072969 + 3 ^ 40 * 8121547 * 2
def baseEnd_8121547 : Nat := 1390085756360280381237397

theorem tailTrace_8121547 : CollatzResearch.WordTrace tailWord_8121547 prefixEnd_8121547 1390085756360280381237397 := by
  unfold tailWord_8121547
  simp only [CollatzResearch.WordTrace]
  refine ⟨296217154308029743644034895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197478102872019829096023263 296217154308029743644034895)
  ·
    refine ⟨444325731462044615466052343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296217154308029743644034895 444325731462044615466052343)
    ·
      refine ⟨666488597193066923199078515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444325731462044615466052343 666488597193066923199078515)
      ·
        refine ⟨999732895789600384798617773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666488597193066923199078515 999732895789600384798617773)
        ·
          refine ⟨374899835921100144299481665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 999732895789600384798617773 374899835921100144299481665)
          ·
            refine ⟨281174876940825108224611249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374899835921100144299481665 281174876940825108224611249)
            ·
              refine ⟨210881157705618831168458437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281174876940825108224611249 210881157705618831168458437)
              ·
                refine ⟨39540217069803530844085957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210881157705618831168458437 39540217069803530844085957)
                ·
                  refine ⟨7413790700588162033266117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39540217069803530844085957 7413790700588162033266117)
                  ·
                    refine ⟨1390085756360280381237397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7413790700588162033266117 1390085756360280381237397)
                    ·
                      rfl

theorem cell23_8121547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 4].length) (baseStart_8121547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121547 prefixEnd_8121547 := by exact prefixLift 8121547
  have htrace : WordTrace (prefixWord ++ tailWord_8121547) baseStart_8121547 baseEnd_8121547 := by
    simpa [prefixWord, tailWord_8121547, baseEnd_8121547] using wordTrace_append hprefix tailTrace_8121547
  have hstable : (prefixWord ++ tailWord_8121547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121547).length < 2 ^ (prefixWord ++ tailWord_8121547).sum := by decide
  have hdescent : baseEnd_8121547 < baseStart_8121547 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121560 : List Nat := [2, 1, 2, 2, 16]
def baseStart_8121560 : Nat := 118140960795 + 8121560 * 2 ^ 59
def prefixEnd_8121560 : Nat := 4983230072969 + 3 ^ 40 * 8121560 * 2
def baseEnd_8121560 : Nat := 5720526672605417822839

theorem tailTrace_8121560 : CollatzResearch.WordTrace tailWord_8121560 prefixEnd_8121560 5720526672605417822839 := by
  unfold tailWord_8121560
  simp only [CollatzResearch.WordTrace]
  refine ⟨148108814228491323432129067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197478418971321764576172089 148108814228491323432129067)
  ·
    refine ⟨222163221342736985148193601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148108814228491323432129067 222163221342736985148193601)
    ·
      refine ⟨166622416007052738861145201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222163221342736985148193601 166622416007052738861145201)
      ·
        refine ⟨124966812005289554145858901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166622416007052738861145201 124966812005289554145858901)
        ·
          refine ⟨5720526672605417822839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 124966812005289554145858901 5720526672605417822839)
          ·
            rfl

theorem cell23_8121560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 16].length) (baseStart_8121560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121560 prefixEnd_8121560 := by exact prefixLift 8121560
  have htrace : WordTrace (prefixWord ++ tailWord_8121560) baseStart_8121560 baseEnd_8121560 := by
    simpa [prefixWord, tailWord_8121560, baseEnd_8121560] using wordTrace_append hprefix tailTrace_8121560
  have hstable : (prefixWord ++ tailWord_8121560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121560).length < 2 ^ (prefixWord ++ tailWord_8121560).sum := by decide
  have hdescent : baseEnd_8121560 < baseStart_8121560 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121565 : List Nat := [1, 4, 3, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_8121565 : Nat := 118140960795 + 8121565 * 2 ^ 59
def prefixEnd_8121565 : Nat := 4983230072969 + 3 ^ 40 * 8121565 * 2
def baseEnd_8121565 : Nat := 4170266511732622073287109

theorem tailTrace_8121565 : CollatzResearch.WordTrace tailWord_8121565 prefixEnd_8121565 4170266511732622073287109 := by
  unfold tailWord_8121565
  simp only [CollatzResearch.WordTrace]
  refine ⟨296217810821964532718190149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197478540547976355145460099 296217810821964532718190149)
  ·
    refine ⟨55540839529118349884660653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296217810821964532718190149 55540839529118349884660653)
    ·
      refine ⟨20827814823419381206747745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55540839529118349884660653 20827814823419381206747745)
      ·
        refine ⟨15620861117564535905060809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20827814823419381206747745 15620861117564535905060809)
        ·
          refine ⟨11715645838173401928795607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15620861117564535905060809 11715645838173401928795607)
          ·
            refine ⟨17573468757260102893193411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11715645838173401928795607 17573468757260102893193411)
            ·
              refine ⟨26360203135890154339790117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17573468757260102893193411 26360203135890154339790117)
              ·
                refine ⟨4942538087979403938710647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26360203135890154339790117 4942538087979403938710647)
                ·
                  refine ⟨7413807131969105908065971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4942538087979403938710647 7413807131969105908065971)
                  ·
                    refine ⟨11120710697953658862098957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7413807131969105908065971 11120710697953658862098957)
                    ·
                      refine ⟨4170266511732622073287109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11120710697953658862098957 4170266511732622073287109)
                      ·
                        rfl

theorem cell23_8121565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_8121565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121565 prefixEnd_8121565 := by exact prefixLift 8121565
  have htrace : WordTrace (prefixWord ++ tailWord_8121565) baseStart_8121565 baseEnd_8121565 := by
    simpa [prefixWord, tailWord_8121565, baseEnd_8121565] using wordTrace_append hprefix tailTrace_8121565
  have hstable : (prefixWord ++ tailWord_8121565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121565).length < 2 ^ (prefixWord ++ tailWord_8121565).sum := by decide
  have hdescent : baseEnd_8121565 < baseStart_8121565 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121581 : List Nat := [1, 5, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_8121581 : Nat := 118140960795 + 8121581 * 2 ^ 59
def prefixEnd_8121581 : Nat := 4983230072969 + 3 ^ 40 * 8121581 * 2
def baseEnd_8121581 : Nat := 1390091575807698003562345

theorem tailTrace_8121581 : CollatzResearch.WordTrace tailWord_8121581 prefixEnd_8121581 1390091575807698003562345 := by
  unfold tailWord_8121581
  simp only [CollatzResearch.WordTrace]
  refine ⟨296218394389906567450772597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197478929593271044967181731 296218394389906567450772597)
  ·
    refine ⟨27770474474053740698509931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 296218394389906567450772597 27770474474053740698509931)
    ·
      refine ⟨41655711711080611047764897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27770474474053740698509931 41655711711080611047764897)
      ·
        refine ⟨31241783783310458285823673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41655711711080611047764897 31241783783310458285823673)
        ·
          refine ⟨23431337837482843714367755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31241783783310458285823673 23431337837482843714367755)
          ·
            refine ⟨35147006756224265571551633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23431337837482843714367755 35147006756224265571551633)
            ·
              refine ⟨26360255067168199178663725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35147006756224265571551633 26360255067168199178663725)
              ·
                refine ⟨9885095650188074691998897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26360255067168199178663725 9885095650188074691998897)
                ·
                  refine ⟨7413821737641056018999173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9885095650188074691998897 7413821737641056018999173)
                  ·
                    refine ⟨1390091575807698003562345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7413821737641056018999173 1390091575807698003562345)
                    ·
                      rfl

theorem cell23_8121581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_8121581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121581 prefixEnd_8121581 := by exact prefixLift 8121581
  have htrace : WordTrace (prefixWord ++ tailWord_8121581) baseStart_8121581 baseEnd_8121581 := by
    simpa [prefixWord, tailWord_8121581, baseEnd_8121581] using wordTrace_append hprefix tailTrace_8121581
  have hstable : (prefixWord ++ tailWord_8121581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121581).length < 2 ^ (prefixWord ++ tailWord_8121581).sum := by decide
  have hdescent : baseEnd_8121581 < baseStart_8121581 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121647 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 5]
def baseStart_8121647 : Nat := 118140960795 + 8121647 * 2 ^ 59
def prefixEnd_8121647 : Nat := 4983230072969 + 3 ^ 40 * 8121647 * 2
def baseEnd_8121647 : Nat := 4170308617146290752461731

theorem tailTrace_8121647 : CollatzResearch.WordTrace tailWord_8121647 prefixEnd_8121647 4170308617146290752461731 := by
  unfold tailWord_8121647
  simp only [CollatzResearch.WordTrace]
  refine ⟨296220801607667460722675195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197480534405111640481783463 296220801607667460722675195)
  ·
    refine ⟨444331202411501191084012793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296220801607667460722675195 444331202411501191084012793)
    ·
      refine ⟨333248401808625893313009595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444331202411501191084012793 333248401808625893313009595)
      ·
        refine ⟨499872602712938839969514393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333248401808625893313009595 499872602712938839969514393)
        ·
          refine ⟨374904452034704129977135795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499872602712938839969514393 374904452034704129977135795)
          ·
            refine ⟨562356678052056194965703693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374904452034704129977135795 562356678052056194965703693)
            ·
              refine ⟨210883754269521073112138885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 562356678052056194965703693 210883754269521073112138885)
              ·
                refine ⟨39540703925535201208526041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210883754269521073112138885 39540703925535201208526041)
                ·
                  refine ⟨29655527944151400906394531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39540703925535201208526041 29655527944151400906394531)
                  ·
                    refine ⟨44483291916227101359591797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29655527944151400906394531 44483291916227101359591797)
                    ·
                      refine ⟨4170308617146290752461731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44483291916227101359591797 4170308617146290752461731)
                      ·
                        rfl

theorem cell23_8121647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_8121647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121647 prefixEnd_8121647 := by exact prefixLift 8121647
  have htrace : WordTrace (prefixWord ++ tailWord_8121647) baseStart_8121647 baseEnd_8121647 := by
    simpa [prefixWord, tailWord_8121647, baseEnd_8121647] using wordTrace_append hprefix tailTrace_8121647
  have hstable : (prefixWord ++ tailWord_8121647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121647).length < 2 ^ (prefixWord ++ tailWord_8121647).sum := by decide
  have hdescent : baseEnd_8121647 < baseStart_8121647 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121678 : List Nat := [4, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2]
def baseStart_8121678 : Nat := 118140960795 + 8121678 * 2 ^ 59
def prefixEnd_8121678 : Nat := 4983230072969 + 3 ^ 40 * 8121678 * 2
def baseEnd_8121678 : Nat := 4170324535046580131174089

theorem tailTrace_8121678 : CollatzResearch.WordTrace tailWord_8121678 prefixEnd_8121678 4170324535046580131174089 := by
  unfold tailWord_8121678
  simp only [CollatzResearch.WordTrace]
  refine ⟨37027741533819394127131711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197481288180370102011369125 37027741533819394127131711)
  ·
    refine ⟨55541612300729091190697567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37027741533819394127131711 55541612300729091190697567)
    ·
      refine ⟨83312418451093636786046351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55541612300729091190697567 83312418451093636786046351)
      ·
        refine ⟨124968627676640455179069527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83312418451093636786046351 124968627676640455179069527)
        ·
          refine ⟨187452941514960682768604291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124968627676640455179069527 187452941514960682768604291)
          ·
            refine ⟨281179412272441024152906437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187452941514960682768604291 281179412272441024152906437)
            ·
              refine ⟨52721139801082692028669957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281179412272441024152906437 52721139801082692028669957)
              ·
                refine ⟨9885213712703004755375617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52721139801082692028669957 9885213712703004755375617)
                ·
                  refine ⟨7413910284527253566531713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9885213712703004755375617 7413910284527253566531713)
                  ·
                    refine ⟨5560432713395440174898785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7413910284527253566531713 5560432713395440174898785)
                    ·
                      refine ⟨4170324535046580131174089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5560432713395440174898785 4170324535046580131174089)
                      ·
                        rfl

theorem cell23_8121678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_8121678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121678 prefixEnd_8121678 := by exact prefixLift 8121678
  have htrace : WordTrace (prefixWord ++ tailWord_8121678) baseStart_8121678 baseEnd_8121678 := by
    simpa [prefixWord, tailWord_8121678, baseEnd_8121678] using wordTrace_append hprefix tailTrace_8121678
  have hstable : (prefixWord ++ tailWord_8121678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121678).length < 2 ^ (prefixWord ++ tailWord_8121678).sum := by decide
  have hdescent : baseEnd_8121678 < baseStart_8121678 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121697 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 3, 7]
def baseStart_8121697 : Nat := 118140960795 + 8121697 * 2 ^ 59
def prefixEnd_8121697 : Nat := 4983230072969 + 3 ^ 40 * 8121697 * 2
def baseEnd_8121697 : Nat := 1390111430393005185612167

theorem tailTrace_8121697 : CollatzResearch.WordTrace tailWord_8121697 prefixEnd_8121697 1390111430393005185612167 := by
  unfold tailWord_8121697
  simp only [CollatzResearch.WordTrace]
  refine ⟨296222625257486319261995345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197481750171657546174663563 296222625257486319261995345)
  ·
    refine ⟨222166968943114739446496509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296222625257486319261995345 222166968943114739446496509)
    ·
      refine ⟨83312613353668027292436191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222166968943114739446496509 83312613353668027292436191)
      ·
        refine ⟨124968920030502040938654287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83312613353668027292436191 124968920030502040938654287)
        ·
          refine ⟨187453380045753061407981431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124968920030502040938654287 187453380045753061407981431)
          ·
            refine ⟨281180070068629592111972147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187453380045753061407981431 281180070068629592111972147)
            ·
              refine ⟨421770105102944388167958221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281180070068629592111972147 421770105102944388167958221)
              ·
                refine ⟨158163789413604145562984333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421770105102944388167958221 158163789413604145562984333)
                ·
                  refine ⟨59311421030101554586119125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158163789413604145562984333 59311421030101554586119125)
                  ·
                    refine ⟨1390111430393005185612167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59311421030101554586119125 1390111430393005185612167)
                    ·
                      rfl

theorem cell23_8121697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_8121697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121697 prefixEnd_8121697 := by exact prefixLift 8121697
  have htrace : WordTrace (prefixWord ++ tailWord_8121697) baseStart_8121697 baseEnd_8121697 := by
    simpa [prefixWord, tailWord_8121697, baseEnd_8121697] using wordTrace_append hprefix tailTrace_8121697
  have hstable : (prefixWord ++ tailWord_8121697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121697).length < 2 ^ (prefixWord ++ tailWord_8121697).sum := by decide
  have hdescent : baseEnd_8121697 < baseStart_8121697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121707 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 5]
def baseStart_8121707 : Nat := 118140960795 + 8121707 * 2 ^ 59
def prefixEnd_8121707 : Nat := 4983230072969 + 3 ^ 40 * 8121707 * 2
def baseEnd_8121707 : Nat := 4170339425985560517711455

theorem tailTrace_8121707 : CollatzResearch.WordTrace tailWord_8121707 prefixEnd_8121707 4170339425985560517711455 := by
  unfold tailWord_8121707
  simp only [CollatzResearch.WordTrace]
  refine ⟨296222989987450090969859375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197481993324966727313239583 296222989987450090969859375)
  ·
    refine ⟨444334484981175136454789063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296222989987450090969859375 444334484981175136454789063)
    ·
      refine ⟨666501727471762704682183595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444334484981175136454789063 666501727471762704682183595)
      ·
        refine ⟨999752591207644057023275393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666501727471762704682183595 999752591207644057023275393)
        ·
          refine ⟨749814443405733042767456545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 999752591207644057023275393 749814443405733042767456545)
          ·
            refine ⟨562360832554299782075592409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 749814443405733042767456545 562360832554299782075592409)
            ·
              refine ⟨421770624415724836556694307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562360832554299782075592409 421770624415724836556694307)
              ·
                refine ⟨632655936623587254835041461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421770624415724836556694307 632655936623587254835041461)
                ·
                  refine ⟨59311494058461305140785137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 632655936623587254835041461 59311494058461305140785137)
                  ·
                    refine ⟨44483620543845978855588853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59311494058461305140785137 44483620543845978855588853)
                    ·
                      refine ⟨4170339425985560517711455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44483620543845978855588853 4170339425985560517711455)
                      ·
                        rfl

theorem cell23_8121707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 5].length) (baseStart_8121707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121707 prefixEnd_8121707 := by exact prefixLift 8121707
  have htrace : WordTrace (prefixWord ++ tailWord_8121707) baseStart_8121707 baseEnd_8121707 := by
    simpa [prefixWord, tailWord_8121707, baseEnd_8121707] using wordTrace_append hprefix tailTrace_8121707
  have hstable : (prefixWord ++ tailWord_8121707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121707).length < 2 ^ (prefixWord ++ tailWord_8121707).sum := by decide
  have hdescent : baseEnd_8121707 < baseStart_8121707 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121768 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_8121768 : Nat := 118140960795 + 8121768 * 2 ^ 59
def prefixEnd_8121768 : Nat := 4983230072969 + 3 ^ 40 * 8121768 * 2
def baseEnd_8121768 : Nat := 4170370748305484779048675

theorem tailTrace_8121768 : CollatzResearch.WordTrace tailWord_8121768 prefixEnd_8121768 4170370748305484779048675 := by
  unfold tailWord_8121768
  simp only [CollatzResearch.WordTrace]
  refine ⟨148112607420114549193914979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197483476560152732258553305 148112607420114549193914979)
  ·
    refine ⟨222168911130171823790872469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148112607420114549193914979 222168911130171823790872469)
    ·
      refine ⟨10414167709226804240197147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 222168911130171823790872469 10414167709226804240197147)
      ·
        refine ⟨15621251563840206360295721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10414167709226804240197147 15621251563840206360295721)
        ·
          refine ⟨11715938672880154770221791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15621251563840206360295721 11715938672880154770221791)
          ·
            refine ⟨17573908009320232155332687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11715938672880154770221791 17573908009320232155332687)
            ·
              refine ⟨26360862013980348232999031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17573908009320232155332687 26360862013980348232999031)
              ·
                refine ⟨39541293020970522349498547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26360862013980348232999031 39541293020970522349498547)
                ·
                  refine ⟨59311939531455783524247821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39541293020970522349498547 59311939531455783524247821)
                  ·
                    refine ⟨22241977324295918821592933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59311939531455783524247821 22241977324295918821592933)
                    ·
                      refine ⟨4170370748305484779048675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22241977324295918821592933 4170370748305484779048675)
                      ·
                        rfl

theorem cell23_8121768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_8121768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121768 prefixEnd_8121768 := by exact prefixLift 8121768
  have htrace : WordTrace (prefixWord ++ tailWord_8121768) baseStart_8121768 baseEnd_8121768 := by
    simpa [prefixWord, tailWord_8121768, baseEnd_8121768] using wordTrace_append hprefix tailTrace_8121768
  have hstable : (prefixWord ++ tailWord_8121768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121768).length < 2 ^ (prefixWord ++ tailWord_8121768).sum := by decide
  have hdescent : baseEnd_8121768 < baseStart_8121768 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121818 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3]
def baseStart_8121818 : Nat := 118140960795 + 8121818 * 2 ^ 59
def prefixEnd_8121818 : Nat := 4983230072969 + 3 ^ 40 * 8121818 * 2
def baseEnd_8121818 : Nat := 4170396422338209583423445

theorem tailTrace_8121818 : CollatzResearch.WordTrace tailWord_8121818 prefixEnd_8121818 4170396422338209583423445 := by
  unfold tailWord_8121818
  simp only [CollatzResearch.WordTrace]
  refine ⟨74056759622511989231787527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197484692326698637951433405 74056759622511989231787527)
  ·
    refine ⟨111085139433767983847681291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74056759622511989231787527 111085139433767983847681291)
    ·
      refine ⟨166627709150651975771521937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111085139433767983847681291 166627709150651975771521937)
      ·
        refine ⟨124970781862988981828641453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166627709150651975771521937 124970781862988981828641453)
        ·
          refine ⟨46864043198620868185740545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124970781862988981828641453 46864043198620868185740545)
          ·
            refine ⟨35148032398965651139305409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46864043198620868185740545 35148032398965651139305409)
            ·
              refine ⟨26361024299224238354479057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35148032398965651139305409 26361024299224238354479057)
              ·
                refine ⟨19770768224418178765859293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26361024299224238354479057 19770768224418178765859293)
                ·
                  refine ⟨7414038084156817037197235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19770768224418178765859293 7414038084156817037197235)
                  ·
                    refine ⟨11121057126235225555795853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7414038084156817037197235 11121057126235225555795853)
                    ·
                      refine ⟨4170396422338209583423445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11121057126235225555795853 4170396422338209583423445)
                      ·
                        rfl

theorem cell23_8121818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_8121818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121818 prefixEnd_8121818 := by exact prefixLift 8121818
  have htrace : WordTrace (prefixWord ++ tailWord_8121818) baseStart_8121818 baseEnd_8121818 := by
    simpa [prefixWord, tailWord_8121818, baseEnd_8121818] using wordTrace_append hprefix tailTrace_8121818
  have hstable : (prefixWord ++ tailWord_8121818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121818).length < 2 ^ (prefixWord ++ tailWord_8121818).sum := by decide
  have hdescent : baseEnd_8121818 < baseStart_8121818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121845 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_8121845 : Nat := 118140960795 + 8121845 * 2 ^ 59
def prefixEnd_8121845 : Nat := 4983230072969 + 3 ^ 40 * 8121845 * 2
def baseEnd_8121845 : Nat := 4170410286315880977785821

theorem tailTrace_8121845 : CollatzResearch.WordTrace tailWord_8121845 prefixEnd_8121845 4170410286315880977785821 := by
  unfold tailWord_8121845
  simp only [CollatzResearch.WordTrace]
  refine ⟨296228023260950140538382989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197485348840633427025588659 296228023260950140538382989)
  ·
    refine ⟨111085508722856302701893621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296228023260950140538382989 111085508722856302701893621)
    ·
      refine ⟨10414266442767778378302527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111085508722856302701893621 10414266442767778378302527)
      ·
        refine ⟨15621399664151667567453791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10414266442767778378302527 15621399664151667567453791)
        ·
          refine ⟨23432099496227501351180687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15621399664151667567453791 23432099496227501351180687)
          ·
            refine ⟨35148149244341252026771031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23432099496227501351180687 35148149244341252026771031)
            ·
              refine ⟨52722223866511878040156547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35148149244341252026771031 52722223866511878040156547)
              ·
                refine ⟨79083335799767817060234821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52722223866511878040156547 79083335799767817060234821)
                ·
                  refine ⟨14828125462456465698794029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79083335799767817060234821 14828125462456465698794029)
                  ·
                    refine ⟨5560547048421174637047761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14828125462456465698794029 5560547048421174637047761)
                    ·
                      refine ⟨4170410286315880977785821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5560547048421174637047761 4170410286315880977785821)
                      ·
                        rfl

theorem cell23_8121845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_8121845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121845 prefixEnd_8121845 := by exact prefixLift 8121845
  have htrace : WordTrace (prefixWord ++ tailWord_8121845) baseStart_8121845 baseEnd_8121845 := by
    simpa [prefixWord, tailWord_8121845, baseEnd_8121845] using wordTrace_append hprefix tailTrace_8121845
  have hstable : (prefixWord ++ tailWord_8121845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121845).length < 2 ^ (prefixWord ++ tailWord_8121845).sum := by decide
  have hdescent : baseEnd_8121845 < baseStart_8121845 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121861 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 3, 2, 3]
def baseStart_8121861 : Nat := 118140960795 + 8121861 * 2 ^ 59
def prefixEnd_8121861 : Nat := 4983230072969 + 3 ^ 40 * 8121861 * 2
def baseEnd_8121861 : Nat := 4170418502006352915185747

theorem tailTrace_8121861 : CollatzResearch.WordTrace tailWord_8121861 prefixEnd_8121861 4170418502006352915185747 := by
  unfold tailWord_8121861
  simp only [CollatzResearch.WordTrace]
  refine ⟨296228606828892175270965437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197485737885928116847310291 296228606828892175270965437)
  ·
    refine ⟨111085727560834565726612039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296228606828892175270965437 111085727560834565726612039)
    ·
      refine ⟨166628591341251848589918059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111085727560834565726612039 166628591341251848589918059)
      ·
        refine ⟨249942887011877772884877089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166628591341251848589918059 249942887011877772884877089)
        ·
          refine ⟨187457165258908329663657817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249942887011877772884877089 187457165258908329663657817)
          ·
            refine ⟨140592873944181247247743363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187457165258908329663657817 140592873944181247247743363)
            ·
              refine ⟨210889310916271870871615045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140592873944181247247743363 210889310916271870871615045)
              ·
                refine ⟨39541745796800975788427821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210889310916271870871615045 39541745796800975788427821)
                ·
                  refine ⟨14828154673800365920660433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39541745796800975788427821 14828154673800365920660433)
                  ·
                    refine ⟨11121116005350274440495325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14828154673800365920660433 11121116005350274440495325)
                    ·
                      refine ⟨4170418502006352915185747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11121116005350274440495325 4170418502006352915185747)
                      ·
                        rfl

theorem cell23_8121861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_8121861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121861 prefixEnd_8121861 := by exact prefixLift 8121861
  have htrace : WordTrace (prefixWord ++ tailWord_8121861) baseStart_8121861 baseEnd_8121861 := by
    simpa [prefixWord, tailWord_8121861, baseEnd_8121861] using wordTrace_append hprefix tailTrace_8121861
  have hstable : (prefixWord ++ tailWord_8121861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121861).length < 2 ^ (prefixWord ++ tailWord_8121861).sum := by decide
  have hdescent : baseEnd_8121861 < baseStart_8121861 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121864 : List Nat := [2, 1, 3, 2, 1, 1, 3, 10]
def baseStart_8121864 : Nat := 118140960795 + 8121864 * 2 ^ 59
def prefixEnd_8121864 : Nat := 4983230072969 + 3 ^ 40 * 8121864 * 2
def baseEnd_8121864 : Nat := 154460001572159866794379

theorem tailTrace_8121864 : CollatzResearch.WordTrace tailWord_8121864 prefixEnd_8121864 154460001572159866794379 := by
  unfold tailWord_8121864
  simp only [CollatzResearch.WordTrace]
  refine ⟨148114358123940653391662323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197485810831920871188883097 148114358123940653391662323)
  ·
    refine ⟨222171537185910980087493485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148114358123940653391662323 222171537185910980087493485)
    ·
      refine ⟨83314326444716617532810057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222171537185910980087493485 83314326444716617532810057)
      ·
        refine ⟨62485744833537463149607543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83314326444716617532810057 62485744833537463149607543)
        ·
          refine ⟨93728617250306194724411315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62485744833537463149607543 93728617250306194724411315)
          ·
            refine ⟨140592925875459292086616973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93728617250306194724411315 140592925875459292086616973)
            ·
              refine ⟨52722347203297234532481365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140592925875459292086616973 52722347203297234532481365)
              ·
                refine ⟨154460001572159866794379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52722347203297234532481365 154460001572159866794379)
                ·
                  rfl

theorem cell23_8121864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 10].length) (baseStart_8121864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121864 prefixEnd_8121864 := by exact prefixLift 8121864
  have htrace : WordTrace (prefixWord ++ tailWord_8121864) baseStart_8121864 baseEnd_8121864 := by
    simpa [prefixWord, tailWord_8121864, baseEnd_8121864] using wordTrace_append hprefix tailTrace_8121864
  have hstable : (prefixWord ++ tailWord_8121864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121864).length < 2 ^ (prefixWord ++ tailWord_8121864).sum := by decide
  have hdescent : baseEnd_8121864 < baseStart_8121864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121888 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 4]
def baseStart_8121888 : Nat := 118140960795 + 8121888 * 2 ^ 59
def prefixEnd_8121888 : Nat := 4983230072969 + 3 ^ 40 * 8121888 * 2
def baseEnd_8121888 : Nat := 4170432365984024309548123

theorem tailTrace_8121888 : CollatzResearch.WordTrace tailWord_8121888 prefixEnd_8121888 4170432365984024309548123 := by
  unfold tailWord_8121888
  simp only [CollatzResearch.WordTrace]
  refine ⟨148114795799897179441099159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197486394399862905921465545 148114795799897179441099159)
  ·
    refine ⟨222172193699845769161648739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148114795799897179441099159 222172193699845769161648739)
    ·
      refine ⟨333258290549768653742473109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222172193699845769161648739 333258290549768653742473109)
      ·
        refine ⟨15621482369520405644178427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 333258290549768653742473109 15621482369520405644178427)
        ·
          refine ⟨23432223554280608466267641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15621482369520405644178427 23432223554280608466267641)
          ·
            refine ⟨17574167665710456349700731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23432223554280608466267641 17574167665710456349700731)
            ·
              refine ⟨26361251498565684524551097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17574167665710456349700731 26361251498565684524551097)
              ·
                refine ⟨19770938623924263393413323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26361251498565684524551097 19770938623924263393413323)
                ·
                  refine ⟨29656407935886395090119985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19770938623924263393413323 29656407935886395090119985)
                  ·
                    refine ⟨22242305951914796317589989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29656407935886395090119985 22242305951914796317589989)
                    ·
                      refine ⟨4170432365984024309548123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22242305951914796317589989 4170432365984024309548123)
                      ·
                        rfl

theorem cell23_8121888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_8121888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121888 prefixEnd_8121888 := by exact prefixLift 8121888
  have htrace : WordTrace (prefixWord ++ tailWord_8121888) baseStart_8121888 baseEnd_8121888 := by
    simpa [prefixWord, tailWord_8121888, baseEnd_8121888] using wordTrace_append hprefix tailTrace_8121888
  have hstable : (prefixWord ++ tailWord_8121888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121888).length < 2 ^ (prefixWord ++ tailWord_8121888).sum := by decide
  have hdescent : baseEnd_8121888 < baseStart_8121888 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121909 : List Nat := [1, 3, 3, 1, 1, 3, 4, 2, 1, 2, 2]
def baseStart_8121909 : Nat := 118140960795 + 8121909 * 2 ^ 59
def prefixEnd_8121909 : Nat := 4983230072969 + 3 ^ 40 * 8121909 * 2
def baseEnd_8121909 : Nat := 4170443149077768727385527

theorem tailTrace_8121909 : CollatzResearch.WordTrace tailWord_8121909 prefixEnd_8121909 4170443149077768727385527 := by
  unfold tailWord_8121909
  simp only [CollatzResearch.WordTrace]
  refine ⟨296230357532718279468712781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197486905021812186312475187 296230357532718279468712781)
  ·
    refine ⟨111086384074769354800767293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296230357532718279468712781 111086384074769354800767293)
    ·
      refine ⟨41657394028038508050287735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111086384074769354800767293 41657394028038508050287735)
      ·
        refine ⟨62486091042057762075431603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41657394028038508050287735 62486091042057762075431603)
        ·
          refine ⟨93729136563086643113147405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62486091042057762075431603 93729136563086643113147405)
          ·
            refine ⟨35148426211157491167430277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93729136563086643113147405 35148426211157491167430277)
            ·
              refine ⟨6590329914592029593893177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35148426211157491167430277 6590329914592029593893177)
              ·
                refine ⟨4942747435944022195419883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6590329914592029593893177 4942747435944022195419883)
                ·
                  refine ⟨7414121153916033293129825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4942747435944022195419883 7414121153916033293129825)
                  ·
                    refine ⟨5560590865437024969847369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7414121153916033293129825 5560590865437024969847369)
                    ·
                      refine ⟨4170443149077768727385527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5560590865437024969847369 4170443149077768727385527)
                      ·
                        rfl

theorem cell23_8121909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_8121909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121909 prefixEnd_8121909 := by exact prefixLift 8121909
  have htrace : WordTrace (prefixWord ++ tailWord_8121909) baseStart_8121909 baseEnd_8121909 := by
    simpa [prefixWord, tailWord_8121909, baseEnd_8121909] using wordTrace_append hprefix tailTrace_8121909
  have hstable : (prefixWord ++ tailWord_8121909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121909).length < 2 ^ (prefixWord ++ tailWord_8121909).sum := by decide
  have hdescent : baseEnd_8121909 < baseStart_8121909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8121961 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 2, 2, 4]
def baseStart_8121961 : Nat := 118140960795 + 8121961 * 2 ^ 59
def prefixEnd_8121961 : Nat := 4983230072969 + 3 ^ 40 * 8121961 * 2
def baseEnd_8121961 : Nat := 4170469850071802523935287

theorem tailTrace_8121961 : CollatzResearch.WordTrace tailWord_8121961 prefixEnd_8121961 4170469850071802523935287 := by
  unfold tailWord_8121961
  simp only [CollatzResearch.WordTrace]
  refine ⟨296232254128529892349605737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197488169419019928233070491 296232254128529892349605737)
  ·
    refine ⟨222174190596397419262204303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296232254128529892349605737 222174190596397419262204303)
    ·
      refine ⟨333261285894596128893306455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222174190596397419262204303 333261285894596128893306455)
      ·
        refine ⟨499891928841894193339959683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333261285894596128893306455 499891928841894193339959683)
        ·
          refine ⟨749837893262841290009939525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499891928841894193339959683 749837893262841290009939525)
          ·
            refine ⟨140594604986782741876863661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 749837893262841290009939525 140594604986782741876863661)
            ·
              refine ⟨52722976870043528203823873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140594604986782741876863661 52722976870043528203823873)
              ·
                refine ⟨39542232652532646152867905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52722976870043528203823873 39542232652532646152867905)
                ·
                  refine ⟨29656674489399484614650929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39542232652532646152867905 29656674489399484614650929)
                  ·
                    refine ⟨22242505867049613460988197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29656674489399484614650929 22242505867049613460988197)
                    ·
                      refine ⟨4170469850071802523935287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22242505867049613460988197 4170469850071802523935287)
                      ·
                        rfl

theorem cell23_8121961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_8121961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8121961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8121961 prefixEnd_8121961 := by exact prefixLift 8121961
  have htrace : WordTrace (prefixWord ++ tailWord_8121961) baseStart_8121961 baseEnd_8121961 := by
    simpa [prefixWord, tailWord_8121961, baseEnd_8121961] using wordTrace_append hprefix tailTrace_8121961
  have hstable : (prefixWord ++ tailWord_8121961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8121961).length < 2 ^ (prefixWord ++ tailWord_8121961).sum := by decide
  have hdescent : baseEnd_8121961 < baseStart_8121961 := by decide
  rcases family_descends (prefixWord ++ tailWord_8121961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122048 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 5, 4]
def baseStart_8122048 : Nat := 118140960795 + 8122048 * 2 ^ 59
def prefixEnd_8122048 : Nat := 4983230072969 + 3 ^ 40 * 8122048 * 2
def baseEnd_8122048 : Nat := 1390171507629581227849129

theorem tailTrace_8122048 : CollatzResearch.WordTrace tailWord_8122048 prefixEnd_8122048 1390171507629581227849129 := by
  unfold tailWord_8122048
  simp only [CollatzResearch.WordTrace]
  refine ⟨148117713639607353104011399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197490284852809804138681865 148117713639607353104011399)
  ·
    refine ⟨222176570459411029656017099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148117713639607353104011399 222176570459411029656017099)
    ·
      refine ⟨333264855689116544484025649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222176570459411029656017099 333264855689116544484025649)
      ·
        refine ⟨249948641766837408363019237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333264855689116544484025649 249948641766837408363019237)
        ·
          refine ⟨46865370331282014068066107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249948641766837408363019237 46865370331282014068066107)
          ·
            refine ⟨70298055496923021102099161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46865370331282014068066107 70298055496923021102099161)
            ·
              refine ⟨52723541622692265826574371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70298055496923021102099161 52723541622692265826574371)
              ·
                refine ⟨79085312434038398739861557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52723541622692265826574371 79085312434038398739861557)
                ·
                  refine ⟨7414248040691099881862021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79085312434038398739861557 7414248040691099881862021)
                  ·
                    refine ⟨1390171507629581227849129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7414248040691099881862021 1390171507629581227849129)
                    ·
                      rfl

theorem cell23_8122048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5, 4].length) (baseStart_8122048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122048 prefixEnd_8122048 := by exact prefixLift 8122048
  have htrace : WordTrace (prefixWord ++ tailWord_8122048) baseStart_8122048 baseEnd_8122048 := by
    simpa [prefixWord, tailWord_8122048, baseEnd_8122048] using wordTrace_append hprefix tailTrace_8122048
  have hstable : (prefixWord ++ tailWord_8122048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122048).length < 2 ^ (prefixWord ++ tailWord_8122048).sum := by decide
  have hdescent : baseEnd_8122048 < baseStart_8122048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122108 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 3, 5]
def baseStart_8122108 : Nat := 118140960795 + 8122108 * 2 ^ 59
def prefixEnd_8122108 : Nat := 4983230072969 + 3 ^ 40 * 8122108 * 2
def baseEnd_8122108 : Nat := 1390181777242671149599037

theorem tailTrace_8122108 : CollatzResearch.WordTrace tailWord_8122108 prefixEnd_8122108 1390181777242671149599037 := by
  unfold tailWord_8122108
  simp only [CollatzResearch.WordTrace]
  refine ⟨148118807829498668227603489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197491743772664890970137985 148118807829498668227603489)
  ·
    refine ⟨111089105872124001170702617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148118807829498668227603489 111089105872124001170702617)
    ·
      refine ⟨83316829404093000878026963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111089105872124001170702617 83316829404093000878026963)
      ·
        refine ⟨124975244106139501317040445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83316829404093000878026963 124975244106139501317040445)
        ·
          refine ⟨46865716539802312993890167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124975244106139501317040445 46865716539802312993890167)
          ·
            refine ⟨70298574809703469490835251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46865716539802312993890167 70298574809703469490835251)
            ·
              refine ⟨105447862214555204236252877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70298574809703469490835251 105447862214555204236252877)
              ·
                refine ⟨39542948330458201588594829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105447862214555204236252877 39542948330458201588594829)
                ·
                  refine ⟨14828605623921825595723061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39542948330458201588594829 14828605623921825595723061)
                  ·
                    refine ⟨1390181777242671149599037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14828605623921825595723061 1390181777242671149599037)
                    ·
                      rfl

theorem cell23_8122108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_8122108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122108 prefixEnd_8122108 := by exact prefixLift 8122108
  have htrace : WordTrace (prefixWord ++ tailWord_8122108) baseStart_8122108 baseEnd_8122108 := by
    simpa [prefixWord, tailWord_8122108, baseEnd_8122108] using wordTrace_append hprefix tailTrace_8122108
  have hstable : (prefixWord ++ tailWord_8122108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122108).length < 2 ^ (prefixWord ++ tailWord_8122108).sum := by decide
  have hdescent : baseEnd_8122108 < baseStart_8122108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122162 : List Nat := [3, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4]
def baseStart_8122162 : Nat := 118140960795 + 8122162 * 2 ^ 59
def prefixEnd_8122162 : Nat := 4983230072969 + 3 ^ 40 * 8122162 * 2
def baseEnd_8122162 : Nat := 4170573059683356237521863

theorem tailTrace_8122162 : CollatzResearch.WordTrace tailWord_8122162 prefixEnd_8122162 4170573059683356237521863 := by
  unfold tailWord_8122162
  simp only [CollatzResearch.WordTrace]
  refine ⟨74059896300200425919418185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197493056800534469118448493 74059896300200425919418185)
  ·
    refine ⟨55544922225150319439563639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74059896300200425919418185 55544922225150319439563639)
    ·
      refine ⟨83317383337725479159345459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55544922225150319439563639 83317383337725479159345459)
      ·
        refine ⟨124976075006588218739018189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83317383337725479159345459 124976075006588218739018189)
        ·
          refine ⟨46866028127470582027131821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124976075006588218739018189 46866028127470582027131821)
          ·
            refine ⟨17574760547801468260174433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46866028127470582027131821 17574760547801468260174433)
            ·
              refine ⟨13181070410851101195130825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17574760547801468260174433 13181070410851101195130825)
              ·
                refine ⟨9885802808138325896348119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13181070410851101195130825 9885802808138325896348119)
                ·
                  refine ⟨14828704212207488844522179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9885802808138325896348119 14828704212207488844522179)
                  ·
                    refine ⟨22243056318311233266783269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14828704212207488844522179 22243056318311233266783269)
                    ·
                      refine ⟨4170573059683356237521863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22243056318311233266783269 4170573059683356237521863)
                      ·
                        rfl

theorem cell23_8122162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_8122162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122162 prefixEnd_8122162 := by exact prefixLift 8122162
  have htrace : WordTrace (prefixWord ++ tailWord_8122162) baseStart_8122162 baseEnd_8122162 := by
    simpa [prefixWord, tailWord_8122162, baseEnd_8122162] using wordTrace_append hprefix tailTrace_8122162
  have hstable : (prefixWord ++ tailWord_8122162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122162).length < 2 ^ (prefixWord ++ tailWord_8122162).sum := by decide
  have hdescent : baseEnd_8122162 < baseStart_8122162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122168 : List Nat := [2, 1, 2, 1, 3, 4, 1, 9]
def baseStart_8122168 : Nat := 118140960795 + 8122168 * 2 ^ 59
def prefixEnd_8122168 : Nat := 4983230072969 + 3 ^ 40 * 8122168 * 2
def baseEnd_8122168 : Nat := 154465782983973452372105

theorem tailTrace_8122168 : CollatzResearch.WordTrace tailWord_8122168 prefixEnd_8122168 154465782983973452372105 := by
  unfold tailWord_8122168
  simp only [CollatzResearch.WordTrace]
  refine ⟨148119902019389983351195579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197493202692519977801594105 148119902019389983351195579)
  ·
    refine ⟨222179853029084975026793369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148119902019389983351195579 222179853029084975026793369)
    ·
      refine ⟨166634889771813731270095027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222179853029084975026793369 166634889771813731270095027)
      ·
        refine ⟨249952334657720596905142541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166634889771813731270095027 249952334657720596905142541)
        ·
          refine ⟨93732125496645223839428453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249952334657720596905142541 93732125496645223839428453)
          ·
            refine ⟨17574773530620979469892835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93732125496645223839428453 17574773530620979469892835)
            ·
              refine ⟨26362160295931469204839253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17574773530620979469892835 26362160295931469204839253)
              ·
                refine ⟨154465782983973452372105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26362160295931469204839253 154465782983973452372105)
                ·
                  rfl

theorem cell23_8122168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 9].length) (baseStart_8122168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122168 prefixEnd_8122168 := by exact prefixLift 8122168
  have htrace : WordTrace (prefixWord ++ tailWord_8122168) baseStart_8122168 baseEnd_8122168 := by
    simpa [prefixWord, tailWord_8122168, baseEnd_8122168] using wordTrace_append hprefix tailTrace_8122168
  have hstable : (prefixWord ++ tailWord_8122168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122168).length < 2 ^ (prefixWord ++ tailWord_8122168).sum := by decide
  have hdescent : baseEnd_8122168 < baseStart_8122168 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122196 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 3, 2, 2]
def baseStart_8122196 : Nat := 118140960795 + 8122196 * 2 ^ 59
def prefixEnd_8122196 : Nat := 4983230072969 + 3 ^ 40 * 8122196 * 2
def baseEnd_8122196 : Nat := 4170590518025609104496707

theorem tailTrace_8122196 : CollatzResearch.WordTrace tailWord_8122196 prefixEnd_8122196 4170590518025609104496707 := by
  unfold tailWord_8122196
  simp only [CollatzResearch.WordTrace]
  refine ⟨148120412641339263742205221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197493883521785684989606961 148120412641339263742205221)
  ·
    refine ⟨27772577370251111951663479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148120412641339263742205221 27772577370251111951663479)
    ·
      refine ⟨41658866055376667927495219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27772577370251111951663479 41658866055376667927495219)
      ·
        refine ⟨62488299083065001891242829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41658866055376667927495219 62488299083065001891242829)
        ·
          refine ⟨23433112156149375709216061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62488299083065001891242829 23433112156149375709216061)
          ·
            refine ⟨8787417058556015890956023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23433112156149375709216061 8787417058556015890956023)
            ·
              refine ⟨13181125587834023836434035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8787417058556015890956023 13181125587834023836434035)
              ·
                refine ⟨19771688381751035754651053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13181125587834023836434035 19771688381751035754651053)
                ·
                  refine ⟨7414383143156638407994145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19771688381751035754651053 7414383143156638407994145)
                  ·
                    refine ⟨5560787357367478805995609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7414383143156638407994145 5560787357367478805995609)
                    ·
                      refine ⟨4170590518025609104496707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5560787357367478805995609 4170590518025609104496707)
                      ·
                        rfl

theorem cell23_8122196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_8122196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122196 prefixEnd_8122196 := by exact prefixLift 8122196
  have htrace : WordTrace (prefixWord ++ tailWord_8122196) baseStart_8122196 baseEnd_8122196 := by
    simpa [prefixWord, tailWord_8122196, baseEnd_8122196] using wordTrace_append hprefix tailTrace_8122196
  have hstable : (prefixWord ++ tailWord_8122196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122196).length < 2 ^ (prefixWord ++ tailWord_8122196).sum := by decide
  have hdescent : baseEnd_8122196 < baseStart_8122196 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122269 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 1, 4, 2]
def baseStart_8122269 : Nat := 118140960795 + 8122269 * 2 ^ 59
def prefixEnd_8122269 : Nat := 4983230072969 + 3 ^ 40 * 8122269 * 2
def baseEnd_8122269 : Nat := 4170628002113387318883871

theorem tailTrace_8122269 : CollatzResearch.WordTrace tailWord_8122269 prefixEnd_8122269 4170628002113387318883871 := by
  unfold tailWord_8122269
  simp only [CollatzResearch.WordTrace]
  refine ⟨296243487811414060951817861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197495658540942707301211907 296243487811414060951817861)
  ·
    refine ⟨55545653964640136428465849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296243487811414060951817861 55545653964640136428465849)
    ·
      refine ⟨41659240473480102321349387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55545653964640136428465849 41659240473480102321349387)
      ·
        refine ⟨62488860710220153482024081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41659240473480102321349387 62488860710220153482024081)
        ·
          refine ⟨46866645532665115111518061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62488860710220153482024081 46866645532665115111518061)
          ·
            refine ⟨17574992074749418166819273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46866645532665115111518061 17574992074749418166819273)
            ·
              refine ⟨13181244056062063625114455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17574992074749418166819273 13181244056062063625114455)
              ·
                refine ⟨19771866084093095437671683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13181244056062063625114455 19771866084093095437671683)
                ·
                  refine ⟨29657799126139643156507525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19771866084093095437671683 29657799126139643156507525)
                  ·
                    refine ⟨5560837336151183091845161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29657799126139643156507525 5560837336151183091845161)
                    ·
                      refine ⟨4170628002113387318883871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5560837336151183091845161 4170628002113387318883871)
                      ·
                        rfl

theorem cell23_8122269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_8122269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122269 prefixEnd_8122269 := by exact prefixLift 8122269
  have htrace : WordTrace (prefixWord ++ tailWord_8122269) baseStart_8122269 baseEnd_8122269 := by
    simpa [prefixWord, tailWord_8122269, baseEnd_8122269] using wordTrace_append hprefix tailTrace_8122269
  have hstable : (prefixWord ++ tailWord_8122269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122269).length < 2 ^ (prefixWord ++ tailWord_8122269).sum := by decide
  have hdescent : baseEnd_8122269 < baseStart_8122269 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122302 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_8122302 : Nat := 118140960795 + 8122302 * 2 ^ 59
def prefixEnd_8122302 : Nat := 4983230072969 + 3 ^ 40 * 8122302 * 2
def baseEnd_8122302 : Nat := 4170644946974985689771219

theorem tailTrace_8122302 : CollatzResearch.WordTrace tailWord_8122302 prefixEnd_8122302 4170644946974985689771219 := by
  unfold tailWord_8122302
  simp only [CollatzResearch.WordTrace]
  refine ⟨37030586427536813448471145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197496460946863005058512773 37030586427536813448471145)
  ·
    refine ⟨27772939820652610086353359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37030586427536813448471145 27772939820652610086353359)
    ·
      refine ⟨41659409730978915129530039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27772939820652610086353359 41659409730978915129530039)
      ·
        refine ⟨62489114596468372694295059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41659409730978915129530039 62489114596468372694295059)
        ·
          refine ⟨93733671894702559041442589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62489114596468372694295059 93733671894702559041442589)
          ·
            refine ⟨35150126960513459640540971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93733671894702559041442589 35150126960513459640540971)
            ·
              refine ⟨52725190440770189460811457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35150126960513459640540971 52725190440770189460811457)
              ·
                refine ⟨39543892830577642095608593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52725190440770189460811457 39543892830577642095608593)
                ·
                  refine ⟨29657919622933231571706445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39543892830577642095608593 29657919622933231571706445)
                  ·
                    refine ⟨11121719858599961839389917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29657919622933231571706445 11121719858599961839389917)
                    ·
                      refine ⟨4170644946974985689771219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11121719858599961839389917 4170644946974985689771219)
                      ·
                        rfl

theorem cell23_8122302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_8122302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122302 prefixEnd_8122302 := by exact prefixLift 8122302
  have htrace : WordTrace (prefixWord ++ tailWord_8122302) baseStart_8122302 baseEnd_8122302 := by
    simpa [prefixWord, tailWord_8122302, baseEnd_8122302] using wordTrace_append hprefix tailTrace_8122302
  have hstable : (prefixWord ++ tailWord_8122302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122302).length < 2 ^ (prefixWord ++ tailWord_8122302).sum := by decide
  have hdescent : baseEnd_8122302 < baseStart_8122302 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122365 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 8]
def baseStart_8122365 : Nat := 118140960795 + 8122365 * 2 ^ 59
def prefixEnd_8122365 : Nat := 4983230072969 + 3 ^ 40 * 8122365 * 2
def baseEnd_8122365 : Nat := 463408588472913215920381

theorem tailTrace_8122365 : CollatzResearch.WordTrace tailWord_8122365 prefixEnd_8122365 463408588472913215920381 := by
  unfold tailWord_8122365
  simp only [CollatzResearch.WordTrace]
  refine ⟨296246989219066269347312549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197497992812710846231541699 296246989219066269347312549)
  ·
    refine ⟨55546310478574925502621103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296246989219066269347312549 55546310478574925502621103)
    ·
      refine ⟨83319465717862388253931655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55546310478574925502621103 83319465717862388253931655)
      ·
        refine ⟨124979198576793582380897483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83319465717862388253931655 124979198576793582380897483)
        ·
          refine ⟨187468797865190373571346225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124979198576793582380897483 187468797865190373571346225)
          ·
            refine ⟨140601598398892780178509669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187468797865190373571346225 140601598398892780178509669)
            ·
              refine ⟨26362799699792396283470563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140601598398892780178509669 26362799699792396283470563)
              ·
                refine ⟨39544199549688594425205845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26362799699792396283470563 39544199549688594425205845)
                ·
                  refine ⟨463408588472913215920381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39544199549688594425205845 463408588472913215920381)
                  ·
                    rfl

theorem cell23_8122365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_8122365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122365 prefixEnd_8122365 := by exact prefixLift 8122365
  have htrace : WordTrace (prefixWord ++ tailWord_8122365) baseStart_8122365 baseEnd_8122365 := by
    simpa [prefixWord, tailWord_8122365, baseEnd_8122365] using wordTrace_append hprefix tailTrace_8122365
  have hstable : (prefixWord ++ tailWord_8122365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122365).length < 2 ^ (prefixWord ++ tailWord_8122365).sum := by decide
  have hdescent : baseEnd_8122365 < baseStart_8122365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122382 : List Nat := [4, 1, 1, 2, 2, 1, 3, 3, 6]
def baseStart_8122382 : Nat := 118140960795 + 8122382 * 2 ^ 59
def prefixEnd_8122382 : Nat := 4983230072969 + 3 ^ 40 * 8122382 * 2
def baseEnd_8122382 : Nat := 463409558380816152974539

theorem tailTrace_8122382 : CollatzResearch.WordTrace tailWord_8122382 prefixEnd_8122382 463409558380816152974539 := by
  unfold tailWord_8122382
  simp only [CollatzResearch.WordTrace]
  refine ⟨37030951157500585156335175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197498406173336454167120933 37030951157500585156335175)
  ·
    refine ⟨55546426736250877734502763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37030951157500585156335175 55546426736250877734502763)
    ·
      refine ⟨83319640104376316601754145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55546426736250877734502763 83319640104376316601754145)
      ·
        refine ⟨62489730078282237451315609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83319640104376316601754145 62489730078282237451315609)
        ·
          refine ⟨46867297558711678088486707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62489730078282237451315609 46867297558711678088486707)
          ·
            refine ⟨70300946338067517132730061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46867297558711678088486707 70300946338067517132730061)
            ·
              refine ⟨26362854876775318924773773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70300946338067517132730061 26362854876775318924773773)
              ·
                refine ⟨9886070578790744596790165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26362854876775318924773773 9886070578790744596790165)
                ·
                  refine ⟨463409558380816152974539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9886070578790744596790165 463409558380816152974539)
                  ·
                    rfl

theorem cell23_8122382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_8122382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122382 prefixEnd_8122382 := by exact prefixLift 8122382
  have htrace : WordTrace (prefixWord ++ tailWord_8122382) baseStart_8122382 baseEnd_8122382 := by
    simpa [prefixWord, tailWord_8122382, baseEnd_8122382] using wordTrace_append hprefix tailTrace_8122382
  have hstable : (prefixWord ++ tailWord_8122382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122382).length < 2 ^ (prefixWord ++ tailWord_8122382).sum := by decide
  have hdescent : baseEnd_8122382 < baseStart_8122382 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122419 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 2, 3, 2]
def baseStart_8122419 : Nat := 118140960795 + 8122419 * 2 ^ 59
def prefixEnd_8122419 : Nat := 4983230072969 + 3 ^ 40 * 8122419 * 2
def baseEnd_8122419 : Nat := 4170705024211561732008181

theorem tailTrace_8122419 : CollatzResearch.WordTrace tailWord_8122419 prefixEnd_8122419 4170705024211561732008181 := by
  unfold tailWord_8122419
  simp only [CollatzResearch.WordTrace]
  refine ⟨296248958760870636569778311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197499305840580424379852207 296248958760870636569778311)
  ·
    refine ⟨444373438141305954854667467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296248958760870636569778311 444373438141305954854667467)
    ·
      refine ⟨666560157211958932282001201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444373438141305954854667467 666560157211958932282001201)
      ·
        refine ⟨499920117908969199211500901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666560157211958932282001201 499920117908969199211500901)
        ·
          refine ⟨93735022107931724852156419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 499920117908969199211500901 93735022107931724852156419)
          ·
            refine ⟨140602533161897587278234629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93735022107931724852156419 140602533161897587278234629)
            ·
              refine ⟨26362974967855797614668993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140602533161897587278234629 26362974967855797614668993)
              ·
                refine ⟨19772231225891848211001745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26362974967855797614668993 19772231225891848211001745)
                ·
                  refine ⟨14829173419418886158251309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19772231225891848211001745 14829173419418886158251309)
                  ·
                    refine ⟨5560940032282082309344241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14829173419418886158251309 5560940032282082309344241)
                    ·
                      refine ⟨4170705024211561732008181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5560940032282082309344241 4170705024211561732008181)
                      ·
                        rfl

theorem cell23_8122419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 3, 2].length) (baseStart_8122419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122419 prefixEnd_8122419 := by exact prefixLift 8122419
  have htrace : WordTrace (prefixWord ++ tailWord_8122419) baseStart_8122419 baseEnd_8122419 := by
    simpa [prefixWord, tailWord_8122419, baseEnd_8122419] using wordTrace_append hprefix tailTrace_8122419
  have hstable : (prefixWord ++ tailWord_8122419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122419).length < 2 ^ (prefixWord ++ tailWord_8122419).sum := by decide
  have hdescent : baseEnd_8122419 < baseStart_8122419 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122432 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 4]
def baseStart_8122432 : Nat := 118140960795 + 8122432 * 2 ^ 59
def prefixEnd_8122432 : Nat := 4983230072969 + 3 ^ 40 * 8122432 * 2
def baseEnd_8122432 : Nat := 4170711699460070181145621

theorem tailTrace_8122432 : CollatzResearch.WordTrace tailWord_8122432 prefixEnd_8122432 4170711699460070181145621 := by
  unfold tailWord_8122432
  simp only [CollatzResearch.WordTrace]
  refine ⟨148124716454911769895000775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197499621939882359860001033 148124716454911769895000775)
  ·
    refine ⟨222187074682367654842501163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148124716454911769895000775 222187074682367654842501163)
    ·
      refine ⟨333280612023551482263751745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222187074682367654842501163 333280612023551482263751745)
      ·
        refine ⟨249960459017663611697813809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333280612023551482263751745 249960459017663611697813809)
        ·
          refine ⟨187470344263247708773360357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249960459017663611697813809 187470344263247708773360357)
          ·
            refine ⟨35150689549358945395005067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187470344263247708773360357 35150689549358945395005067)
            ·
              refine ⟨52726034324038418092507601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35150689549358945395005067 52726034324038418092507601)
              ·
                refine ⟨39544525743028813569380701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52726034324038418092507601 39544525743028813569380701)
                ·
                  refine ⟨14829197153635805088517763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39544525743028813569380701 14829197153635805088517763)
                  ·
                    refine ⟨22243795730453707632776645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14829197153635805088517763 22243795730453707632776645)
                    ·
                      refine ⟨4170711699460070181145621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22243795730453707632776645 4170711699460070181145621)
                      ·
                        rfl

theorem cell23_8122432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_8122432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122432 prefixEnd_8122432 := by exact prefixLift 8122432
  have htrace : WordTrace (prefixWord ++ tailWord_8122432) baseStart_8122432 baseEnd_8122432 := by
    simpa [prefixWord, tailWord_8122432, baseEnd_8122432] using wordTrace_append hprefix tailTrace_8122432
  have hstable : (prefixWord ++ tailWord_8122432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122432).length < 2 ^ (prefixWord ++ tailWord_8122432).sum := by decide
  have hdescent : baseEnd_8122432 < baseStart_8122432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122442 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 6, 4]
def baseStart_8122442 : Nat := 118140960795 + 8122442 * 2 ^ 59
def prefixEnd_8122442 : Nat := 4983230072969 + 3 ^ 40 * 8122442 * 2
def baseEnd_8122442 : Nat := 1390238944755538380673525

theorem tailTrace_8122442 : CollatzResearch.WordTrace tailWord_8122442 prefixEnd_8122442 1390238944755538380673525 := by
  unfold tailWord_8122442
  simp only [CollatzResearch.WordTrace]
  refine ⟨74062449409946827874466395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197499865093191540998577053 74062449409946827874466395)
  ·
    refine ⟨111093674114920241811699593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74062449409946827874466395 111093674114920241811699593)
    ·
      refine ⟨83320255586190181358774695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111093674114920241811699593 83320255586190181358774695)
      ·
        refine ⟨124980383379285272038162043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83320255586190181358774695 124980383379285272038162043)
        ·
          refine ⟨187470575068927908057243065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124980383379285272038162043 187470575068927908057243065)
          ·
            refine ⟨140602931301695931042932299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187470575068927908057243065 140602931301695931042932299)
            ·
              refine ⟨210904396952543896564398449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140602931301695931042932299 210904396952543896564398449)
              ·
                refine ⟨158178297714407922423298837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210904396952543896564398449 158178297714407922423298837)
                ·
                  refine ⟨7414607705362871363592133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158178297714407922423298837 7414607705362871363592133)
                  ·
                    refine ⟨1390238944755538380673525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7414607705362871363592133 1390238944755538380673525)
                    ·
                      rfl

theorem cell23_8122442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_8122442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122442 prefixEnd_8122442 := by exact prefixLift 8122442
  have htrace : WordTrace (prefixWord ++ tailWord_8122442) baseStart_8122442 baseEnd_8122442 := by
    simpa [prefixWord, tailWord_8122442, baseEnd_8122442] using wordTrace_append hprefix tailTrace_8122442
  have hstable : (prefixWord ++ tailWord_8122442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122442).length < 2 ^ (prefixWord ++ tailWord_8122442).sum := by decide
  have hdescent : baseEnd_8122442 < baseStart_8122442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122455 : List Nat := [1, 1, 3, 2, 2, 1, 2, 11]
def baseStart_8122455 : Nat := 118140960795 + 8122455 * 2 ^ 59
def prefixEnd_8122455 : Nat := 4983230072969 + 3 ^ 40 * 8122455 * 2
def baseEnd_8122455 : Nat := 154471241093152725598445

theorem tailTrace_8122455 : CollatzResearch.WordTrace tailWord_8122455 prefixEnd_8122455 154471241093152725598445 := by
  unfold tailWord_8122455
  simp only [CollatzResearch.WordTrace]
  refine ⟨296250271788740214718088819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197500181192493476478725879 296250271788740214718088819)
  ·
    refine ⟨444375407683110322077133229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296250271788740214718088819 444375407683110322077133229)
    ·
      refine ⟨166640777881166370778924961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444375407683110322077133229 166640777881166370778924961)
      ·
        refine ⟨124980583410874778084193721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166640777881166370778924961 124980583410874778084193721)
        ·
          refine ⟨93735437558156083563145291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124980583410874778084193721 93735437558156083563145291)
          ·
            refine ⟨140603156337234125344717937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93735437558156083563145291 140603156337234125344717937)
            ·
              refine ⟨105452367252925594008538453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140603156337234125344717937 105452367252925594008538453)
              ·
                refine ⟨154471241093152725598445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 105452367252925594008538453 154471241093152725598445)
                ·
                  rfl

theorem cell23_8122455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 11].length) (baseStart_8122455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122455 prefixEnd_8122455 := by exact prefixLift 8122455
  have htrace : WordTrace (prefixWord ++ tailWord_8122455) baseStart_8122455 baseEnd_8122455 := by
    simpa [prefixWord, tailWord_8122455, baseEnd_8122455] using wordTrace_append hprefix tailTrace_8122455
  have hstable : (prefixWord ++ tailWord_8122455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122455).length < 2 ^ (prefixWord ++ tailWord_8122455).sum := by decide
  have hdescent : baseEnd_8122455 < baseStart_8122455 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122476 : List Nat := [2, 2, 1, 1, 3, 5, 1, 2, 2, 4]
def baseStart_8122476 : Nat := 118140960795 + 8122476 * 2 ^ 59
def prefixEnd_8122476 : Nat := 4983230072969 + 3 ^ 40 * 8122476 * 2
def baseEnd_8122476 : Nat := 1390244764202956002998473

theorem tailTrace_8122476 : CollatzResearch.WordTrace tailWord_8122476 prefixEnd_8122476 1390244764202956002998473 := by
  unfold tailWord_8122476
  simp only [CollatzResearch.WordTrace]
  refine ⟨148125518860832067652301641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197500691814442756869735521 148125518860832067652301641)
  ·
    refine ⟨111094139145624050739226231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148125518860832067652301641 111094139145624050739226231)
    ·
      refine ⟨166641208718436076108839347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111094139145624050739226231 166641208718436076108839347)
      ·
        refine ⟨249961813077654114163259021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166641208718436076108839347 249961813077654114163259021)
        ·
          refine ⟨93735679904120292811222133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249961813077654114163259021 93735679904120292811222133)
          ·
            refine ⟨8787719991011277451052075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93735679904120292811222133 8787719991011277451052075)
            ·
              refine ⟨13181579986516916176578113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8787719991011277451052075 13181579986516916176578113)
              ·
                refine ⟨9886184989887687132433585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13181579986516916176578113 9886184989887687132433585)
                ·
                  refine ⟨7414638742415765349325189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9886184989887687132433585 7414638742415765349325189)
                  ·
                    refine ⟨1390244764202956002998473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7414638742415765349325189 1390244764202956002998473)
                    ·
                      rfl

theorem cell23_8122476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_8122476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122476 prefixEnd_8122476 := by exact prefixLift 8122476
  have htrace : WordTrace (prefixWord ++ tailWord_8122476) baseStart_8122476 baseEnd_8122476 := by
    simpa [prefixWord, tailWord_8122476, baseEnd_8122476] using wordTrace_append hprefix tailTrace_8122476
  have hstable : (prefixWord ++ tailWord_8122476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122476).length < 2 ^ (prefixWord ++ tailWord_8122476).sum := by decide
  have hdescent : baseEnd_8122476 < baseStart_8122476 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122499 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 3]
def baseStart_8122499 : Nat := 118140960795 + 8122499 * 2 ^ 59
def prefixEnd_8122499 : Nat := 4983230072969 + 3 ^ 40 * 8122499 * 2
def baseEnd_8122499 : Nat := 4170746102663921419007813

theorem tailTrace_8122499 : CollatzResearch.WordTrace tailWord_8122499 prefixEnd_8122499 4170746102663921419007813 := by
  unfold tailWord_8122499
  simp only [CollatzResearch.WordTrace]
  refine ⟨296251876600580810232690551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197501251067053873488460367 296251876600580810232690551)
  ·
    refine ⟨444377814900871215349035827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296251876600580810232690551 444377814900871215349035827)
    ·
      refine ⟨666566722351306823023553741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444377814900871215349035827 666566722351306823023553741)
      ·
        refine ⟨249962520881740058633832653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 666566722351306823023553741 249962520881740058633832653)
        ·
          refine ⟨93735945330652521987687245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249962520881740058633832653 93735945330652521987687245)
          ·
            refine ⟨35150979498994695745382717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93735945330652521987687245 35150979498994695745382717)
            ·
              refine ⟨13181617312123010904518519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35150979498994695745382717 13181617312123010904518519)
              ·
                refine ⟨19772425968184516356777779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13181617312123010904518519 19772425968184516356777779)
                ·
                  refine ⟨29658638952276774535166669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19772425968184516356777779 29658638952276774535166669)
                  ·
                    refine ⟨11121989607103790450687501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29658638952276774535166669 11121989607103790450687501)
                    ·
                      refine ⟨4170746102663921419007813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11121989607103790450687501 4170746102663921419007813)
                      ·
                        rfl

theorem cell23_8122499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_8122499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122499 prefixEnd_8122499 := by exact prefixLift 8122499
  have htrace : WordTrace (prefixWord ++ tailWord_8122499) baseStart_8122499 baseEnd_8122499 := by
    simpa [prefixWord, tailWord_8122499, baseEnd_8122499] using wordTrace_append hprefix tailTrace_8122499
  have hstable : (prefixWord ++ tailWord_8122499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122499).length < 2 ^ (prefixWord ++ tailWord_8122499).sum := by decide
  have hdescent : baseEnd_8122499 < baseStart_8122499 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122552 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 1, 4, 4]
def baseStart_8122552 : Nat := 118140960795 + 8122552 * 2 ^ 59
def prefixEnd_8122552 : Nat := 4983230072969 + 3 ^ 40 * 8122552 * 2
def baseEnd_8122552 : Nat := 4170773317138609711645069

theorem tailTrace_8122552 : CollatzResearch.WordTrace tailWord_8122552 prefixEnd_8122552 4170773317138609711645069 := by
  unfold tailWord_8122552
  simp only [CollatzResearch.WordTrace]
  refine ⟨148126904834694400142184955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197502539779592533522913273 148126904834694400142184955)
  ·
    refine ⟨222190357252041600213277433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148126904834694400142184955 222190357252041600213277433)
    ·
      refine ⟨166642767939031200159958075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222190357252041600213277433 166642767939031200159958075)
      ·
        refine ⟨249964151908546800239937113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166642767939031200159958075 249964151908546800239937113)
        ·
          refine ⟨187473113931410100179952835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249964151908546800239937113 187473113931410100179952835)
          ·
            refine ⟨281209670897115150269929253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187473113931410100179952835 281209670897115150269929253)
            ·
              refine ⟨52726813293209090675611735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281209670897115150269929253 52726813293209090675611735)
              ·
                refine ⟨79090219939813636013417603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52726813293209090675611735 79090219939813636013417603)
                ·
                  refine ⟨118635329909720454020126405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79090219939813636013417603 118635329909720454020126405)
                  ·
                    refine ⟨22244124358072585128773701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118635329909720454020126405 22244124358072585128773701)
                    ·
                      refine ⟨4170773317138609711645069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22244124358072585128773701 4170773317138609711645069)
                      ·
                        rfl

theorem cell23_8122552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_8122552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122552 prefixEnd_8122552 := by exact prefixLift 8122552
  have htrace : WordTrace (prefixWord ++ tailWord_8122552) baseStart_8122552 baseEnd_8122552 := by
    simpa [prefixWord, tailWord_8122552, baseEnd_8122552] using wordTrace_append hprefix tailTrace_8122552
  have hstable : (prefixWord ++ tailWord_8122552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122552).length < 2 ^ (prefixWord ++ tailWord_8122552).sum := by decide
  have hdescent : baseEnd_8122552 < baseStart_8122552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122626 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_8122626 : Nat := 118140960795 + 8122626 * 2 ^ 59
def prefixEnd_8122626 : Nat := 4983230072969 + 3 ^ 40 * 8122626 * 2
def baseEnd_8122626 : Nat := 1390270438235680807373243

theorem tailTrace_8122626 : CollatzResearch.WordTrace tailWord_8122626 prefixEnd_8122626 1390270438235680807373243 := by
  unfold tailWord_8122626
  simp only [CollatzResearch.WordTrace]
  refine ⟨74064127167780177730640933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197504339114080473948375821 74064127167780177730640933)
  ·
    refine ⟨13887023843958783324495175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74064127167780177730640933 13887023843958783324495175)
    ·
      refine ⟨20830535765938174986742763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13887023843958783324495175 20830535765938174986742763)
      ·
        refine ⟨31245803648907262480114145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20830535765938174986742763 31245803648907262480114145)
        ·
          refine ⟨23434352736680446860085609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31245803648907262480114145 23434352736680446860085609)
          ·
            refine ⟨17575764552510335145064207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23434352736680446860085609 17575764552510335145064207)
            ·
              refine ⟨26363646828765502717596311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17575764552510335145064207 26363646828765502717596311)
              ·
                refine ⟨39545470243148254076394467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26363646828765502717596311 39545470243148254076394467)
                ·
                  refine ⟨59318205364722381114591701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39545470243148254076394467 59318205364722381114591701)
                  ·
                    refine ⟨1390270438235680807373243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59318205364722381114591701 1390270438235680807373243)
                    ·
                      rfl

theorem cell23_8122626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_8122626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122626 prefixEnd_8122626 := by exact prefixLift 8122626
  have htrace : WordTrace (prefixWord ++ tailWord_8122626) baseStart_8122626 baseEnd_8122626 := by
    simpa [prefixWord, tailWord_8122626, baseEnd_8122626] using wordTrace_append hprefix tailTrace_8122626
  have hstable : (prefixWord ++ tailWord_8122626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122626).length < 2 ^ (prefixWord ++ tailWord_8122626).sum := by decide
  have hdescent : baseEnd_8122626 < baseStart_8122626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122629 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 2, 1, 4]
def baseStart_8122629 : Nat := 118140960795 + 8122629 * 2 ^ 59
def prefixEnd_8122629 : Nat := 4983230072969 + 3 ^ 40 * 8122629 * 2
def baseEnd_8122629 : Nat := 4170812855149005910382215

theorem tailTrace_8122629 : CollatzResearch.WordTrace tailWord_8122629 prefixEnd_8122629 4170812855149005910382215 := by
  unfold tailWord_8122629
  simp only [CollatzResearch.WordTrace]
  refine ⟨296256618090109842434922941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197504412060073228289948627 296256618090109842434922941)
  ·
    refine ⟨111096231783791190913096103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296256618090109842434922941 111096231783791190913096103)
    ·
      refine ⟨166644347675686786369644155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111096231783791190913096103 166644347675686786369644155)
      ·
        refine ⟨249966521513530179554466233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166644347675686786369644155 249966521513530179554466233)
        ·
          refine ⟨187474891135147634665849675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249966521513530179554466233 187474891135147634665849675)
          ·
            refine ⟨281212336702721451998774513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187474891135147634665849675 281212336702721451998774513)
            ·
              refine ⟨210909252527041088999080885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281212336702721451998774513 210909252527041088999080885)
              ·
                refine ⟨19772742424410102093663833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210909252527041088999080885 19772742424410102093663833)
                ·
                  refine ⟨14829556818307576570247875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19772742424410102093663833 14829556818307576570247875)
                  ·
                    refine ⟨22244335227461364855371813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14829556818307576570247875 22244335227461364855371813)
                    ·
                      refine ⟨4170812855149005910382215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22244335227461364855371813 4170812855149005910382215)
                      ·
                        rfl

theorem cell23_8122629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_8122629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122629 prefixEnd_8122629 := by exact prefixLift 8122629
  have htrace : WordTrace (prefixWord ++ tailWord_8122629) baseStart_8122629 baseEnd_8122629 := by
    simpa [prefixWord, tailWord_8122629, baseEnd_8122629] using wordTrace_append hprefix tailTrace_8122629
  have hstable : (prefixWord ++ tailWord_8122629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122629).length < 2 ^ (prefixWord ++ tailWord_8122629).sum := by decide
  have hdescent : baseEnd_8122629 < baseStart_8122629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122656 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 3, 4]
def baseStart_8122656 : Nat := 118140960795 + 8122656 * 2 ^ 59
def prefixEnd_8122656 : Nat := 4983230072969 + 3 ^ 40 * 8122656 * 2
def baseEnd_8122656 : Nat := 1390275573042225768248197

theorem tailTrace_8122656 : CollatzResearch.WordTrace tailWord_8122656 prefixEnd_8122656 1390275573042225768248197 := by
  unfold tailWord_8122656
  simp only [CollatzResearch.WordTrace]
  refine ⟨148128801430506013023077911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197505068574008017364103881 148128801430506013023077911)
  ·
    refine ⟨222193202145759019534616867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148128801430506013023077911 222193202145759019534616867)
    ·
      refine ⟨333289803218638529301925301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222193202145759019534616867 333289803218638529301925301)
      ·
        refine ⟨31245919051747362122055497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 333289803218638529301925301 31245919051747362122055497)
        ·
          refine ⟨23434439288810521591541623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31245919051747362122055497 23434439288810521591541623)
          ·
            refine ⟨35151658933215782387312435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23434439288810521591541623 35151658933215782387312435)
            ·
              refine ⟨52727488399823673580968653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35151658933215782387312435 52727488399823673580968653)
              ·
                refine ⟨19772808149933877592863245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52727488399823673580968653 19772808149933877592863245)
                ·
                  refine ⟨7414803056225204097323717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19772808149933877592863245 7414803056225204097323717)
                  ·
                    refine ⟨1390275573042225768248197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7414803056225204097323717 1390275573042225768248197)
                    ·
                      rfl

theorem cell23_8122656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 3, 4].length) (baseStart_8122656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122656 prefixEnd_8122656 := by exact prefixLift 8122656
  have htrace : WordTrace (prefixWord ++ tailWord_8122656) baseStart_8122656 baseEnd_8122656 := by
    simpa [prefixWord, tailWord_8122656, baseEnd_8122656] using wordTrace_append hprefix tailTrace_8122656
  have hstable : (prefixWord ++ tailWord_8122656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122656).length < 2 ^ (prefixWord ++ tailWord_8122656).sum := by decide
  have hdescent : baseEnd_8122656 < baseStart_8122656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122696 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 5, 1, 3]
def baseStart_8122696 : Nat := 118140960795 + 8122696 * 2 ^ 59
def prefixEnd_8122696 : Nat := 4983230072969 + 3 ^ 40 * 8122696 * 2
def baseEnd_8122696 : Nat := 4170847258352857148244407

theorem tailTrace_8122696 : CollatzResearch.WordTrace tailWord_8122696 prefixEnd_8122696 4170847258352857148244407 := by
  unfold tailWord_8122696
  simp only [CollatzResearch.WordTrace]
  refine ⟨148129530890433556438805971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197506041187244741918407961 148129530890433556438805971)
  ·
    refine ⟨222194296335650334658208957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148129530890433556438805971 222194296335650334658208957)
    ·
      refine ⟨83322861125868875496828359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222194296335650334658208957 83322861125868875496828359)
      ·
        refine ⟨124984291688803313245242539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83322861125868875496828359 124984291688803313245242539)
        ·
          refine ⟨187476437533204969867863809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124984291688803313245242539 187476437533204969867863809)
          ·
            refine ⟨140607328149903727400897857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187476437533204969867863809 140607328149903727400897857)
            ·
              refine ⟨105455496112427795550673393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140607328149903727400897857 105455496112427795550673393)
              ·
                refine ⟨79091622084320846663005045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105455496112427795550673393 79091622084320846663005045)
                ·
                  refine ⟨7414839570405079374656723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79091622084320846663005045 7414839570405079374656723)
                  ·
                    refine ⟨11122259355607619061985085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7414839570405079374656723 11122259355607619061985085)
                    ·
                      refine ⟨4170847258352857148244407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11122259355607619061985085 4170847258352857148244407)
                      ·
                        rfl

theorem cell23_8122696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_8122696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122696 prefixEnd_8122696 := by exact prefixLift 8122696
  have htrace : WordTrace (prefixWord ++ tailWord_8122696) baseStart_8122696 baseEnd_8122696 := by
    simpa [prefixWord, tailWord_8122696, baseEnd_8122696] using wordTrace_append hprefix tailTrace_8122696
  have hstable : (prefixWord ++ tailWord_8122696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122696).length < 2 ^ (prefixWord ++ tailWord_8122696).sum := by decide
  have hdescent : baseEnd_8122696 < baseStart_8122696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122720 : List Nat := [2, 1, 1, 3, 6, 1, 2, 1, 6]
def baseStart_8122720 : Nat := 118140960795 + 8122720 * 2 ^ 59
def prefixEnd_8122720 : Nat := 4983230072969 + 3 ^ 40 * 8122720 * 2
def baseEnd_8122720 : Nat := 463428842432062783816033

theorem tailTrace_8122720 : CollatzResearch.WordTrace tailWord_8122720 prefixEnd_8122720 463428842432062783816033 := by
  unfold tailWord_8122720
  simp only [CollatzResearch.WordTrace]
  refine ⟨148129968566390082488242807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197506624755186776650990409 148129968566390082488242807)
  ·
    refine ⟨222194952849585123732364211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148129968566390082488242807 222194952849585123732364211)
    ·
      refine ⟨333292429274377685598546317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222194952849585123732364211 333292429274377685598546317)
      ·
        refine ⟨124984660977891632099454869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333292429274377685598546317 124984660977891632099454869)
        ·
          refine ⟨5858655983338670254661947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 124984660977891632099454869 5858655983338670254661947)
          ·
            refine ⟨8787983975008005381992921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5858655983338670254661947 8787983975008005381992921)
            ·
              refine ⟨6590987981256004036494691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8787983975008005381992921 6590987981256004036494691)
              ·
                refine ⟨9886481971884006054742037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6590987981256004036494691 9886481971884006054742037)
                ·
                  refine ⟨463428842432062783816033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9886481971884006054742037 463428842432062783816033)
                  ·
                    rfl

theorem cell23_8122720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 6].length) (baseStart_8122720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122720 prefixEnd_8122720 := by exact prefixLift 8122720
  have htrace : WordTrace (prefixWord ++ tailWord_8122720) baseStart_8122720 baseEnd_8122720 := by
    simpa [prefixWord, tailWord_8122720, baseEnd_8122720] using wordTrace_append hprefix tailTrace_8122720
  have hstable : (prefixWord ++ tailWord_8122720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122720).length < 2 ^ (prefixWord ++ tailWord_8122720).sum := by decide
  have hdescent : baseEnd_8122720 < baseStart_8122720 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122729 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 1, 6]
def baseStart_8122729 : Nat := 118140960795 + 8122729 * 2 ^ 59
def prefixEnd_8122729 : Nat := 4983230072969 + 3 ^ 40 * 8122729 * 2
def baseEnd_8122729 : Nat := 1390288067738151839710585

theorem tailTrace_8122729 : CollatzResearch.WordTrace tailWord_8122729 prefixEnd_8122729 1390288067738151839710585 := by
  unfold tailWord_8122729
  simp only [CollatzResearch.WordTrace]
  refine ⟨296260265389747559513563241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197506843593165039675708827 296260265389747559513563241)
  ·
    refine ⟨222195199042310669635172431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296260265389747559513563241 222195199042310669635172431)
    ·
      refine ⟨333292798563466004452758647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222195199042310669635172431 333292798563466004452758647)
      ·
        refine ⟨499939197845199006679137971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333292798563466004452758647 499939197845199006679137971)
        ·
          refine ⟨749908796767798510018706957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499939197845199006679137971 749908796767798510018706957)
          ·
            refine ⟨281215798787924441257015109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 749908796767798510018706957 281215798787924441257015109)
            ·
              refine ⟨52727962272735832735690333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281215798787924441257015109 52727962272735832735690333)
              ·
                refine ⟨19772985852275937275883875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52727962272735832735690333 19772985852275937275883875)
                ·
                  refine ⟨29659478778413905913825813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19772985852275937275883875 29659478778413905913825813)
                  ·
                    refine ⟨1390288067738151839710585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29659478778413905913825813 1390288067738151839710585)
                    ·
                      rfl

theorem cell23_8122729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 6].length) (baseStart_8122729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122729 prefixEnd_8122729 := by exact prefixLift 8122729
  have htrace : WordTrace (prefixWord ++ tailWord_8122729) baseStart_8122729 baseEnd_8122729 := by
    simpa [prefixWord, tailWord_8122729, baseEnd_8122729] using wordTrace_append hprefix tailTrace_8122729
  have hstable : (prefixWord ++ tailWord_8122729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122729).length < 2 ^ (prefixWord ++ tailWord_8122729).sum := by decide
  have hdescent : baseEnd_8122729 < baseStart_8122729 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122736 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 4]
def baseStart_8122736 : Nat := 118140960795 + 8122736 * 2 ^ 59
def prefixEnd_8122736 : Nat := 4983230072969 + 3 ^ 40 * 8122736 * 2
def baseEnd_8122736 : Nat := 4170867797579036991744223

theorem tailTrace_8122736 : CollatzResearch.WordTrace tailWord_8122736 prefixEnd_8122736 4170867797579036991744223 := by
  unfold tailWord_8122736
  simp only [CollatzResearch.WordTrace]
  refine ⟨148130260350361099854534031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197507013800481466472712041 148130260350361099854534031)
  ·
    refine ⟨222195390525541649781801047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148130260350361099854534031 222195390525541649781801047)
    ·
      refine ⟨333293085788312474672701571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222195390525541649781801047 333293085788312474672701571)
      ·
        refine ⟨499939628682468712009052357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333293085788312474672701571 499939628682468712009052357)
        ·
          refine ⟨93738680377962883501697317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 499939628682468712009052357 93738680377962883501697317)
          ·
            refine ⟨17576002570868040656568247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93738680377962883501697317 17576002570868040656568247)
            ·
              refine ⟨26364003856302060984852371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17576002570868040656568247 26364003856302060984852371)
              ·
                refine ⟨39546005784453091477278557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26364003856302060984852371 39546005784453091477278557)
                ·
                  refine ⟨14829752169169909303979459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39546005784453091477278557 14829752169169909303979459)
                  ·
                    refine ⟨22244628253754863955969189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14829752169169909303979459 22244628253754863955969189)
                    ·
                      refine ⟨4170867797579036991744223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22244628253754863955969189 4170867797579036991744223)
                      ·
                        rfl

theorem cell23_8122736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 4].length) (baseStart_8122736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122736 prefixEnd_8122736 := by exact prefixLift 8122736
  have htrace : WordTrace (prefixWord ++ tailWord_8122736) baseStart_8122736 baseEnd_8122736 := by
    simpa [prefixWord, tailWord_8122736, baseEnd_8122736] using wordTrace_append hprefix tailTrace_8122736
  have hstable : (prefixWord ++ tailWord_8122736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122736).length < 2 ^ (prefixWord ++ tailWord_8122736).sum := by decide
  have hdescent : baseEnd_8122736 < baseStart_8122736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122739 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 3]
def baseStart_8122739 : Nat := 118140960795 + 8122739 * 2 ^ 59
def prefixEnd_8122739 : Nat := 4983230072969 + 3 ^ 40 * 8122739 * 2
def baseEnd_8122739 : Nat := 4170869338021000480006709

theorem tailTrace_8122739 : CollatzResearch.WordTrace tailWord_8122739 prefixEnd_8122739 4170869338021000480006709 := by
  unfold tailWord_8122739
  simp only [CollatzResearch.WordTrace]
  refine ⟨296260630119711331221427271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197507086746474220814284847 296260630119711331221427271)
  ·
    refine ⟨444390945179566996832140907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296260630119711331221427271 444390945179566996832140907)
    ·
      refine ⟨666586417769350495248211361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444390945179566996832140907 666586417769350495248211361)
      ·
        refine ⟨499939813327012871436158521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666586417769350495248211361 499939813327012871436158521)
        ·
          refine ⟨374954859995259653577118891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499939813327012871436158521 374954859995259653577118891)
          ·
            refine ⟨562432289992889480365678337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374954859995259653577118891 562432289992889480365678337)
            ·
              refine ⟨421824217494667110274258753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562432289992889480365678337 421824217494667110274258753)
              ·
                refine ⟨316368163121000332705694065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421824217494667110274258753 316368163121000332705694065)
                ·
                  refine ⟨237276122340750249529270549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316368163121000332705694065 237276122340750249529270549)
                  ·
                    refine ⟨11122318234722667946684557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 237276122340750249529270549 11122318234722667946684557)
                    ·
                      refine ⟨4170869338021000480006709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11122318234722667946684557 4170869338021000480006709)
                      ·
                        rfl

theorem cell23_8122739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 3].length) (baseStart_8122739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122739 prefixEnd_8122739 := by exact prefixLift 8122739
  have htrace : WordTrace (prefixWord ++ tailWord_8122739) baseStart_8122739 baseEnd_8122739 := by
    simpa [prefixWord, tailWord_8122739, baseEnd_8122739] using wordTrace_append hprefix tailTrace_8122739
  have hstable : (prefixWord ++ tailWord_8122739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122739).length < 2 ^ (prefixWord ++ tailWord_8122739).sum := by decide
  have hdescent : baseEnd_8122739 < baseStart_8122739 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122763 : List Nat := [1, 1, 1, 1, 4, 5, 2, 2, 2, 4]
def baseStart_8122763 : Nat := 118140960795 + 8122763 * 2 ^ 59
def prefixEnd_8122763 : Nat := 4983230072969 + 3 ^ 40 * 8122763 * 2
def baseEnd_8122763 : Nat := 1390293887185569462035533

theorem tailTrace_8122763 : CollatzResearch.WordTrace tailWord_8122763 prefixEnd_8122763 1390293887185569462035533 := by
  unfold tailWord_8122763
  simp only [CollatzResearch.WordTrace]
  refine ⟨296261505471624383320300943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197507670314416255546867295 296261505471624383320300943)
  ·
    refine ⟨444392258207436574980451415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296261505471624383320300943 444392258207436574980451415)
    ·
      refine ⟨666588387311154862470677123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444392258207436574980451415 666588387311154862470677123)
      ·
        refine ⟨999882580966732293706015685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666588387311154862470677123 999882580966732293706015685)
        ·
          refine ⟨187477983931262305069877941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 999882580966732293706015685 187477983931262305069877941)
          ·
            refine ⟨17576060993555841100301057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187477983931262305069877941 17576060993555841100301057)
            ·
              refine ⟨13182045745166880825225793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17576060993555841100301057 13182045745166880825225793)
              ·
                refine ⟨9886534308875160618919345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13182045745166880825225793 9886534308875160618919345)
                ·
                  refine ⟨7414900731656370464189509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9886534308875160618919345 7414900731656370464189509)
                  ·
                    refine ⟨1390293887185569462035533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7414900731656370464189509 1390293887185569462035533)
                    ·
                      rfl

theorem cell23_8122763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 4].length) (baseStart_8122763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122763 prefixEnd_8122763 := by exact prefixLift 8122763
  have htrace : WordTrace (prefixWord ++ tailWord_8122763) baseStart_8122763 baseEnd_8122763 := by
    simpa [prefixWord, tailWord_8122763, baseEnd_8122763] using wordTrace_append hprefix tailTrace_8122763
  have hstable : (prefixWord ++ tailWord_8122763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122763).length < 2 ^ (prefixWord ++ tailWord_8122763).sum := by decide
  have hdescent : baseEnd_8122763 < baseStart_8122763 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122776 : List Nat := [2, 1, 2, 5, 1, 1, 3, 8]
def baseStart_8122776 : Nat := 118140960795 + 8122776 * 2 ^ 59
def prefixEnd_8122776 : Nat := 4983230072969 + 3 ^ 40 * 8122776 * 2
def baseEnd_8122776 : Nat := 154477345807600623527557

theorem tailTrace_8122776 : CollatzResearch.WordTrace tailWord_8122776 prefixEnd_8122776 154477345807600623527557 := by
  unfold tailWord_8122776
  simp only [CollatzResearch.WordTrace]
  refine ⟨148130989810288643270262091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197507986413718191027016121 148130989810288643270262091)
  ·
    refine ⟨222196484715432964905393137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148130989810288643270262091 222196484715432964905393137)
    ·
      refine ⟨166647363536574723679044853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222196484715432964905393137 166647363536574723679044853)
      ·
        refine ⟨15623190331553880344910455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166647363536574723679044853 15623190331553880344910455)
        ·
          refine ⟨23434785497330820517365683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15623190331553880344910455 23434785497330820517365683)
          ·
            refine ⟨35152178245996230776048525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23434785497330820517365683 35152178245996230776048525)
            ·
              refine ⟨13182066842248586541018197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35152178245996230776048525 13182066842248586541018197)
              ·
                refine ⟨154477345807600623527557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13182066842248586541018197 154477345807600623527557)
                ·
                  rfl

theorem cell23_8122776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 8].length) (baseStart_8122776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122776 prefixEnd_8122776 := by exact prefixLift 8122776
  have htrace : WordTrace (prefixWord ++ tailWord_8122776) baseStart_8122776 baseEnd_8122776 := by
    simpa [prefixWord, tailWord_8122776, baseEnd_8122776] using wordTrace_append hprefix tailTrace_8122776
  have hstable : (prefixWord ++ tailWord_8122776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122776).length < 2 ^ (prefixWord ++ tailWord_8122776).sum := by decide
  have hdescent : baseEnd_8122776 < baseStart_8122776 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122789 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 2, 7]
def baseStart_8122789 : Nat := 118140960795 + 8122789 * 2 ^ 59
def prefixEnd_8122789 : Nat := 4983230072969 + 3 ^ 40 * 8122789 * 2
def baseEnd_8122789 : Nat := 1390298337351241761460493

theorem tailTrace_8122789 : CollatzResearch.WordTrace tailWord_8122789 prefixEnd_8122789 1390298337351241761460493 := by
  unfold tailWord_8122789
  simp only [CollatzResearch.WordTrace]
  refine ⟨296262453769530189760747421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197508302513020126507164947 296262453769530189760747421)
  ·
    refine ⟨111098420163573821160280283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296262453769530189760747421 111098420163573821160280283)
    ·
      refine ⟨166647630245360731740420425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111098420163573821160280283 166647630245360731740420425)
      ·
        refine ⟨124985722684020548805315319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166647630245360731740420425 124985722684020548805315319)
        ·
          refine ⟨187478584026030823207972979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124985722684020548805315319 187478584026030823207972979)
          ·
            refine ⟨281217876039046234811959469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187478584026030823207972979 281217876039046234811959469)
            ·
              refine ⟨105456703514642338054484801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281217876039046234811959469 105456703514642338054484801)
              ·
                refine ⟨79092527635981753540863601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105456703514642338054484801 79092527635981753540863601)
                ·
                  refine ⟨59319395726986315155647701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79092527635981753540863601 59319395726986315155647701)
                  ·
                    refine ⟨1390298337351241761460493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59319395726986315155647701 1390298337351241761460493)
                    ·
                      rfl

theorem cell23_8122789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_8122789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122789 prefixEnd_8122789 := by exact prefixLift 8122789
  have htrace : WordTrace (prefixWord ++ tailWord_8122789) baseStart_8122789 baseEnd_8122789 := by
    simpa [prefixWord, tailWord_8122789, baseEnd_8122789] using wordTrace_append hprefix tailTrace_8122789
  have hstable : (prefixWord ++ tailWord_8122789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122789).length < 2 ^ (prefixWord ++ tailWord_8122789).sum := by decide
  have hdescent : baseEnd_8122789 < baseStart_8122789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122837 : List Nat := [1, 3, 2, 3, 1, 3, 3, 1, 2, 1, 3]
def baseStart_8122837 : Nat := 118140960795 + 8122837 * 2 ^ 59
def prefixEnd_8122837 : Nat := 4983230072969 + 3 ^ 40 * 8122837 * 2
def baseEnd_8122837 : Nat := 4170919659125141096581259

theorem tailTrace_8122837 : CollatzResearch.WordTrace tailWord_8122837 prefixEnd_8122837 4170919659125141096581259 := by
  unfold tailWord_8122837
  simp only [CollatzResearch.WordTrace]
  refine ⟨296264204473356293958494765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197509469648904195972329843 296264204473356293958494765)
  ·
    refine ⟨111099076677508610234435537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296264204473356293958494765 111099076677508610234435537)
    ·
      refine ⟨83324307508131457675826653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111099076677508610234435537 83324307508131457675826653)
      ·
        refine ⟨31246615315549296628434995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83324307508131457675826653 31246615315549296628434995)
        ·
          refine ⟨46869922973323944942652493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31246615315549296628434995 46869922973323944942652493)
          ·
            refine ⟨17576221114996479353494685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46869922973323944942652493 17576221114996479353494685)
            ·
              refine ⟨6591082918123679757560507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17576221114996479353494685 6591082918123679757560507)
              ·
                refine ⟨9886624377185519636340761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6591082918123679757560507 9886624377185519636340761)
                ·
                  refine ⟨7414968282889139727255571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9886624377185519636340761 7414968282889139727255571)
                  ·
                    refine ⟨11122452424333709590883357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7414968282889139727255571 11122452424333709590883357)
                    ·
                      refine ⟨4170919659125141096581259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11122452424333709590883357 4170919659125141096581259)
                      ·
                        rfl

theorem cell23_8122837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_8122837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122837 prefixEnd_8122837 := by exact prefixLift 8122837
  have htrace : WordTrace (prefixWord ++ tailWord_8122837) baseStart_8122837 baseEnd_8122837 := by
    simpa [prefixWord, tailWord_8122837, baseEnd_8122837] using wordTrace_append hprefix tailTrace_8122837
  have hstable : (prefixWord ++ tailWord_8122837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122837).length < 2 ^ (prefixWord ++ tailWord_8122837).sum := by decide
  have hdescent : baseEnd_8122837 < baseStart_8122837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122894 : List Nat := [4, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2]
def baseStart_8122894 : Nat := 118140960795 + 8122894 * 2 ^ 59
def prefixEnd_8122894 : Nat := 4983230072969 + 3 ^ 40 * 8122894 * 2
def baseEnd_8122894 : Nat := 4170948927522447373568497

theorem tailTrace_8122894 : CollatzResearch.WordTrace tailWord_8122894 prefixEnd_8122894 4170948927522447373568497 := by
  unfold tailWord_8122894
  simp only [CollatzResearch.WordTrace]
  refine ⟨37033285429268724086664967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197510855622766528462213157 37033285429268724086664967)
  ·
    refine ⟨55549928143903086129997451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37033285429268724086664967 55549928143903086129997451)
    ·
      refine ⟨83324892215854629194996177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55549928143903086129997451 83324892215854629194996177)
      ·
        refine ⟨62493669161890971896247133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83324892215854629194996177 62493669161890971896247133)
        ·
          refine ⟨23435125935709114461092675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62493669161890971896247133 23435125935709114461092675)
          ·
            refine ⟨35152688903563671691639013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23435125935709114461092675 35152688903563671691639013)
            ·
              refine ⟨6591129169418188442182315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35152688903563671691639013 6591129169418188442182315)
              ·
                refine ⟨9886693754127282663273473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6591129169418188442182315 9886693754127282663273473)
                ·
                  refine ⟨7415020315595461997455105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9886693754127282663273473 7415020315595461997455105)
                  ·
                    refine ⟨5561265236696596498091329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7415020315595461997455105 5561265236696596498091329)
                    ·
                      refine ⟨4170948927522447373568497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5561265236696596498091329 4170948927522447373568497)
                      ·
                        rfl

theorem cell23_8122894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_8122894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122894 prefixEnd_8122894 := by exact prefixLift 8122894
  have htrace : WordTrace (prefixWord ++ tailWord_8122894) baseStart_8122894 baseEnd_8122894 := by
    simpa [prefixWord, tailWord_8122894, baseEnd_8122894] using wordTrace_append hprefix tailTrace_8122894
  have hstable : (prefixWord ++ tailWord_8122894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122894).length < 2 ^ (prefixWord ++ tailWord_8122894).sum := by decide
  have hdescent : baseEnd_8122894 < baseStart_8122894 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122913 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 2, 5]
def baseStart_8122913 : Nat := 118140960795 + 8122913 * 2 ^ 59
def prefixEnd_8122913 : Nat := 4983230072969 + 3 ^ 40 * 8122913 * 2
def baseEnd_8122913 : Nat := 1390319561218294266410303

theorem tailTrace_8122913 : CollatzResearch.WordTrace tailWord_8122913 prefixEnd_8122913 1390319561218294266410303 := by
  unfold tailWord_8122913
  simp only [CollatzResearch.WordTrace]
  refine ⟨296266976421080958938261393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197511317614053972625507595 296266976421080958938261393)
  ·
    refine ⟨222200232315810719203696045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296266976421080958938261393 222200232315810719203696045)
    ·
      refine ⟨83325087118429019701386017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222200232315810719203696045 83325087118429019701386017)
      ·
        refine ⟨62493815338821764776039513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83325087118429019701386017 62493815338821764776039513)
        ·
          refine ⟨46870361504116323582029635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62493815338821764776039513 46870361504116323582029635)
          ·
            refine ⟨70305542256174485373044453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46870361504116323582029635 70305542256174485373044453)
            ·
              refine ⟨13182289173032716007445835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70305542256174485373044453 13182289173032716007445835)
              ·
                refine ⟨19773433759549074011168753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13182289173032716007445835 19773433759549074011168753)
                ·
                  refine ⟨14830075319661805508376565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19773433759549074011168753 14830075319661805508376565)
                  ·
                    refine ⟨1390319561218294266410303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14830075319661805508376565 1390319561218294266410303)
                    ·
                      rfl

theorem cell23_8122913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_8122913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122913 prefixEnd_8122913 := by exact prefixLift 8122913
  have htrace : WordTrace (prefixWord ++ tailWord_8122913) baseStart_8122913 baseEnd_8122913 := by
    simpa [prefixWord, tailWord_8122913, baseEnd_8122913] using wordTrace_append hprefix tailTrace_8122913
  have hstable : (prefixWord ++ tailWord_8122913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122913).length < 2 ^ (prefixWord ++ tailWord_8122913).sum := by decide
  have hdescent : baseEnd_8122913 < baseStart_8122913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122933 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_8122933 : Nat := 118140960795 + 8122933 * 2 ^ 59
def prefixEnd_8122933 : Nat := 4983230072969 + 3 ^ 40 * 8122933 * 2
def baseEnd_8122933 : Nat := 4170968953267972720980817

theorem tailTrace_8122933 : CollatzResearch.WordTrace tailWord_8122933 prefixEnd_8122933 4170968953267972720980817 := by
  unfold tailWord_8122933
  simp only [CollatzResearch.WordTrace]
  refine ⟨296267705881008502353989453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197511803920672334902659635 296267705881008502353989453)
  ·
    refine ⟨111100389705378188382746045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296267705881008502353989453 111100389705378188382746045)
    ·
      refine ⟨41662646139516820643529767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111100389705378188382746045 41662646139516820643529767)
      ·
        refine ⟨62493969209275230965294651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41662646139516820643529767 62493969209275230965294651)
        ·
          refine ⟨93740953813912846447941977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62493969209275230965294651 93740953813912846447941977)
          ·
            refine ⟨70305715360434634835956483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93740953813912846447941977 70305715360434634835956483)
            ·
              refine ⟨105458573040651952253934725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70305715360434634835956483 105458573040651952253934725)
              ·
                refine ⟨19773482445122241047612761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105458573040651952253934725 19773482445122241047612761)
                ·
                  refine ⟨14830111833841680785709571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19773482445122241047612761 14830111833841680785709571)
                  ·
                    refine ⟨22245167750762521178564357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14830111833841680785709571 22245167750762521178564357)
                    ·
                      refine ⟨4170968953267972720980817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22245167750762521178564357 4170968953267972720980817)
                      ·
                        rfl

theorem cell23_8122933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_8122933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122933 prefixEnd_8122933 := by exact prefixLift 8122933
  have htrace : WordTrace (prefixWord ++ tailWord_8122933) baseStart_8122933 baseEnd_8122933 := by
    simpa [prefixWord, tailWord_8122933, baseEnd_8122933] using wordTrace_append hprefix tailTrace_8122933
  have hstable : (prefixWord ++ tailWord_8122933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122933).length < 2 ^ (prefixWord ++ tailWord_8122933).sum := by decide
  have hdescent : baseEnd_8122933 < baseStart_8122933 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122934 : List Nat := [5, 1, 2, 1, 2, 3, 2, 2, 5]
def baseStart_8122934 : Nat := 118140960795 + 8122934 * 2 ^ 59
def prefixEnd_8122934 : Nat := 4983230072969 + 3 ^ 40 * 8122934 * 2
def baseEnd_8122934 : Nat := 463441051860958579674257

theorem tailTrace_8122934 : CollatzResearch.WordTrace tailWord_8122934 prefixEnd_8122934 463441051860958579674257 := by
  unfold tailWord_8122934
  simp only [CollatzResearch.WordTrace]
  refine ⟨18516733897125304970298491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197511828236003253016517237 18516733897125304970298491)
  ·
    refine ⟨27775100845687957455447737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18516733897125304970298491 27775100845687957455447737)
    ·
      refine ⟨20831325634265968091585803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27775100845687957455447737 20831325634265968091585803)
      ·
        refine ⟨31246988451398952137378705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20831325634265968091585803 31246988451398952137378705)
        ·
          refine ⟨23435241338549214103034029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31246988451398952137378705 23435241338549214103034029)
          ·
            refine ⟨8788215501955955288637761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23435241338549214103034029 8788215501955955288637761)
            ·
              refine ⟨6591161626466966466478321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8788215501955955288637761 6591161626466966466478321)
              ·
                refine ⟨4943371219850224849858741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6591161626466966466478321 4943371219850224849858741)
                ·
                  refine ⟨463441051860958579674257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4943371219850224849858741 463441051860958579674257)
                  ·
                    rfl

theorem cell23_8122934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_8122934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122934 prefixEnd_8122934 := by exact prefixLift 8122934
  have htrace : WordTrace (prefixWord ++ tailWord_8122934) baseStart_8122934 baseEnd_8122934 := by
    simpa [prefixWord, tailWord_8122934, baseEnd_8122934] using wordTrace_append hprefix tailTrace_8122934
  have hstable : (prefixWord ++ tailWord_8122934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122934).length < 2 ^ (prefixWord ++ tailWord_8122934).sum := by decide
  have hdescent : baseEnd_8122934 < baseStart_8122934 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122936 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 2, 3, 5]
def baseStart_8122936 : Nat := 118140960795 + 8122936 * 2 ^ 59
def prefixEnd_8122936 : Nat := 4983230072969 + 3 ^ 40 * 8122936 * 2
def baseEnd_8122936 : Nat := 4170970493709936209243303

theorem tailTrace_8122936 : CollatzResearch.WordTrace tailWord_8122936 prefixEnd_8122936 4170970493709936209243303 := by
  unfold tailWord_8122936
  simp only [CollatzResearch.WordTrace]
  refine ⟨148133907649998816933174331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197511876866665089244232441 148133907649998816933174331)
  ·
    refine ⟨222200861474998225399761497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148133907649998816933174331 222200861474998225399761497)
    ·
      refine ⟨166650646106248669049821123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222200861474998225399761497 166650646106248669049821123)
      ·
        refine ⟨249975969159373003574731685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166650646106248669049821123 249975969159373003574731685)
        ·
          refine ⟨46870494217382438170262191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249975969159373003574731685 46870494217382438170262191)
          ·
            refine ⟨70305741326073657255393287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46870494217382438170262191 70305741326073657255393287)
            ·
              refine ⟨105458611989110485883089931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70305741326073657255393287 105458611989110485883089931)
              ·
                refine ⟨158187917983665728824634897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105458611989110485883089931 158187917983665728824634897)
                ·
                  refine ⟨118640938487749296618476173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158187917983665728824634897 118640938487749296618476173)
                  ·
                    refine ⟨44490351932905986231928565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118640938487749296618476173 44490351932905986231928565)
                    ·
                      refine ⟨4170970493709936209243303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44490351932905986231928565 4170970493709936209243303)
                      ·
                        rfl

theorem cell23_8122936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_8122936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122936 prefixEnd_8122936 := by exact prefixLift 8122936
  have htrace : WordTrace (prefixWord ++ tailWord_8122936) baseStart_8122936 baseEnd_8122936 := by
    simpa [prefixWord, tailWord_8122936, baseEnd_8122936] using wordTrace_append hprefix tailTrace_8122936
  have hstable : (prefixWord ++ tailWord_8122936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122936).length < 2 ^ (prefixWord ++ tailWord_8122936).sum := by decide
  have hdescent : baseEnd_8122936 < baseStart_8122936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122943 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 3, 4]
def baseStart_8122943 : Nat := 118140960795 + 8122943 * 2 ^ 59
def prefixEnd_8122943 : Nat := 4983230072969 + 3 ^ 40 * 8122943 * 2
def baseEnd_8122943 : Nat := 1390324696024839227285257

theorem tailTrace_8122943 : CollatzResearch.WordTrace tailWord_8122943 prefixEnd_8122943 1390324696024839227285257 := by
  unfold tailWord_8122943
  simp only [CollatzResearch.WordTrace]
  refine ⟨296268070610972274061853483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197512047073981516041235655 296268070610972274061853483)
  ·
    refine ⟨444402105916458411092780225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296268070610972274061853483 444402105916458411092780225)
    ·
      refine ⟨333301579437343808319585169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444402105916458411092780225 333301579437343808319585169)
      ·
        refine ⟨249976184578007856239688877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333301579437343808319585169 249976184578007856239688877)
        ·
          refine ⟨93741069216752946089883329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249976184578007856239688877 93741069216752946089883329)
          ·
            refine ⟨70305801912564709567412497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93741069216752946089883329 70305801912564709567412497)
            ·
              refine ⟨52729351434423532175559373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70305801912564709567412497 52729351434423532175559373)
              ·
                refine ⟨19773506787908824565834765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52729351434423532175559373 19773506787908824565834765)
                ·
                  refine ⟨7415065045465809212188037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19773506787908824565834765 7415065045465809212188037)
                  ·
                    refine ⟨1390324696024839227285257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7415065045465809212188037 1390324696024839227285257)
                    ·
                      rfl

theorem cell23_8122943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 4].length) (baseStart_8122943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122943 prefixEnd_8122943 := by exact prefixLift 8122943
  have htrace : WordTrace (prefixWord ++ tailWord_8122943) baseStart_8122943 baseEnd_8122943 := by
    simpa [prefixWord, tailWord_8122943, baseEnd_8122943] using wordTrace_append hprefix tailTrace_8122943
  have hstable : (prefixWord ++ tailWord_8122943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122943).length < 2 ^ (prefixWord ++ tailWord_8122943).sum := by decide
  have hdescent : baseEnd_8122943 < baseStart_8122943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122977 : List Nat := [1, 2, 3, 1, 1, 5, 2, 3, 1, 4]
def baseStart_8122977 : Nat := 118140960795 + 8122977 * 2 ^ 59
def prefixEnd_8122977 : Nat := 4983230072969 + 3 ^ 40 * 8122977 * 2
def baseEnd_8122977 : Nat := 1390330515472256849610205

theorem tailTrace_8122977 : CollatzResearch.WordTrace tailWord_8122977 prefixEnd_8122977 1390330515472256849610205 := by
  unfold tailWord_8122977
  simp only [CollatzResearch.WordTrace]
  refine ⟨296269310692849097868591185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197512873795232731912394123 296269310692849097868591185)
  ·
    refine ⟨222201983019636823401443389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296269310692849097868591185 222201983019636823401443389)
    ·
      refine ⟨83325743632363808775541271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222201983019636823401443389 83325743632363808775541271)
      ·
        refine ⟨124988615448545713163311907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83325743632363808775541271 124988615448545713163311907)
        ·
          refine ⟨187482923172818569744967861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124988615448545713163311907 187482923172818569744967861)
          ·
            refine ⟨17576524047451740913590737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187482923172818569744967861 17576524047451740913590737)
            ·
              refine ⟨13182393035588805685193053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17576524047451740913590737 13182393035588805685193053)
              ·
                refine ⟨4943397388345802131947395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13182393035588805685193053 4943397388345802131947395)
                ·
                  refine ⟨7415096082518703197921093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4943397388345802131947395 7415096082518703197921093)
                  ·
                    refine ⟨1390330515472256849610205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7415096082518703197921093 1390330515472256849610205)
                    ·
                      rfl

theorem cell23_8122977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_8122977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122977 prefixEnd_8122977 := by exact prefixLift 8122977
  have htrace : WordTrace (prefixWord ++ tailWord_8122977) baseStart_8122977 baseEnd_8122977 := by
    simpa [prefixWord, tailWord_8122977, baseEnd_8122977] using wordTrace_append hprefix tailTrace_8122977
  have hstable : (prefixWord ++ tailWord_8122977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122977).length < 2 ^ (prefixWord ++ tailWord_8122977).sum := by decide
  have hdescent : baseEnd_8122977 < baseStart_8122977 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8122990 : List Nat := [4, 1, 2, 2, 2, 1, 3, 2, 6]
def baseStart_8122990 : Nat := 118140960795 + 8122990 * 2 ^ 59
def prefixEnd_8122990 : Nat := 4983230072969 + 3 ^ 40 * 8122990 * 2
def baseEnd_8122990 : Nat := 463444246851697666440895

theorem tailTrace_8122990 : CollatzResearch.WordTrace tailWord_8122990 prefixEnd_8122990 463444246851697666440895 := by
  unfold tailWord_8122990
  simp only [CollatzResearch.WordTrace]
  refine ⟨37033723105225250136101803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197513189894534667392542949 37033723105225250136101803)
  ·
    refine ⟨55550584657837875204152705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37033723105225250136101803 55550584657837875204152705)
    ·
      refine ⟨41662938493378406403114529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55550584657837875204152705 41662938493378406403114529)
      ·
        refine ⟨31247203870033804802335897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41662938493378406403114529 31247203870033804802335897)
        ·
          refine ⟨23435402902525353601751923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31247203870033804802335897 23435402902525353601751923)
          ·
            refine ⟨35153104353788030402627885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23435402902525353601751923 35153104353788030402627885)
            ·
              refine ⟨13182414132670511400985457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35153104353788030402627885 13182414132670511400985457)
              ·
                refine ⟨9886810599502883550739093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13182414132670511400985457 9886810599502883550739093)
                ·
                  refine ⟨463444246851697666440895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9886810599502883550739093 463444246851697666440895)
                  ·
                    rfl

theorem cell23_8122990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_8122990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8122990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8122990 prefixEnd_8122990 := by exact prefixLift 8122990
  have htrace : WordTrace (prefixWord ++ tailWord_8122990) baseStart_8122990 baseEnd_8122990 := by
    simpa [prefixWord, tailWord_8122990, baseEnd_8122990] using wordTrace_append hprefix tailTrace_8122990
  have hstable : (prefixWord ++ tailWord_8122990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8122990).length < 2 ^ (prefixWord ++ tailWord_8122990).sum := by decide
  have hdescent : baseEnd_8122990 < baseStart_8122990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8122990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123033 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 6, 4]
def baseStart_8123033 : Nat := 118140960795 + 8123033 * 2 ^ 59
def prefixEnd_8123033 : Nat := 4983230072969 + 3 ^ 40 * 8123033 * 2
def baseEnd_8123033 : Nat := 1390340100444474109910119

theorem tailTrace_8123033 : CollatzResearch.WordTrace tailWord_8123033 prefixEnd_8123033 1390340100444474109910119 := by
  unfold tailWord_8123033
  simp only [CollatzResearch.WordTrace]
  refine ⟨296271353180646219432629753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197514235453764146288419835 296271353180646219432629753)
  ·
    refine ⟨222203514885484664574472315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296271353180646219432629753 222203514885484664574472315)
    ·
      refine ⟨333305272328226996861708473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222203514885484664574472315 333305272328226996861708473)
      ·
        refine ⟨249978954246170247646281355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333305272328226996861708473 249978954246170247646281355)
        ·
          refine ⟨374968431369255371469422033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249978954246170247646281355 374968431369255371469422033)
          ·
            refine ⟨281226323526941528602066525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374968431369255371469422033 281226323526941528602066525)
            ·
              refine ⟨105459871322603073225774947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281226323526941528602066525 105459871322603073225774947)
              ·
                refine ⟨158189806983904609838662421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105459871322603073225774947 158189806983904609838662421)
                ·
                  refine ⟨7415147202370528586187301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158189806983904609838662421 7415147202370528586187301)
                  ·
                    refine ⟨1390340100444474109910119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7415147202370528586187301 1390340100444474109910119)
                    ·
                      rfl

theorem cell23_8123033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 4].length) (baseStart_8123033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123033 prefixEnd_8123033 := by exact prefixLift 8123033
  have htrace : WordTrace (prefixWord ++ tailWord_8123033) baseStart_8123033 baseEnd_8123033 := by
    simpa [prefixWord, tailWord_8123033, baseEnd_8123033] using wordTrace_append hprefix tailTrace_8123033
  have hstable : (prefixWord ++ tailWord_8123033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123033).length < 2 ^ (prefixWord ++ tailWord_8123033).sum := by decide
  have hdescent : baseEnd_8123033 < baseStart_8123033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123070 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_8123070 : Nat := 118140960795 + 8123070 * 2 ^ 59
def prefixEnd_8123070 : Nat := 4983230072969 + 3 ^ 40 * 8123070 * 2
def baseEnd_8123070 : Nat := 4171039300117638684967687

theorem tailTrace_8123070 : CollatzResearch.WordTrace tailWord_8123070 prefixEnd_8123070 4171039300117638684967687 := by
  unfold tailWord_8123070
  simp only [CollatzResearch.WordTrace]
  refine ⟨37034087835189021843965833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197515135121008116501151109 37034087835189021843965833)
  ·
    refine ⟨27775565876391766382974375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37034087835189021843965833 27775565876391766382974375)
    ·
      refine ⟨41663348814587649574461563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27775565876391766382974375 41663348814587649574461563)
      ·
        refine ⟨62495023221881474361692345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41663348814587649574461563 62495023221881474361692345)
        ·
          refine ⟨46871267416411105771269259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62495023221881474361692345 46871267416411105771269259)
          ·
            refine ⟨70306901124616658656903889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46871267416411105771269259 70306901124616658656903889)
            ·
              refine ⟨52730175843462493992677917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70306901124616658656903889 52730175843462493992677917)
              ·
                refine ⟨19773815941298435247254219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52730175843462493992677917 19773815941298435247254219)
                ·
                  refine ⟨29660723911947652870881329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19773815941298435247254219 29660723911947652870881329)
                  ·
                    refine ⟨22245542933960739653160997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29660723911947652870881329 22245542933960739653160997)
                    ·
                      refine ⟨4171039300117638684967687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22245542933960739653160997 4171039300117638684967687)
                      ·
                        rfl

theorem cell23_8123070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_8123070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123070 prefixEnd_8123070 := by exact prefixLift 8123070
  have htrace : WordTrace (prefixWord ++ tailWord_8123070) baseStart_8123070 baseEnd_8123070 := by
    simpa [prefixWord, tailWord_8123070, baseEnd_8123070] using wordTrace_append hprefix tailTrace_8123070
  have hstable : (prefixWord ++ tailWord_8123070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123070).length < 2 ^ (prefixWord ++ tailWord_8123070).sum := by decide
  have hdescent : baseEnd_8123070 < baseStart_8123070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123078 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_8123078 : Nat := 118140960795 + 8123078 * 2 ^ 59
def prefixEnd_8123078 : Nat := 4983230072969 + 3 ^ 40 * 8123078 * 2
def baseEnd_8123078 : Nat := 4171043407962874653667651

theorem tailTrace_8123078 : CollatzResearch.WordTrace tailWord_8123078 prefixEnd_8123078 4171043407962874653667651 := by
  unfold tailWord_8123078
  simp only [CollatzResearch.WordTrace]
  refine ⟨9258531077046349753688059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 197515329643655461412011925 9258531077046349753688059)
  ·
    refine ⟨13887796615569524630532089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9258531077046349753688059 13887796615569524630532089)
    ·
      refine ⟨10415847461677143472899067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13887796615569524630532089 10415847461677143472899067)
      ·
        refine ⟨15623771192515715209348601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10415847461677143472899067 15623771192515715209348601)
        ·
          refine ⟨11717828394386786407011451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15623771192515715209348601 11717828394386786407011451)
          ·
            refine ⟨17576742591580179610517177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11717828394386786407011451 17576742591580179610517177)
            ·
              refine ⟨13182556943685134707887883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17576742591580179610517177 13182556943685134707887883)
              ·
                refine ⟨19773835415527702061831825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13182556943685134707887883 19773835415527702061831825)
                ·
                  refine ⟨14830376561645776546373869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19773835415527702061831825 14830376561645776546373869)
                  ·
                    refine ⟨5561391210617166204890201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14830376561645776546373869 5561391210617166204890201)
                    ·
                      refine ⟨4171043407962874653667651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5561391210617166204890201 4171043407962874653667651)
                      ·
                        rfl

theorem cell23_8123078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_8123078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123078 prefixEnd_8123078 := by exact prefixLift 8123078
  have htrace : WordTrace (prefixWord ++ tailWord_8123078) baseStart_8123078 baseEnd_8123078 := by
    simpa [prefixWord, tailWord_8123078, baseEnd_8123078] using wordTrace_append hprefix tailTrace_8123078
  have hstable : (prefixWord ++ tailWord_8123078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123078).length < 2 ^ (prefixWord ++ tailWord_8123078).sum := by decide
  have hdescent : baseEnd_8123078 < baseStart_8123078 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123108 : List Nat := [2, 3, 1, 1, 1, 6, 2, 2, 1, 2, 2]
def baseStart_8123108 : Nat := 118140960795 + 8123108 * 2 ^ 59
def prefixEnd_8123108 : Nat := 4983230072969 + 3 ^ 40 * 8123108 * 2
def baseEnd_8123108 : Nat := 4171058812382509536292513

theorem tailTrace_8123108 : CollatzResearch.WordTrace tailWord_8123108 prefixEnd_8123108 4171058812382509536292513 := by
  unfold tailWord_8123108
  simp only [CollatzResearch.WordTrace]
  refine ⟨148137044327687253620804989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197516059103583004827739985 148137044327687253620804989)
  ·
    refine ⟨55551391622882720107801871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148137044327687253620804989 55551391622882720107801871)
    ·
      refine ⟨83327087434324080161702807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55551391622882720107801871 83327087434324080161702807)
      ·
        refine ⟨124990631151486120242554211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83327087434324080161702807 124990631151486120242554211)
        ·
          refine ⟨187485946727229180363831317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124990631151486120242554211 187485946727229180363831317)
          ·
            refine ⟨8788403752838867829554593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187485946727229180363831317 8788403752838867829554593)
            ·
              refine ⟨6591302814629150872165945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8788403752838867829554593 6591302814629150872165945)
              ·
                refine ⟨4943477110971863154124459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6591302814629150872165945 4943477110971863154124459)
                ·
                  refine ⟨7415215666457794731186689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4943477110971863154124459 7415215666457794731186689)
                  ·
                    refine ⟨5561411749843346048390017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7415215666457794731186689 5561411749843346048390017)
                    ·
                      refine ⟨4171058812382509536292513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5561411749843346048390017 4171058812382509536292513)
                      ·
                        rfl

theorem cell23_8123108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_8123108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123108 prefixEnd_8123108 := by exact prefixLift 8123108
  have htrace : WordTrace (prefixWord ++ tailWord_8123108) baseStart_8123108 baseEnd_8123108 := by
    simpa [prefixWord, tailWord_8123108, baseEnd_8123108] using wordTrace_append hprefix tailTrace_8123108
  have hstable : (prefixWord ++ tailWord_8123108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123108).length < 2 ^ (prefixWord ++ tailWord_8123108).sum := by decide
  have hdescent : baseEnd_8123108 < baseStart_8123108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123113 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 2, 3, 4]
def baseStart_8123113 : Nat := 118140960795 + 8123113 * 2 ^ 59
def prefixEnd_8123113 : Nat := 4983230072969 + 3 ^ 40 * 8123113 * 2
def baseEnd_8123113 : Nat := 4171061379785782016729989

theorem tailTrace_8123113 : CollatzResearch.WordTrace tailWord_8123113 prefixEnd_8123113 4171061379785782016729989 := by
  unfold tailWord_8123113
  simp only [CollatzResearch.WordTrace]
  refine ⟨296274271020356393095541993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197516180680237595397027995 296274271020356393095541993)
  ·
    refine ⟨222205703265267294821656495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296274271020356393095541993 222205703265267294821656495)
    ·
      refine ⟨333308554897900942232484743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222205703265267294821656495 333308554897900942232484743)
      ·
        refine ⟨499962832346851413348727115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333308554897900942232484743 499962832346851413348727115)
        ·
          refine ⟨749944248520277120023090673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499962832346851413348727115 749944248520277120023090673)
          ·
            refine ⟨562458186390207840017318005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 749944248520277120023090673 562458186390207840017318005)
            ·
              refine ⟨52730454974081985001623563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 562458186390207840017318005 52730454974081985001623563)
              ·
                refine ⟨79095682461122977502435345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52730454974081985001623563 79095682461122977502435345)
                ·
                  refine ⟨59321761845842233126826509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79095682461122977502435345 59321761845842233126826509)
                  ·
                    refine ⟨22245660692190837422559941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59321761845842233126826509 22245660692190837422559941)
                    ·
                      refine ⟨4171061379785782016729989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22245660692190837422559941 4171061379785782016729989)
                      ·
                        rfl

theorem cell23_8123113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_8123113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123113 prefixEnd_8123113 := by exact prefixLift 8123113
  have htrace : WordTrace (prefixWord ++ tailWord_8123113) baseStart_8123113 baseEnd_8123113 := by
    simpa [prefixWord, tailWord_8123113, baseEnd_8123113] using wordTrace_append hprefix tailTrace_8123113
  have hstable : (prefixWord ++ tailWord_8123113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123113).length < 2 ^ (prefixWord ++ tailWord_8123113).sum := by decide
  have hdescent : baseEnd_8123113 < baseStart_8123113 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123117 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 5, 3, 2]
def baseStart_8123117 : Nat := 118140960795 + 8123117 * 2 ^ 59
def prefixEnd_8123117 : Nat := 4983230072969 + 3 ^ 40 * 8123117 * 2
def baseEnd_8123117 : Nat := 4171063433708400001079971

theorem tailTrace_8123117 : CollatzResearch.WordTrace tailWord_8123117 prefixEnd_8123117 4171063433708400001079971 := by
  unfold tailWord_8123117
  simp only [CollatzResearch.WordTrace]
  refine ⟨296274416912341901778687605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197516277941561267852458403 296274416912341901778687605)
  ·
    refine ⟨27775726585532053291751963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 296274416912341901778687605 27775726585532053291751963)
    ·
      refine ⟨41663589878298079937627945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27775726585532053291751963 41663589878298079937627945)
      ·
        refine ⟨31247692408723559953220959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41663589878298079937627945 31247692408723559953220959)
        ·
          refine ⟨46871538613085339929831439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31247692408723559953220959 46871538613085339929831439)
          ·
            refine ⟨70307307919628009894747159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46871538613085339929831439 70307307919628009894747159)
            ·
              refine ⟨105460961879442014842120739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70307307919628009894747159 105460961879442014842120739)
              ·
                refine ⟨158191442819163022263181109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105460961879442014842120739 158191442819163022263181109)
                ·
                  refine ⟨14830447764296533337173229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158191442819163022263181109 14830447764296533337173229)
                  ·
                    refine ⟨5561417911611200001439961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14830447764296533337173229 5561417911611200001439961)
                    ·
                      refine ⟨4171063433708400001079971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5561417911611200001439961 4171063433708400001079971)
                      ·
                        rfl

theorem cell23_8123117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_8123117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123117 prefixEnd_8123117 := by exact prefixLift 8123117
  have htrace : WordTrace (prefixWord ++ tailWord_8123117) baseStart_8123117 baseEnd_8123117 := by
    simpa [prefixWord, tailWord_8123117, baseEnd_8123117] using wordTrace_append hprefix tailTrace_8123117
  have hstable : (prefixWord ++ tailWord_8123117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123117).length < 2 ^ (prefixWord ++ tailWord_8123117).sum := by decide
  have hdescent : baseEnd_8123117 < baseStart_8123117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123134 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_8123134 : Nat := 118140960795 + 8123134 * 2 ^ 59
def prefixEnd_8123134 : Nat := 4983230072969 + 3 ^ 40 * 8123134 * 2
def baseEnd_8123134 : Nat := 4171072162879526434567393

theorem tailTrace_8123134 : CollatzResearch.WordTrace tailWord_8123134 prefixEnd_8123134 4171072162879526434567393 := by
  unfold tailWord_8123134
  simp only [CollatzResearch.WordTrace]
  refine ⟨37034379619160039210257057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197516691302186875788037637 37034379619160039210257057)
  ·
    refine ⟨27775784714370029407692793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37034379619160039210257057 27775784714370029407692793)
    ·
      refine ⟨20831838535777522055769595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27775784714370029407692793 20831838535777522055769595)
      ·
        refine ⟨31247757803666283083654393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20831838535777522055769595 31247757803666283083654393)
        ·
          refine ⟨23435818352749712312740795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31247757803666283083654393 23435818352749712312740795)
          ·
            refine ⟨35153727529124568469111193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23435818352749712312740795 35153727529124568469111193)
            ·
              refine ⟨26365295646843426351833395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35153727529124568469111193 26365295646843426351833395)
              ·
                refine ⟨39547943470265139527750093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26365295646843426351833395 39547943470265139527750093)
                ·
                  refine ⟨14830478801349427322906285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39547943470265139527750093 14830478801349427322906285)
                  ·
                    refine ⟨5561429550506035246089857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14830478801349427322906285 5561429550506035246089857)
                    ·
                      refine ⟨4171072162879526434567393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5561429550506035246089857 4171072162879526434567393)
                      ·
                        rfl

theorem cell23_8123134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_8123134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123134 prefixEnd_8123134 := by exact prefixLift 8123134
  have htrace : WordTrace (prefixWord ++ tailWord_8123134) baseStart_8123134 baseEnd_8123134 := by
    simpa [prefixWord, tailWord_8123134, baseEnd_8123134] using wordTrace_append hprefix tailTrace_8123134
  have hstable : (prefixWord ++ tailWord_8123134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123134).length < 2 ^ (prefixWord ++ tailWord_8123134).sum := by decide
  have hdescent : baseEnd_8123134 < baseStart_8123134 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123147 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 4, 2, 2]
def baseStart_8123147 : Nat := 118140960795 + 8123147 * 2 ^ 59
def prefixEnd_8123147 : Nat := 4983230072969 + 3 ^ 40 * 8123147 * 2
def baseEnd_8123147 : Nat := 4171078838128034883704833

theorem tailTrace_8123147 : CollatzResearch.WordTrace tailWord_8123147 prefixEnd_8123147 4171078838128034883704833 := by
  unfold tailWord_8123147
  simp only [CollatzResearch.WordTrace]
  refine ⟨296275511102233216902279695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197517007401488811268186463 296275511102233216902279695)
  ·
    refine ⟨444413266653349825353419543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296275511102233216902279695 444413266653349825353419543)
    ·
      refine ⟨666619899980024738030129315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444413266653349825353419543 666619899980024738030129315)
      ·
        refine ⟨999929849970037107045193973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666619899980024738030129315 999929849970037107045193973)
        ·
          refine ⟨93743423434690978785486935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 999929849970037107045193973 93743423434690978785486935)
          ·
            refine ⟨140615135152036468178230403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93743423434690978785486935 140615135152036468178230403)
            ·
              refine ⟨210922702728054702267345605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140615135152036468178230403 210922702728054702267345605)
              ·
                refine ⟨39548006761510256675127301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210922702728054702267345605 39548006761510256675127301)
                ·
                  refine ⟨7415251267783173126586369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39548006761510256675127301 7415251267783173126586369)
                  ·
                    refine ⟨5561438450837379844939777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7415251267783173126586369 5561438450837379844939777)
                    ·
                      refine ⟨4171078838128034883704833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5561438450837379844939777 4171078838128034883704833)
                      ·
                        rfl

theorem cell23_8123147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 2, 2].length) (baseStart_8123147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123147 prefixEnd_8123147 := by exact prefixLift 8123147
  have htrace : WordTrace (prefixWord ++ tailWord_8123147) baseStart_8123147 baseEnd_8123147 := by
    simpa [prefixWord, tailWord_8123147, baseEnd_8123147] using wordTrace_append hprefix tailTrace_8123147
  have hstable : (prefixWord ++ tailWord_8123147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123147).length < 2 ^ (prefixWord ++ tailWord_8123147).sum := by decide
  have hdescent : baseEnd_8123147 < baseStart_8123147 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123164 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 4, 2, 2]
def baseStart_8123164 : Nat := 118140960795 + 8123164 * 2 ^ 59
def prefixEnd_8123164 : Nat := 4983230072969 + 3 ^ 40 * 8123164 * 2
def baseEnd_8123164 : Nat := 4171087567299161317192255

theorem tailTrace_8123164 : CollatzResearch.WordTrace tailWord_8123164 prefixEnd_8123164 4171087567299161317192255 := by
  unfold tailWord_8123164
  simp only [CollatzResearch.WordTrace]
  refine ⟨148138065571585814402824273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197517420762114419203765697 148138065571585814402824273)
  ·
    refine ⟨111103549178689360802118205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148138065571585814402824273 111103549178689360802118205)
    ·
      refine ⟨41663830942008510300794327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111103549178689360802118205 41663830942008510300794327)
      ·
        refine ⟨62495746413012765451191491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41663830942008510300794327 62495746413012765451191491)
        ·
          refine ⟨93743619619519148176787237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62495746413012765451191491 93743619619519148176787237)
          ·
            refine ⟨17576928678659840283147607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93743619619519148176787237 17576928678659840283147607)
            ·
              refine ⟨26365393017989760424721411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17576928678659840283147607 26365393017989760424721411)
              ·
                refine ⟨39548089526984640637082117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26365393017989760424721411 39548089526984640637082117)
                ·
                  refine ⟨7415266786309620119452897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39548089526984640637082117 7415266786309620119452897)
                  ·
                    refine ⟨5561450089732215089589673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7415266786309620119452897 5561450089732215089589673)
                    ·
                      refine ⟨4171087567299161317192255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5561450089732215089589673 4171087567299161317192255)
                      ·
                        rfl

theorem cell23_8123164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_8123164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123164 prefixEnd_8123164 := by exact prefixLift 8123164
  have htrace : WordTrace (prefixWord ++ tailWord_8123164) baseStart_8123164 baseEnd_8123164 := by
    simpa [prefixWord, tailWord_8123164, baseEnd_8123164] using wordTrace_append hprefix tailTrace_8123164
  have hstable : (prefixWord ++ tailWord_8123164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123164).length < 2 ^ (prefixWord ++ tailWord_8123164).sum := by decide
  have hdescent : baseEnd_8123164 < baseStart_8123164 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123170 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 7]
def baseStart_8123170 : Nat := 118140960795 + 8123170 * 2 ^ 59
def prefixEnd_8123170 : Nat := 4983230072969 + 3 ^ 40 * 8123170 * 2
def baseEnd_8123170 : Nat := 463454516464787588190803

theorem tailTrace_8123170 : CollatzResearch.WordTrace tailWord_8123170 prefixEnd_8123170 463454516464787588190803 := by
  unfold tailWord_8123170
  simp only [CollatzResearch.WordTrace]
  refine ⟨74069087495287472957591741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197517566654099927886911309 74069087495287472957591741)
  ·
    refine ⟨27775907810732802359096903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74069087495287472957591741 27775907810732802359096903)
    ·
      refine ⟨41663861716099203538645355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27775907810732802359096903 41663861716099203538645355)
      ·
        refine ⟨62495792574148805307968033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41663861716099203538645355 62495792574148805307968033)
        ·
          refine ⟨46871844430611603980976025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62495792574148805307968033 46871844430611603980976025)
          ·
            refine ⟨35153883322958702985732019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46871844430611603980976025 35153883322958702985732019)
            ·
              refine ⟨52730824984438054478598029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35153883322958702985732019 52730824984438054478598029)
              ·
                refine ⟨19774059369164270429474261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52730824984438054478598029 19774059369164270429474261)
                ·
                  refine ⟨463454516464787588190803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19774059369164270429474261 463454516464787588190803)
                  ·
                    rfl

theorem cell23_8123170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_8123170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123170 prefixEnd_8123170 := by exact prefixLift 8123170
  have htrace : WordTrace (prefixWord ++ tailWord_8123170) baseStart_8123170 baseEnd_8123170 := by
    simpa [prefixWord, tailWord_8123170, baseEnd_8123170] using wordTrace_append hprefix tailTrace_8123170
  have hstable : (prefixWord ++ tailWord_8123170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123170).length < 2 ^ (prefixWord ++ tailWord_8123170).sum := by decide
  have hdescent : baseEnd_8123170 < baseStart_8123170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123180 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 3]
def baseStart_8123180 : Nat := 118140960795 + 8123180 * 2 ^ 59
def prefixEnd_8123180 : Nat := 4983230072969 + 3 ^ 40 * 8123180 * 2
def baseEnd_8123180 : Nat := 4171095782989633254592181

theorem tailTrace_8123180 : CollatzResearch.WordTrace tailWord_8123180 prefixEnd_8123180 4171095782989633254592181 := by
  unfold tailWord_8123180
  simp only [CollatzResearch.WordTrace]
  refine ⟨148138357355556831769115497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197517809807409109025487329 148138357355556831769115497)
  ·
    refine ⟨111103768016667623826836623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148138357355556831769115497 111103768016667623826836623)
    ·
      refine ⟨166655652025001435740254935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111103768016667623826836623 166655652025001435740254935)
      ·
        refine ⟨249983478037502153610382403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166655652025001435740254935 249983478037502153610382403)
        ·
          refine ⟨374975217056253230415573605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249983478037502153610382403 374975217056253230415573605)
          ·
            refine ⟨70307853198047480702920051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 374975217056253230415573605 70307853198047480702920051)
            ·
              refine ⟨105461779797071221054380077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70307853198047480702920051 105461779797071221054380077)
              ·
                refine ⟨39548167423901707895392529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105461779797071221054380077 39548167423901707895392529)
                ·
                  refine ⟨29661125567926280921544397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39548167423901707895392529 29661125567926280921544397)
                  ·
                    refine ⟨11122922087972355345579149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29661125567926280921544397 11122922087972355345579149)
                    ·
                      refine ⟨4171095782989633254592181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11122922087972355345579149 4171095782989633254592181)
                      ·
                        rfl

theorem cell23_8123180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_8123180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123180 prefixEnd_8123180 := by exact prefixLift 8123180
  have htrace : WordTrace (prefixWord ++ tailWord_8123180) baseStart_8123180 baseEnd_8123180 := by
    simpa [prefixWord, tailWord_8123180, baseEnd_8123180] using wordTrace_append hprefix tailTrace_8123180
  have hstable : (prefixWord ++ tailWord_8123180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123180).length < 2 ^ (prefixWord ++ tailWord_8123180).sum := by decide
  have hdescent : baseEnd_8123180 < baseStart_8123180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123217 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 2, 5]
def baseStart_8123217 : Nat := 118140960795 + 8123217 * 2 ^ 59
def prefixEnd_8123217 : Nat := 4983230072969 + 3 ^ 40 * 8123217 * 2
def baseEnd_8123217 : Nat := 1390371593924616536609837

theorem tailTrace_8123217 : CollatzResearch.WordTrace tailWord_8123217 prefixEnd_8123217 1390371593924616536609837 := by
  unfold tailWord_8123217
  simp only [CollatzResearch.WordTrace]
  refine ⟨296278064211979618857327905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197518709474653079238218603 296278064211979618857327905)
  ·
    refine ⟨222208548158984714142995929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296278064211979618857327905 222208548158984714142995929)
    ·
      refine ⟨166656411119238535607246947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222208548158984714142995929 166656411119238535607246947)
      ·
        refine ⟨249984616678857803410870421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166656411119238535607246947 249984616678857803410870421)
        ·
          refine ⟨11718028906821459534884551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 249984616678857803410870421 11718028906821459534884551)
          ·
            refine ⟨17577043360232189302326827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11718028906821459534884551 17577043360232189302326827)
            ·
              refine ⟨26365565040348283953490241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17577043360232189302326827 26365565040348283953490241)
              ·
                refine ⟨19774173780261212965117681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26365565040348283953490241 19774173780261212965117681)
                ·
                  refine ⟨14830630335195909723838261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19774173780261212965117681 14830630335195909723838261)
                  ·
                    refine ⟨1390371593924616536609837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14830630335195909723838261 1390371593924616536609837)
                    ·
                      rfl

theorem cell23_8123217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_8123217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123217 prefixEnd_8123217 := by exact prefixLift 8123217
  have htrace : WordTrace (prefixWord ++ tailWord_8123217) baseStart_8123217 baseEnd_8123217 := by
    simpa [prefixWord, tailWord_8123217, baseEnd_8123217] using wordTrace_append hprefix tailTrace_8123217
  have hstable : (prefixWord ++ tailWord_8123217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123217).length < 2 ^ (prefixWord ++ tailWord_8123217).sum := by decide
  have hdescent : baseEnd_8123217 < baseStart_8123217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123237 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 2, 4, 2]
def baseStart_8123237 : Nat := 118140960795 + 8123237 * 2 ^ 59
def prefixEnd_8123237 : Nat := 4983230072969 + 3 ^ 40 * 8123237 * 2
def baseEnd_8123237 : Nat := 4171125051386939531579419

theorem tailTrace_8123237 : CollatzResearch.WordTrace tailWord_8123237 prefixEnd_8123237 4171125051386939531579419 := by
  unfold tailWord_8123237
  simp only [CollatzResearch.WordTrace]
  refine ⟨296278793671907162273055965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197519195781271441515370643 296278793671907162273055965)
  ·
    refine ⟨111104547626965185852395987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296278793671907162273055965 111104547626965185852395987)
    ·
      refine ⟨166656821440447778778593981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111104547626965185852395987 166656821440447778778593981)
      ·
        refine ⟨62496308040167917041972743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166656821440447778778593981 62496308040167917041972743)
        ·
          refine ⟨93744462060251875562959115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62496308040167917041972743 93744462060251875562959115)
          ·
            refine ⟨140616693090377813344438673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93744462060251875562959115 140616693090377813344438673)
            ·
              refine ⟨105462519817783360008329005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140616693090377813344438673 105462519817783360008329005)
              ·
                refine ⟨39548444931668760003123377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105462519817783360008329005 39548444931668760003123377)
                ·
                  refine ⟨29661333698751570002342533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39548444931668760003123377 29661333698751570002342533)
                  ·
                    refine ⟨5561500068515919375439225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29661333698751570002342533 5561500068515919375439225)
                    ·
                      refine ⟨4171125051386939531579419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5561500068515919375439225 4171125051386939531579419)
                      ·
                        rfl

theorem cell23_8123237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_8123237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123237 prefixEnd_8123237 := by exact prefixLift 8123237
  have htrace : WordTrace (prefixWord ++ tailWord_8123237) baseStart_8123237 baseEnd_8123237 := by
    simpa [prefixWord, tailWord_8123237, baseEnd_8123237] using wordTrace_append hprefix tailTrace_8123237
  have hstable : (prefixWord ++ tailWord_8123237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123237).length < 2 ^ (prefixWord ++ tailWord_8123237).sum := by decide
  have hdescent : baseEnd_8123237 < baseStart_8123237 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123250 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_8123250 : Nat := 118140960795 + 8123250 * 2 ^ 59
def prefixEnd_8123250 : Nat := 4983230072969 + 3 ^ 40 * 8123250 * 2
def baseEnd_8123250 : Nat := 4171131726635447980716859

theorem tailTrace_8123250 : CollatzResearch.WordTrace tailWord_8123250 prefixEnd_8123250 4171131726635447980716859 := by
  unfold tailWord_8123250
  simp only [CollatzResearch.WordTrace]
  refine ⟨74069816955215016373319801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197519511880573376995519469 74069816955215016373319801)
  ·
    refine ⟨55552362716411262279989851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74069816955215016373319801 55552362716411262279989851)
    ·
      refine ⟨83328544074616893419984777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55552362716411262279989851 83328544074616893419984777)
      ·
        refine ⟨62496408055962670064988583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83328544074616893419984777 62496408055962670064988583)
        ·
          refine ⟨93744612083944005097482875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62496408055962670064988583 93744612083944005097482875)
          ·
            refine ⟨140616918125916007646224313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93744612083944005097482875 140616918125916007646224313)
            ·
              refine ⟨105462688594437005734668235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140616918125916007646224313 105462688594437005734668235)
              ·
                refine ⟨158194032891655508602002353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105462688594437005734668235 158194032891655508602002353)
                ·
                  refine ⟨118645524668741631451501765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158194032891655508602002353 118645524668741631451501765)
                  ·
                    refine ⟨22246035875389055897156581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118645524668741631451501765 22246035875389055897156581)
                    ·
                      refine ⟨4171131726635447980716859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22246035875389055897156581 4171131726635447980716859)
                      ·
                        rfl

theorem cell23_8123250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_8123250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123250 prefixEnd_8123250 := by exact prefixLift 8123250
  have htrace : WordTrace (prefixWord ++ tailWord_8123250) baseStart_8123250 baseEnd_8123250 := by
    simpa [prefixWord, tailWord_8123250, baseEnd_8123250] using wordTrace_append hprefix tailTrace_8123250
  have hstable : (prefixWord ++ tailWord_8123250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123250).length < 2 ^ (prefixWord ++ tailWord_8123250).sum := by decide
  have hdescent : baseEnd_8123250 < baseStart_8123250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123254 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_8123254 : Nat := 118140960795 + 8123254 * 2 ^ 59
def prefixEnd_8123254 : Nat := 4983230072969 + 3 ^ 40 * 8123254 * 2
def baseEnd_8123254 : Nat := 4171133780558065965066841

theorem tailTrace_8123254 : CollatzResearch.WordTrace tailWord_8123254 prefixEnd_8123254 4171133780558065965066841 := by
  unfold tailWord_8123254
  simp only [CollatzResearch.WordTrace]
  refine ⟨18517463357052848386026551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197519609141897049450949877 18517463357052848386026551)
  ·
    refine ⟨27776195035579272579039827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18517463357052848386026551 27776195035579272579039827)
    ·
      refine ⟨41664292553368908868559741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27776195035579272579039827 41664292553368908868559741)
      ·
        refine ⟨15624109707513340825709903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41664292553368908868559741 15624109707513340825709903)
        ·
          refine ⟨23436164561270011238564855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15624109707513340825709903 23436164561270011238564855)
          ·
            refine ⟨35154246841905016857847283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23436164561270011238564855 35154246841905016857847283)
            ·
              refine ⟨52731370262857525286770925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35154246841905016857847283 52731370262857525286770925)
              ·
                refine ⟨19774263848571571982539097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52731370262857525286770925 19774263848571571982539097)
                ·
                  refine ⟨14830697886428678986904323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19774263848571571982539097 14830697886428678986904323)
                  ·
                    refine ⟨22246046829643018480356485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14830697886428678986904323 22246046829643018480356485)
                    ·
                      refine ⟨4171133780558065965066841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22246046829643018480356485 4171133780558065965066841)
                      ·
                        rfl

theorem cell23_8123254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_8123254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123254 prefixEnd_8123254 := by exact prefixLift 8123254
  have htrace : WordTrace (prefixWord ++ tailWord_8123254) baseStart_8123254 baseEnd_8123254 := by
    simpa [prefixWord, tailWord_8123254, baseEnd_8123254] using wordTrace_append hprefix tailTrace_8123254
  have hstable : (prefixWord ++ tailWord_8123254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123254).length < 2 ^ (prefixWord ++ tailWord_8123254).sum := by decide
  have hdescent : baseEnd_8123254 < baseStart_8123254 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123257 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 2, 2, 3]
def baseStart_8123257 : Nat := 118140960795 + 8123257 * 2 ^ 59
def prefixEnd_8123257 : Nat := 4983230072969 + 3 ^ 40 * 8123257 * 2
def baseEnd_8123257 : Nat := 4171135321000029453329327

theorem tailTrace_8123257 : CollatzResearch.WordTrace tailWord_8123257 prefixEnd_8123257 4171135321000029453329327 := by
  unfold tailWord_8123257
  simp only [CollatzResearch.WordTrace]
  refine ⟨296279523131834705688784025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197519682087889803792522683 296279523131834705688784025)
  ·
    refine ⟨222209642348876029266588019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296279523131834705688784025 222209642348876029266588019)
    ·
      refine ⟨333314463523314043899882029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222209642348876029266588019 333314463523314043899882029)
      ·
        refine ⟨124992923821242766462455761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333314463523314043899882029 124992923821242766462455761)
        ·
          refine ⟨93744692865932074846841821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124992923821242766462455761 93744692865932074846841821)
          ·
            refine ⟨35154259824724528067565683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93744692865932074846841821 35154259824724528067565683)
            ·
              refine ⟨52731389737086792101348525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35154259824724528067565683 52731389737086792101348525)
              ·
                refine ⟨19774271151407547038005697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52731389737086792101348525 19774271151407547038005697)
                ·
                  refine ⟨14830703363555660278504273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19774271151407547038005697 14830703363555660278504273)
                  ·
                    refine ⟨11123027522666745208878205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14830703363555660278504273 11123027522666745208878205)
                    ·
                      refine ⟨4171135321000029453329327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11123027522666745208878205 4171135321000029453329327)
                      ·
                        rfl

theorem cell23_8123257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_8123257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123257 prefixEnd_8123257 := by exact prefixLift 8123257
  have htrace : WordTrace (prefixWord ++ tailWord_8123257) baseStart_8123257 baseEnd_8123257 := by
    simpa [prefixWord, tailWord_8123257, baseEnd_8123257] using wordTrace_append hprefix tailTrace_8123257
  have hstable : (prefixWord ++ tailWord_8123257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123257).length < 2 ^ (prefixWord ++ tailWord_8123257).sum := by decide
  have hdescent : baseEnd_8123257 < baseStart_8123257 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123274 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 2, 2, 3]
def baseStart_8123274 : Nat := 118140960795 + 8123274 * 2 ^ 59
def prefixEnd_8123274 : Nat := 4983230072969 + 3 ^ 40 * 8123274 * 2
def baseEnd_8123274 : Nat := 4171144050171155886816749

theorem tailTrace_8123274 : CollatzResearch.WordTrace tailWord_8123274 prefixEnd_8123274 4171144050171155886816749 := by
  unfold tailWord_8123274
  simp only [CollatzResearch.WordTrace]
  refine ⟨74070035793193279398038219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197520095448515411728101917 74070035793193279398038219)
  ·
    refine ⟨111105053689789919097057329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74070035793193279398038219 111105053689789919097057329)
    ·
      refine ⟨83328790267342439322792997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111105053689789919097057329 83328790267342439322792997)
      ·
        refine ⟨15624148175126707373023687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83328790267342439322792997 15624148175126707373023687)
        ·
          refine ⟨23436222262690061059535531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15624148175126707373023687 23436222262690061059535531)
          ·
            refine ⟨35154333394035091589303297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23436222262690061059535531 35154333394035091589303297)
            ·
              refine ⟨26365750045526318691977473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35154333394035091589303297 26365750045526318691977473)
              ·
                refine ⟨19774312534144739018983105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26365750045526318691977473 19774312534144739018983105)
                ·
                  refine ⟨14830734400608554264237329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19774312534144739018983105 14830734400608554264237329)
                  ·
                    refine ⟨11123050800456415698177997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14830734400608554264237329 11123050800456415698177997)
                    ·
                      refine ⟨4171144050171155886816749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11123050800456415698177997 4171144050171155886816749)
                      ·
                        rfl

theorem cell23_8123274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_8123274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123274 prefixEnd_8123274 := by exact prefixLift 8123274
  have htrace : WordTrace (prefixWord ++ tailWord_8123274) baseStart_8123274 baseEnd_8123274 := by
    simpa [prefixWord, tailWord_8123274, baseEnd_8123274] using wordTrace_append hprefix tailTrace_8123274
  have hstable : (prefixWord ++ tailWord_8123274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123274).length < 2 ^ (prefixWord ++ tailWord_8123274).sum := by decide
  have hdescent : baseEnd_8123274 < baseStart_8123274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123300 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_8123300 : Nat := 118140960795 + 8123300 * 2 ^ 59
def prefixEnd_8123300 : Nat := 4983230072969 + 3 ^ 40 * 8123300 * 2
def baseEnd_8123300 : Nat := 4171157400668172785091629

theorem tailTrace_8123300 : CollatzResearch.WordTrace tailWord_8123300 prefixEnd_8123300 4171157400668172785091629 := by
  unfold tailWord_8123300
  simp only [CollatzResearch.WordTrace]
  refine ⟨148140545735339462016299677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197520727647119282688399569 148140545735339462016299677)
  ·
    refine ⟨55552704650752298256112379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148140545735339462016299677 55552704650752298256112379)
    ·
      refine ⟨83329056976128447384168569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55552704650752298256112379 83329056976128447384168569)
      ·
        refine ⟨62496792732096335538126427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83329056976128447384168569 62496792732096335538126427)
        ·
          refine ⟨93745189098144503307189641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62496792732096335538126427 93745189098144503307189641)
          ·
            refine ⟨70308891823608377480392231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93745189098144503307189641 70308891823608377480392231)
            ·
              refine ⟨105463337735412566220588347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70308891823608377480392231 105463337735412566220588347)
              ·
                refine ⟨158195006603118849330882521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105463337735412566220588347 158195006603118849330882521)
                ·
                  refine ⟨118646254952339136998161891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158195006603118849330882521 118646254952339136998161891)
                  ·
                    refine ⟨177969382428508705497242837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118646254952339136998161891 177969382428508705497242837)
                    ·
                      refine ⟨4171157400668172785091629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177969382428508705497242837 4171157400668172785091629)
                      ·
                        rfl

theorem cell23_8123300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_8123300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123300 prefixEnd_8123300 := by exact prefixLift 8123300
  have htrace : WordTrace (prefixWord ++ tailWord_8123300) baseStart_8123300 baseEnd_8123300 := by
    simpa [prefixWord, tailWord_8123300, baseEnd_8123300] using wordTrace_append hprefix tailTrace_8123300
  have hstable : (prefixWord ++ tailWord_8123300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123300).length < 2 ^ (prefixWord ++ tailWord_8123300).sum := by decide
  have hdescent : baseEnd_8123300 < baseStart_8123300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123321 : List Nat := [1, 2, 1, 4, 2, 2, 1, 5, 1, 1, 3]
def baseStart_8123321 : Nat := 118140960795 + 8123321 * 2 ^ 59
def prefixEnd_8123321 : Nat := 4983230072969 + 3 ^ 40 * 8123321 * 2
def baseEnd_8123321 : Nat := 4171168183761917202929033

theorem tailTrace_8123321 : CollatzResearch.WordTrace tailWord_8123321 prefixEnd_8123321 4171168183761917202929033 := by
  unfold tailWord_8123321
  simp only [CollatzResearch.WordTrace]
  refine ⟨296281857403602844619113817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197521238269068563079409211 296281857403602844619113817)
  ·
    refine ⟨222211393052702133464335363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296281857403602844619113817 222211393052702133464335363)
    ·
      refine ⟨333317089579053200196503045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222211393052702133464335363 333317089579053200196503045)
      ·
        refine ⟨62496954296072475036844321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333317089579053200196503045 62496954296072475036844321)
        ·
          refine ⟨46872715722054356277633241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62496954296072475036844321 46872715722054356277633241)
          ·
            refine ⟨35154536791540767208224931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46872715722054356277633241 35154536791540767208224931)
            ·
              refine ⟨52731805187311150812337397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35154536791540767208224931 52731805187311150812337397)
              ·
                refine ⟨4943606736310420388656631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52731805187311150812337397 4943606736310420388656631)
                ·
                  refine ⟨7415410104465630582984947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4943606736310420388656631 7415410104465630582984947)
                  ·
                    refine ⟨11123115156698445874477421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7415410104465630582984947 11123115156698445874477421)
                    ·
                      refine ⟨4171168183761917202929033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11123115156698445874477421 4171168183761917202929033)
                      ·
                        rfl

theorem cell23_8123321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_8123321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123321 prefixEnd_8123321 := by exact prefixLift 8123321
  have htrace : WordTrace (prefixWord ++ tailWord_8123321) baseStart_8123321 baseEnd_8123321 := by
    simpa [prefixWord, tailWord_8123321, baseEnd_8123321] using wordTrace_append hprefix tailTrace_8123321
  have hstable : (prefixWord ++ tailWord_8123321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123321).length < 2 ^ (prefixWord ++ tailWord_8123321).sum := by decide
  have hdescent : baseEnd_8123321 < baseStart_8123321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123354 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 1, 6]
def baseStart_8123354 : Nat := 118140960795 + 8123354 * 2 ^ 59
def prefixEnd_8123354 : Nat := 4983230072969 + 3 ^ 40 * 8123354 * 2
def baseEnd_8123354 : Nat := 1390395042874505191272127

theorem tailTrace_8123354 : CollatzResearch.WordTrace tailWord_8123354 prefixEnd_8123354 1390395042874505191272127 := by
  unfold tailWord_8123354
  simp only [CollatzResearch.WordTrace]
  refine ⟨74070765253120822813766279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197522040674988860836710077 74070765253120822813766279)
  ·
    refine ⟨111106147879681234220649419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74070765253120822813766279 111106147879681234220649419)
    ·
      refine ⟨166659221819521851330974129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111106147879681234220649419 166659221819521851330974129)
      ·
        refine ⟨124994416364641388498230597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166659221819521851330974129 124994416364641388498230597)
        ·
          refine ⟨23436453068370260343418237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124994416364641388498230597 23436453068370260343418237)
          ·
            refine ⟨8788669900638847628781839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23436453068370260343418237 8788669900638847628781839)
            ·
              refine ⟨13183004850958271443172759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8788669900638847628781839 13183004850958271443172759)
              ·
                refine ⟨19774507276437407164759139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13183004850958271443172759 19774507276437407164759139)
                ·
                  refine ⟨29661760914656110747138709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19774507276437407164759139 29661760914656110747138709)
                  ·
                    refine ⟨1390395042874505191272127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29661760914656110747138709 1390395042874505191272127)
                    ·
                      rfl

theorem cell23_8123354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_8123354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123354 prefixEnd_8123354 := by exact prefixLift 8123354
  have htrace : WordTrace (prefixWord ++ tailWord_8123354) baseStart_8123354 baseEnd_8123354 := by
    simpa [prefixWord, tailWord_8123354, baseEnd_8123354] using wordTrace_append hprefix tailTrace_8123354
  have hstable : (prefixWord ++ tailWord_8123354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123354).length < 2 ^ (prefixWord ++ tailWord_8123354).sum := by decide
  have hdescent : baseEnd_8123354 < baseStart_8123354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123367 : List Nat := [1, 1, 5, 2, 2, 2, 1, 9]
def baseStart_8123367 : Nat := 118140960795 + 8123367 * 2 ^ 59
def prefixEnd_8123367 : Nat := 4983230072969 + 3 ^ 40 * 8123367 * 2
def baseEnd_8123367 : Nat := 154488585328593482331623

theorem tailTrace_8123367 : CollatzResearch.WordTrace tailWord_8123367 prefixEnd_8123367 154488585328593482331623 := by
  unfold tailWord_8123367
  simp only [CollatzResearch.WordTrace]
  refine ⟨296283535161436194475288355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197522356774290796316858903 296283535161436194475288355)
  ·
    refine ⟨444425302742154291712932533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296283535161436194475288355 444425302742154291712932533)
    ·
      refine ⟨41664872132076964848087425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 444425302742154291712932533 41664872132076964848087425)
      ·
        refine ⟨31248654099057723636065569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41664872132076964848087425 31248654099057723636065569)
        ·
          refine ⟨23436490574293292727049177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31248654099057723636065569 23436490574293292727049177)
          ·
            refine ⟨17577367930719969545286883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23436490574293292727049177 17577367930719969545286883)
            ·
              refine ⟨26366051896079954317930325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17577367930719969545286883 26366051896079954317930325)
              ·
                refine ⟨154488585328593482331623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26366051896079954317930325 154488585328593482331623)
                ·
                  rfl

theorem cell23_8123367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 9].length) (baseStart_8123367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123367 prefixEnd_8123367 := by exact prefixLift 8123367
  have htrace : WordTrace (prefixWord ++ tailWord_8123367) baseStart_8123367 baseEnd_8123367 := by
    simpa [prefixWord, tailWord_8123367, baseEnd_8123367] using wordTrace_append hprefix tailTrace_8123367
  have hstable : (prefixWord ++ tailWord_8123367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123367).length < 2 ^ (prefixWord ++ tailWord_8123367).sum := by decide
  have hdescent : baseEnd_8123367 < baseStart_8123367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123447 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 4]
def baseStart_8123447 : Nat := 118140960795 + 8123447 * 2 ^ 59
def prefixEnd_8123447 : Nat := 4983230072969 + 3 ^ 40 * 8123447 * 2
def baseEnd_8123447 : Nat := 4171232882324383709953453

theorem tailTrace_8123447 : CollatzResearch.WordTrace tailWord_8123447 prefixEnd_8123447 4171232882324383709953453 := by
  unfold tailWord_8123447
  simp only [CollatzResearch.WordTrace]
  refine ⟨296286453001146368138200595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197524302000764245425467063 296286453001146368138200595)
  ·
    refine ⟨444429679501719552207300893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296286453001146368138200595 444429679501719552207300893)
    ·
      refine ⟨166661129813144832077737835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444429679501719552207300893 166661129813144832077737835)
      ·
        refine ⟨249991694719717248116606753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166661129813144832077737835 249991694719717248116606753)
        ·
          refine ⟨187493771039787936087455065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249991694719717248116606753 187493771039787936087455065)
          ·
            refine ⟨140620328279840952065591299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187493771039787936087455065 140620328279840952065591299)
            ·
              refine ⟨210930492419761428098386949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140620328279840952065591299 210930492419761428098386949)
              ·
                refine ⟨39549467328705267768447553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210930492419761428098386949 39549467328705267768447553)
                ·
                  refine ⟨29662100496528950826335665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39549467328705267768447553 29662100496528950826335665)
                  ·
                    refine ⟨22246575372396713119751749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29662100496528950826335665 22246575372396713119751749)
                    ·
                      refine ⟨4171232882324383709953453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22246575372396713119751749 4171232882324383709953453)
                      ·
                        rfl

theorem cell23_8123447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_8123447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123447 prefixEnd_8123447 := by exact prefixLift 8123447
  have htrace : WordTrace (prefixWord ++ tailWord_8123447) baseStart_8123447 baseEnd_8123447 := by
    simpa [prefixWord, tailWord_8123447, baseEnd_8123447] using wordTrace_append hprefix tailTrace_8123447
  have hstable : (prefixWord ++ tailWord_8123447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123447).length < 2 ^ (prefixWord ++ tailWord_8123447).sum := by decide
  have hdescent : baseEnd_8123447 < baseStart_8123447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123474 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 7]
def baseStart_8123474 : Nat := 118140960795 + 8123474 * 2 ^ 59
def prefixEnd_8123474 : Nat := 4983230072969 + 3 ^ 40 * 8123474 * 2
def baseEnd_8123474 : Nat := 463471860700228344923981

theorem tailTrace_8123474 : CollatzResearch.WordTrace tailWord_8123474 prefixEnd_8123474 463471860700228344923981 := by
  unfold tailWord_8123474
  simp only [CollatzResearch.WordTrace]
  refine ⟨74071859443012137937358369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197524958514699034499622317 74071859443012137937358369)
  ·
    refine ⟨55553894582259103453018777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74071859443012137937358369 55553894582259103453018777)
    ·
      refine ⟨41665420936694327589764083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55553894582259103453018777 41665420936694327589764083)
      ·
        refine ⟨62498131405041491384646125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41665420936694327589764083 62498131405041491384646125)
        ·
          refine ⟨23436799276890559269242297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62498131405041491384646125 23436799276890559269242297)
          ·
            refine ⟨17577599457667919451931723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23436799276890559269242297 17577599457667919451931723)
            ·
              refine ⟨26366399186501879177897585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17577599457667919451931723 26366399186501879177897585)
              ·
                refine ⟨19774799389876409383423189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26366399186501879177897585 19774799389876409383423189)
                ·
                  refine ⟨463471860700228344923981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19774799389876409383423189 463471860700228344923981)
                  ·
                    rfl

theorem cell23_8123474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_8123474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123474 prefixEnd_8123474 := by exact prefixLift 8123474
  have htrace : WordTrace (prefixWord ++ tailWord_8123474) baseStart_8123474 baseEnd_8123474 := by
    simpa [prefixWord, tailWord_8123474, baseEnd_8123474] using wordTrace_append hprefix tailTrace_8123474
  have hstable : (prefixWord ++ tailWord_8123474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123474).length < 2 ^ (prefixWord ++ tailWord_8123474).sum := by decide
  have hdescent : baseEnd_8123474 < baseStart_8123474 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123484 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_8123484 : Nat := 118140960795 + 8123484 * 2 ^ 59
def prefixEnd_8123484 : Nat := 4983230072969 + 3 ^ 40 * 8123484 * 2
def baseEnd_8123484 : Nat := 4171251881108600065190783

theorem tailTrace_8123484 : CollatzResearch.WordTrace tailWord_8123484 prefixEnd_8123484 4171251881108600065190783 := by
  unfold tailWord_8123484
  simp only [CollatzResearch.WordTrace]
  refine ⟨148143901251006161728648753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197525201668008215638198337 148143901251006161728648753)
  ·
    refine ⟨111107925938254621296486565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148143901251006161728648753 111107925938254621296486565)
    ·
      refine ⟨20832736113422741493091231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111107925938254621296486565 20832736113422741493091231)
      ·
        refine ⟨31249104170134112239636847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20832736113422741493091231 31249104170134112239636847)
        ·
          refine ⟨46873656255201168359455271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31249104170134112239636847 46873656255201168359455271)
          ·
            refine ⟨70310484382801752539182907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46873656255201168359455271 70310484382801752539182907)
            ·
              refine ⟨105465726574202628808774361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70310484382801752539182907 105465726574202628808774361)
              ·
                refine ⟨79099294930651971606580771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105465726574202628808774361 79099294930651971606580771)
                ·
                  refine ⟨118648942395977957409871157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79099294930651971606580771 118648942395977957409871157)
                  ·
                    refine ⟨11123338349622933507175421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118648942395977957409871157 11123338349622933507175421)
                    ·
                      refine ⟨4171251881108600065190783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11123338349622933507175421 4171251881108600065190783)
                      ·
                        rfl

theorem cell23_8123484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_8123484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123484 prefixEnd_8123484 := by exact prefixLift 8123484
  have htrace : WordTrace (prefixWord ++ tailWord_8123484) baseStart_8123484 baseEnd_8123484 := by
    simpa [prefixWord, tailWord_8123484, baseEnd_8123484] using wordTrace_append hprefix tailTrace_8123484
  have hstable : (prefixWord ++ tailWord_8123484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123484).length < 2 ^ (prefixWord ++ tailWord_8123484).sum := by decide
  have hdescent : baseEnd_8123484 < baseStart_8123484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123487 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 1, 7]
def baseStart_8123487 : Nat := 118140960795 + 8123487 * 2 ^ 59
def prefixEnd_8123487 : Nat := 4983230072969 + 3 ^ 40 * 8123487 * 2
def baseEnd_8123487 : Nat := 1390417807183521184484423

theorem tailTrace_8123487 : CollatzResearch.WordTrace tailWord_8123487 prefixEnd_8123487 1390417807183521184484423 := by
  unfold tailWord_8123487
  simp only [CollatzResearch.WordTrace]
  refine ⟨296287911921001454969656715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197525274614000969979771143 296287911921001454969656715)
  ·
    refine ⟨444431867881502182454485073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296287911921001454969656715 444431867881502182454485073)
    ·
      refine ⟨333323900911126636840863805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444431867881502182454485073 333323900911126636840863805)
      ·
        refine ⟨124996462841672488815323927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333323900911126636840863805 124996462841672488815323927)
        ·
          refine ⟨187494694262508733222985891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124996462841672488815323927 187494694262508733222985891)
          ·
            refine ⟨281242041393763099834478837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187494694262508733222985891 281242041393763099834478837)
            ·
              refine ⟨26366441380665290609482391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 281242041393763099834478837 26366441380665290609482391)
              ·
                refine ⟨39549662070997935914223587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26366441380665290609482391 39549662070997935914223587)
                ·
                  refine ⟨59324493106496903871335381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39549662070997935914223587 59324493106496903871335381)
                  ·
                    refine ⟨1390417807183521184484423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59324493106496903871335381 1390417807183521184484423)
                    ·
                      rfl

theorem cell23_8123487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 7].length) (baseStart_8123487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123487 prefixEnd_8123487 := by exact prefixLift 8123487
  have htrace : WordTrace (prefixWord ++ tailWord_8123487) baseStart_8123487 baseEnd_8123487 := by
    simpa [prefixWord, tailWord_8123487, baseEnd_8123487] using wordTrace_append hprefix tailTrace_8123487
  have hstable : (prefixWord ++ tailWord_8123487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123487).length < 2 ^ (prefixWord ++ tailWord_8123487).sum := by decide
  have hdescent : baseEnd_8123487 < baseStart_8123487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123524 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_8123524 : Nat := 118140960795 + 8123524 * 2 ^ 59
def prefixEnd_8123524 : Nat := 4983230072969 + 3 ^ 40 * 8123524 * 2
def baseEnd_8123524 : Nat := 4171272420334779908690599

theorem tailTrace_8123524 : CollatzResearch.WordTrace tailWord_8123524 prefixEnd_8123524 4171272420334779908690599 := by
  unfold tailWord_8123524
  simp only [CollatzResearch.WordTrace]
  refine ⟨148144630710933705144376813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197526174281244940192502417 148144630710933705144376813)
  ·
    refine ⟨55554236516600139429141305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148144630710933705144376813 55554236516600139429141305)
    ·
      refine ⟨41665677387450104571855979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55554236516600139429141305 41665677387450104571855979)
      ·
        refine ⟨62498516081175156857783969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41665677387450104571855979 62498516081175156857783969)
        ·
          refine ⟨46873887060881367643337977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62498516081175156857783969 46873887060881367643337977)
          ·
            refine ⟨35155415295661025732503483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46873887060881367643337977 35155415295661025732503483)
            ·
              refine ⟨52733122943491538598755225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35155415295661025732503483 52733122943491538598755225)
              ·
                refine ⟨39549842207618653949066419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52733122943491538598755225 39549842207618653949066419)
                ·
                  refine ⟨59324763311427980923599629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39549842207618653949066419 59324763311427980923599629)
                  ·
                    refine ⟨22246786241785492846349861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59324763311427980923599629 22246786241785492846349861)
                    ·
                      refine ⟨4171272420334779908690599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22246786241785492846349861 4171272420334779908690599)
                      ·
                        rfl

theorem cell23_8123524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_8123524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123524 prefixEnd_8123524 := by exact prefixLift 8123524
  have htrace : WordTrace (prefixWord ++ tailWord_8123524) baseStart_8123524 baseEnd_8123524 := by
    simpa [prefixWord, tailWord_8123524, baseEnd_8123524] using wordTrace_append hprefix tailTrace_8123524
  have hstable : (prefixWord ++ tailWord_8123524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123524).length < 2 ^ (prefixWord ++ tailWord_8123524).sum := by decide
  have hdescent : baseEnd_8123524 < baseStart_8123524 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123567 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 8]
def baseStart_8123567 : Nat := 118140960795 + 8123567 * 2 ^ 59
def prefixEnd_8123567 : Nat := 4983230072969 + 3 ^ 40 * 8123567 * 2
def baseEnd_8123567 : Nat := 4171294500002923240452901

theorem tailTrace_8123567 : CollatzResearch.WordTrace tailWord_8123567 prefixEnd_8123567 4171294500002923240452901 := by
  unfold tailWord_8123567
  simp only [CollatzResearch.WordTrace]
  refine ⟨296290829760711628632568955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197527219840474419088379303 296290829760711628632568955)
  ·
    refine ⟨444436244641067442948853433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296290829760711628632568955 444436244641067442948853433)
    ·
      refine ⟨333327183480800582211640075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444436244641067442948853433 333327183480800582211640075)
      ·
        refine ⟨499990775221200873317460113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333327183480800582211640075 499990775221200873317460113)
        ·
          refine ⟨374993081415900654988095085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499990775221200873317460113 374993081415900654988095085)
          ·
            refine ⟨140622405530962745620535657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374993081415900654988095085 140622405530962745620535657)
            ·
              refine ⟨105466804148222059215401743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140622405530962745620535657 105466804148222059215401743)
              ·
                refine ⟨158200206222333088823102615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105466804148222059215401743 158200206222333088823102615)
                ·
                  refine ⟨237300309333499633234653923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158200206222333088823102615 237300309333499633234653923)
                  ·
                    refine ⟨355950464000249449851980885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 237300309333499633234653923 355950464000249449851980885)
                    ·
                      refine ⟨4171294500002923240452901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 355950464000249449851980885 4171294500002923240452901)
                      ·
                        rfl

theorem cell23_8123567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_8123567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123567 prefixEnd_8123567 := by exact prefixLift 8123567
  have htrace : WordTrace (prefixWord ++ tailWord_8123567) baseStart_8123567 baseEnd_8123567 := by
    simpa [prefixWord, tailWord_8123567, baseEnd_8123567] using wordTrace_append hprefix tailTrace_8123567
  have hstable : (prefixWord ++ tailWord_8123567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123567).length < 2 ^ (prefixWord ++ tailWord_8123567).sum := by decide
  have hdescent : baseEnd_8123567 < baseStart_8123567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123581 : List Nat := [1, 4, 1, 2, 1, 1, 6, 1, 6]
def baseStart_8123581 : Nat := 118140960795 + 8123581 * 2 ^ 59
def prefixEnd_8123581 : Nat := 4983230072969 + 3 ^ 40 * 8123581 * 2
def baseEnd_8123581 : Nat := 463477965414676242853093

theorem tailTrace_8123581 : CollatzResearch.WordTrace tailWord_8123581 prefixEnd_8123581 463477965414676242853093 := by
  unfold tailWord_8123581
  simp only [CollatzResearch.WordTrace]
  refine ⟨296291340382660909023578597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197527560255107272682385731 296291340382660909023578597)
  ·
    refine ⟨55554626321748920441920987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296291340382660909023578597 55554626321748920441920987)
    ·
      refine ⟨83331939482623380662881481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55554626321748920441920987 83331939482623380662881481)
      ·
        refine ⟨62498954611967535497161111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83331939482623380662881481 62498954611967535497161111)
        ·
          refine ⟨93748431917951303245741667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62498954611967535497161111 93748431917951303245741667)
          ·
            refine ⟨140622647876926954868612501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93748431917951303245741667 140622647876926954868612501)
            ·
              refine ⟨6591686619230951009466211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140622647876926954868612501 6591686619230951009466211)
              ·
                refine ⟨9887529928846426514199317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6591686619230951009466211 9887529928846426514199317)
                ·
                  refine ⟨463477965414676242853093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9887529928846426514199317 463477965414676242853093)
                  ·
                    rfl

theorem cell23_8123581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_8123581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123581 prefixEnd_8123581 := by exact prefixLift 8123581
  have htrace : WordTrace (prefixWord ++ tailWord_8123581) baseStart_8123581 baseEnd_8123581 := by
    simpa [prefixWord, tailWord_8123581, baseEnd_8123581] using wordTrace_append hprefix tailTrace_8123581
  have hstable : (prefixWord ++ tailWord_8123581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123581).length < 2 ^ (prefixWord ++ tailWord_8123581).sum := by decide
  have hdescent : baseEnd_8123581 < baseStart_8123581 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123587 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 7]
def baseStart_8123587 : Nat := 118140960795 + 8123587 * 2 ^ 59
def prefixEnd_8123587 : Nat := 4983230072969 + 3 ^ 40 * 8123587 * 2
def baseEnd_8123587 : Nat := 4171304769616013162202809

theorem tailTrace_8123587 : CollatzResearch.WordTrace tailWord_8123587 prefixEnd_8123587 4171304769616013162202809 := by
  unfold tailWord_8123587
  simp only [CollatzResearch.WordTrace]
  refine ⟨296291559220639172048297015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197527706147092781365531343 296291559220639172048297015)
  ·
    refine ⟨444437338830958758072445523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296291559220639172048297015 444437338830958758072445523)
    ·
      refine ⟨666656008246438137108668285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444437338830958758072445523 666656008246438137108668285)
      ·
        refine ⟨249996003092414301415750607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 666656008246438137108668285 249996003092414301415750607)
        ·
          refine ⟨374994004638621452123625911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249996003092414301415750607 374994004638621452123625911)
          ·
            refine ⟨562491006957932178185438867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374994004638621452123625911 562491006957932178185438867)
            ·
              refine ⟨843736510436898267278158301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562491006957932178185438867 843736510436898267278158301)
              ·
                refine ⟨316401191413836850229309363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 843736510436898267278158301 316401191413836850229309363)
                ·
                  refine ⟨474601787120755275343964045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316401191413836850229309363 474601787120755275343964045)
                  ·
                    refine ⟨177975670170283228253986517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 474601787120755275343964045 177975670170283228253986517)
                    ·
                      refine ⟨4171304769616013162202809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177975670170283228253986517 4171304769616013162202809)
                      ·
                        rfl

theorem cell23_8123587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_8123587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123587 prefixEnd_8123587 := by exact prefixLift 8123587
  have htrace : WordTrace (prefixWord ++ tailWord_8123587) baseStart_8123587 baseEnd_8123587 := by
    simpa [prefixWord, tailWord_8123587, baseEnd_8123587] using wordTrace_append hprefix tailTrace_8123587
  have hstable : (prefixWord ++ tailWord_8123587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123587).length < 2 ^ (prefixWord ++ tailWord_8123587).sum := by decide
  have hdescent : baseEnd_8123587 < baseStart_8123587 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123591 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 3, 1, 3]
def baseStart_8123591 : Nat := 118140960795 + 8123591 * 2 ^ 59
def prefixEnd_8123591 : Nat := 4983230072969 + 3 ^ 40 * 8123591 * 2
def baseEnd_8123591 : Nat := 4171306823538631146552791

theorem tailTrace_8123591 : CollatzResearch.WordTrace tailWord_8123591 prefixEnd_8123591 4171306823538631146552791 := by
  unfold tailWord_8123591
  simp only [CollatzResearch.WordTrace]
  refine ⟨296291705112624680731442627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197527803408416453820961751 296291705112624680731442627)
  ·
    refine ⟨444437557668937021097163941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296291705112624680731442627 444437557668937021097163941)
    ·
      refine ⟨83332042062925691455718239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 444437557668937021097163941 83332042062925691455718239)
      ·
        refine ⟨124998063094388537183577359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83332042062925691455718239 124998063094388537183577359)
        ·
          refine ⟨187497094641582805775366039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124998063094388537183577359 187497094641582805775366039)
          ·
            refine ⟨281245641962374208663049059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187497094641582805775366039 281245641962374208663049059)
            ·
              refine ⟨421868462943561312994573589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281245641962374208663049059 421868462943561312994573589)
              ·
                refine ⟨19775084200479436546620637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 421868462943561312994573589 19775084200479436546620637)
                ·
                  refine ⟨7415656575179788704982739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19775084200479436546620637 7415656575179788704982739)
                  ·
                    refine ⟨11123484862769683057474109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7415656575179788704982739 11123484862769683057474109)
                    ·
                      refine ⟨4171306823538631146552791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11123484862769683057474109 4171306823538631146552791)
                      ·
                        rfl

theorem cell23_8123591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_8123591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123591 prefixEnd_8123591 := by exact prefixLift 8123591
  have htrace : WordTrace (prefixWord ++ tailWord_8123591) baseStart_8123591 baseEnd_8123591 := by
    simpa [prefixWord, tailWord_8123591, baseEnd_8123591] using wordTrace_append hprefix tailTrace_8123591
  have hstable : (prefixWord ++ tailWord_8123591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123591).length < 2 ^ (prefixWord ++ tailWord_8123591).sum := by decide
  have hdescent : baseEnd_8123591 < baseStart_8123591 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123624 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 3, 6]
def baseStart_8123624 : Nat := 118140960795 + 8123624 * 2 ^ 59
def prefixEnd_8123624 : Nat := 4983230072969 + 3 ^ 40 * 8123624 * 2
def baseEnd_8123624 : Nat := 1390441256133409839146713

theorem tailTrace_8123624 : CollatzResearch.WordTrace tailWord_8123624 prefixEnd_8123624 1390441256133409839146713 := by
  unfold tailWord_8123624
  simp only [CollatzResearch.WordTrace]
  refine ⟨148146454360752563683696963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197528605814336751578262617 148146454360752563683696963)
  ·
    refine ⟨222219681541128845525545445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148146454360752563683696963 222219681541128845525545445)
    ·
      refine ⟨41666190288961658536039771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222219681541128845525545445 41666190288961658536039771)
      ·
        refine ⟨62499285433442487804059657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41666190288961658536039771 62499285433442487804059657)
        ·
          refine ⟨46874464075081865853044743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62499285433442487804059657 46874464075081865853044743)
          ·
            refine ⟨70311696112622798779567115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46874464075081865853044743 70311696112622798779567115)
            ·
              refine ⟨105467544168934198169350673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70311696112622798779567115 105467544168934198169350673)
              ·
                refine ⟨79100658126700648627013005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105467544168934198169350673 79100658126700648627013005)
                ·
                  refine ⟨29662746797512743235129877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79100658126700648627013005 29662746797512743235129877)
                  ·
                    refine ⟨1390441256133409839146713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29662746797512743235129877 1390441256133409839146713)
                    ·
                      rfl

theorem cell23_8123624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_8123624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123624 prefixEnd_8123624 := by exact prefixLift 8123624
  have htrace : WordTrace (prefixWord ++ tailWord_8123624) baseStart_8123624 baseEnd_8123624 := by
    simpa [prefixWord, tailWord_8123624, baseEnd_8123624] using wordTrace_append hprefix tailTrace_8123624
  have hstable : (prefixWord ++ tailWord_8123624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123624).length < 2 ^ (prefixWord ++ tailWord_8123624).sum := by decide
  have hdescent : baseEnd_8123624 < baseStart_8123624 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123641 : List Nat := [1, 2, 1, 3, 1, 1, 3, 5, 2, 4]
def baseStart_8123641 : Nat := 118140960795 + 8123641 * 2 ^ 59
def prefixEnd_8123641 : Nat := 4983230072969 + 3 ^ 40 * 8123641 * 2
def baseEnd_8123641 : Nat := 1390444165857118650309187

theorem tailTrace_8123641 : CollatzResearch.WordTrace tailWord_8123641 prefixEnd_8123641 1390444165857118650309187 := by
  unfold tailWord_8123641
  simp only [CollatzResearch.WordTrace]
  refine ⟨296293528762443539270762777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197529019174962359513841851 296293528762443539270762777)
  ·
    refine ⟨222220146571832654453072083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296293528762443539270762777 222220146571832654453072083)
    ·
      refine ⟨333330219857748981679608125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222220146571832654453072083 333330219857748981679608125)
      ·
        refine ⟨124998832446655868129853047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333330219857748981679608125 124998832446655868129853047)
        ·
          refine ⟨187498248669983802194779571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124998832446655868129853047 187498248669983802194779571)
          ·
            refine ⟨281247373004975703292169357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187498248669983802194779571 281247373004975703292169357)
            ·
              refine ⟨105467764876865888734563509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281247373004975703292169357 105467764876865888734563509)
              ·
                refine ⟨9887602957206177068865329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105467764876865888734563509 9887602957206177068865329)
                ·
                  refine ⟨7415702217904632801648997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9887602957206177068865329 7415702217904632801648997)
                  ·
                    refine ⟨1390444165857118650309187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7415702217904632801648997 1390444165857118650309187)
                    ·
                      rfl

theorem cell23_8123641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 4].length) (baseStart_8123641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123641 prefixEnd_8123641 := by exact prefixLift 8123641
  have htrace : WordTrace (prefixWord ++ tailWord_8123641) baseStart_8123641 baseEnd_8123641 := by
    simpa [prefixWord, tailWord_8123641, baseEnd_8123641] using wordTrace_append hprefix tailTrace_8123641
  have hstable : (prefixWord ++ tailWord_8123641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123641).length < 2 ^ (prefixWord ++ tailWord_8123641).sum := by decide
  have hdescent : baseEnd_8123641 < baseStart_8123641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123651 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 3]
def baseStart_8123651 : Nat := 118140960795 + 8123651 * 2 ^ 59
def prefixEnd_8123651 : Nat := 4983230072969 + 3 ^ 40 * 8123651 * 2
def baseEnd_8123651 : Nat := 4171337632377900911802515

theorem tailTrace_8123651 : CollatzResearch.WordTrace tailWord_8123651 prefixEnd_8123651 4171337632377900911802515 := by
  unfold tailWord_8123651
  simp only [CollatzResearch.WordTrace]
  refine ⟨296293893492407310978626807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197529262328271540652417871 296293893492407310978626807)
  ·
    refine ⟨444440840238610966467940211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296293893492407310978626807 444440840238610966467940211)
    ·
      refine ⟨666661260357916449701910317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444440840238610966467940211 666661260357916449701910317)
      ·
        refine ⟨249997972634218668638216369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 666661260357916449701910317 249997972634218668638216369)
        ·
          refine ⟨187498479475664001478662277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249997972634218668638216369 187498479475664001478662277)
          ·
            refine ⟨35155964901687000277249177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187498479475664001478662277 35155964901687000277249177)
            ·
              refine ⟨26366973676265250207936883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35155964901687000277249177 26366973676265250207936883)
              ·
                refine ⟨39550460514397875311905325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26366973676265250207936883 39550460514397875311905325)
                ·
                  refine ⟨14831422692899203241964497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39550460514397875311905325 14831422692899203241964497)
                  ·
                    refine ⟨11123567019674402431473373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14831422692899203241964497 11123567019674402431473373)
                    ·
                      refine ⟨4171337632377900911802515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11123567019674402431473373 4171337632377900911802515)
                      ·
                        rfl

theorem cell23_8123651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_8123651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123651 prefixEnd_8123651 := by exact prefixLift 8123651
  have htrace : WordTrace (prefixWord ++ tailWord_8123651) baseStart_8123651 baseEnd_8123651 := by
    simpa [prefixWord, tailWord_8123651, baseEnd_8123651] using wordTrace_append hprefix tailTrace_8123651
  have hstable : (prefixWord ++ tailWord_8123651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123651).length < 2 ^ (prefixWord ++ tailWord_8123651).sum := by decide
  have hdescent : baseEnd_8123651 < baseStart_8123651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123664 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 3]
def baseStart_8123664 : Nat := 118140960795 + 8123664 * 2 ^ 59
def prefixEnd_8123664 : Nat := 4983230072969 + 3 ^ 40 * 8123664 * 2
def baseEnd_8123664 : Nat := 4171344307626409360939955

theorem tailTrace_8123664 : CollatzResearch.WordTrace tailWord_8123664 prefixEnd_8123664 4171344307626409360939955 := by
  unfold tailWord_8123664
  simp only [CollatzResearch.WordTrace]
  refine ⟨148147183820680107099425023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197529578427573476132566697 148147183820680107099425023)
  ·
    refine ⟨222220775731020160649137535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148147183820680107099425023 222220775731020160649137535)
    ·
      refine ⟨333331163596530240973706303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222220775731020160649137535 333331163596530240973706303)
      ·
        refine ⟨499996745394795361460559455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333331163596530240973706303 499996745394795361460559455)
        ·
          refine ⟨749995118092193042190839183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499996745394795361460559455 749995118092193042190839183)
          ·
            refine ⟨1124992677138289563286258775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749995118092193042190839183 1124992677138289563286258775)
            ·
              refine ⟨1687489015707434344929388163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124992677138289563286258775 1687489015707434344929388163)
              ·
                refine ⟨2531233523561151517394082245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687489015707434344929388163 2531233523561151517394082245)
                ·
                  refine ⟨474606285667715909511390421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2531233523561151517394082245 474606285667715909511390421)
                  ·
                    refine ⟨11123584820337091629173213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 474606285667715909511390421 11123584820337091629173213)
                    ·
                      refine ⟨4171344307626409360939955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11123584820337091629173213 4171344307626409360939955)
                      ·
                        rfl

theorem cell23_8123664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 3].length) (baseStart_8123664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123664 prefixEnd_8123664 := by exact prefixLift 8123664
  have htrace : WordTrace (prefixWord ++ tailWord_8123664) baseStart_8123664 baseEnd_8123664 := by
    simpa [prefixWord, tailWord_8123664, baseEnd_8123664] using wordTrace_append hprefix tailTrace_8123664
  have hstable : (prefixWord ++ tailWord_8123664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123664).length < 2 ^ (prefixWord ++ tailWord_8123664).sum := by decide
  have hdescent : baseEnd_8123664 < baseStart_8123664 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123682 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 3, 2, 2]
def baseStart_8123682 : Nat := 118140960795 + 8123682 * 2 ^ 59
def prefixEnd_8123682 : Nat := 4983230072969 + 3 ^ 40 * 8123682 * 2
def baseEnd_8123682 : Nat := 4171353550278190290514873

theorem tailTrace_8123682 : CollatzResearch.WordTrace tailWord_8123682 prefixEnd_8123682 4171353550278190290514873 := by
  unfold tailWord_8123682
  simp only [CollatzResearch.WordTrace]
  refine ⟨74073756038823750818251325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197530016103530002182003533 74073756038823750818251325)
  ·
    refine ⟨27777658514558906556844247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74073756038823750818251325 27777658514558906556844247)
    ·
      refine ⟨41666487771838359835266371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27777658514558906556844247 41666487771838359835266371)
      ·
        refine ⟨62499731657757539752899557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41666487771838359835266371 62499731657757539752899557)
        ·
          refine ⟨11718699685829538703668667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62499731657757539752899557 11718699685829538703668667)
          ·
            refine ⟨17578049528744308055503001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11718699685829538703668667 17578049528744308055503001)
            ·
              refine ⟨13183537146558231041627251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17578049528744308055503001 13183537146558231041627251)
              ·
                refine ⟨19775305719837346562440877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13183537146558231041627251 19775305719837346562440877)
                ·
                  refine ⟨7415739644939004960915329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19775305719837346562440877 7415739644939004960915329)
                  ·
                    refine ⟨5561804733704253720686497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7415739644939004960915329 5561804733704253720686497)
                    ·
                      refine ⟨4171353550278190290514873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5561804733704253720686497 4171353550278190290514873)
                      ·
                        rfl

theorem cell23_8123682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_8123682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123682 prefixEnd_8123682 := by exact prefixLift 8123682
  have htrace : WordTrace (prefixWord ++ tailWord_8123682) baseStart_8123682 baseEnd_8123682 := by
    simpa [prefixWord, tailWord_8123682, baseEnd_8123682] using wordTrace_append hprefix tailTrace_8123682
  have hstable : (prefixWord ++ tailWord_8123682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123682).length < 2 ^ (prefixWord ++ tailWord_8123682).sum := by decide
  have hdescent : baseEnd_8123682 < baseStart_8123682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123698 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3]
def baseStart_8123698 : Nat := 118140960795 + 8123698 * 2 ^ 59
def prefixEnd_8123698 : Nat := 4983230072969 + 3 ^ 40 * 8123698 * 2
def baseEnd_8123698 : Nat := 4171361765968662227914799

theorem tailTrace_8123698 : CollatzResearch.WordTrace tailWord_8123698 prefixEnd_8123698 4171361765968662227914799 := by
  unfold tailWord_8123698
  simp only [CollatzResearch.WordTrace]
  refine ⟨74073901930809259501396937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197530405148824692003725165 74073901930809259501396937)
  ·
    refine ⟨55555426448106944626047703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74073901930809259501396937 55555426448106944626047703)
    ·
      refine ⟨83333139672160416939071555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55555426448106944626047703 83333139672160416939071555)
      ·
        refine ⟨124999709508240625408607333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83333139672160416939071555 124999709508240625408607333)
        ·
          refine ⟨23437445532795117264113875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124999709508240625408607333 23437445532795117264113875)
          ·
            refine ⟨35156168299192675896170813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23437445532795117264113875 35156168299192675896170813)
            ·
              refine ⟨13183563112197253461064055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35156168299192675896170813 13183563112197253461064055)
              ·
                refine ⟨19775344668295880191596083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13183563112197253461064055 19775344668295880191596083)
                ·
                  refine ⟨29663017002443820287394125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19775344668295880191596083 29663017002443820287394125)
                  ·
                    refine ⟨11123631375916432607772797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29663017002443820287394125 11123631375916432607772797)
                    ·
                      refine ⟨4171361765968662227914799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11123631375916432607772797 4171361765968662227914799)
                      ·
                        rfl

theorem cell23_8123698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_8123698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123698 prefixEnd_8123698 := by exact prefixLift 8123698
  have htrace : WordTrace (prefixWord ++ tailWord_8123698) baseStart_8123698 baseEnd_8123698 := by
    simpa [prefixWord, tailWord_8123698, baseEnd_8123698] using wordTrace_append hprefix tailTrace_8123698
  have hstable : (prefixWord ++ tailWord_8123698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123698).length < 2 ^ (prefixWord ++ tailWord_8123698).sum := by decide
  have hdescent : baseEnd_8123698 < baseStart_8123698 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123705 : List Nat := [1, 2, 1, 6, 3, 1, 2, 7]
def baseStart_8123705 : Nat := 118140960795 + 8123705 * 2 ^ 59
def prefixEnd_8123705 : Nat := 4983230072969 + 3 ^ 40 * 8123705 * 2
def baseEnd_8123705 : Nat := 154495013345675692612121

theorem tailTrace_8123705 : CollatzResearch.WordTrace tailWord_8123705 prefixEnd_8123705 154495013345675692612121 := by
  unfold tailWord_8123705
  simp only [CollatzResearch.WordTrace]
  refine ⟨296295863034211678201092569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197530575356141118800728379 296295863034211678201092569)
  ·
    refine ⟨222221897275658758650819427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296295863034211678201092569 222221897275658758650819427)
    ·
      refine ⟨333332845913488137976229141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222221897275658758650819427 333332845913488137976229141)
      ·
        refine ⟨15624977152194756467635741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 333332845913488137976229141 15624977152194756467635741)
        ·
          refine ⟨5859366432073033675363403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15624977152194756467635741 5859366432073033675363403)
          ·
            refine ⟨8789049648109550513045105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5859366432073033675363403 8789049648109550513045105)
            ·
              refine ⟨6591787236082162884783829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8789049648109550513045105 6591787236082162884783829)
              ·
                refine ⟨154495013345675692612121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6591787236082162884783829 154495013345675692612121)
                ·
                  rfl

theorem cell23_8123705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 7].length) (baseStart_8123705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123705 prefixEnd_8123705 := by exact prefixLift 8123705
  have htrace : WordTrace (prefixWord ++ tailWord_8123705) baseStart_8123705 baseEnd_8123705 := by
    simpa [prefixWord, tailWord_8123705, baseEnd_8123705] using wordTrace_append hprefix tailTrace_8123705
  have hstable : (prefixWord ++ tailWord_8123705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123705).length < 2 ^ (prefixWord ++ tailWord_8123705).sum := by decide
  have hdescent : baseEnd_8123705 < baseStart_8123705 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123716 : List Nat := [2, 3, 4, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_8123716 : Nat := 118140960795 + 8123716 * 2 ^ 59
def prefixEnd_8123716 : Nat := 4983230072969 + 3 ^ 40 * 8123716 * 2
def baseEnd_8123716 : Nat := 4171371008620443157489717

theorem tailTrace_8123716 : CollatzResearch.WordTrace tailWord_8123716 prefixEnd_8123716 4171371008620443157489717 := by
  unfold tailWord_8123716
  simp only [CollatzResearch.WordTrace]
  refine ⟨148148132118585913539871501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197530842824781218053162001 148148132118585913539871501)
  ·
    refine ⟨55555549544469717577451813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148148132118585913539871501 55555549544469717577451813)
    ·
      refine ⟨10416665539588072045772215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55555549544469717577451813 10416665539588072045772215)
      ·
        refine ⟨15624998309382108068658323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10416665539588072045772215 15624998309382108068658323)
        ·
          refine ⟨23437497464073162102987485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15624998309382108068658323 23437497464073162102987485)
          ·
            refine ⟨8789061549027435788620307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23437497464073162102987485 8789061549027435788620307)
            ·
              refine ⟨13183592323541153682930461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8789061549027435788620307 13183592323541153682930461)
              ·
                refine ⟨4943847121327932631098923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13183592323541153682930461 4943847121327932631098923)
                ·
                  refine ⟨7415770681991898946648385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4943847121327932631098923 7415770681991898946648385)
                  ·
                    refine ⟨5561828011493924209986289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7415770681991898946648385 5561828011493924209986289)
                    ·
                      refine ⟨4171371008620443157489717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5561828011493924209986289 4171371008620443157489717)
                      ·
                        rfl

theorem cell23_8123716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_8123716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123716 prefixEnd_8123716 := by exact prefixLift 8123716
  have htrace : WordTrace (prefixWord ++ tailWord_8123716) baseStart_8123716 baseEnd_8123716 := by
    simpa [prefixWord, tailWord_8123716, baseEnd_8123716] using wordTrace_append hprefix tailTrace_8123716
  have hstable : (prefixWord ++ tailWord_8123716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123716).length < 2 ^ (prefixWord ++ tailWord_8123716).sum := by decide
  have hdescent : baseEnd_8123716 < baseStart_8123716 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123801 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 1, 2, 5]
def baseStart_8123801 : Nat := 118140960795 + 8123801 * 2 ^ 59
def prefixEnd_8123801 : Nat := 4983230072969 + 3 ^ 40 * 8123801 * 2
def baseEnd_8123801 : Nat := 4171414654476075324926825

theorem tailTrace_8123801 : CollatzResearch.WordTrace tailWord_8123801 prefixEnd_8123801 4171414654476075324926825 := by
  unfold tailWord_8123801
  simp only [CollatzResearch.WordTrace]
  refine ⟨296299364441863886596587257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197532909627909257731058171 296299364441863886596587257)
  ·
    refine ⟨222224523331397914947440443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296299364441863886596587257 222224523331397914947440443)
    ·
      refine ⟨333336784997096872421160665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222224523331397914947440443 333336784997096872421160665)
      ·
        refine ⟨250002588747822654315870499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333336784997096872421160665 250002588747822654315870499)
        ·
          refine ⟨375003883121733981473805749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250002588747822654315870499 375003883121733981473805749)
          ·
            refine ⟨35156614042662560763169289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 375003883121733981473805749 35156614042662560763169289)
            ·
              refine ⟨26367460531996920572376967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35156614042662560763169289 26367460531996920572376967)
              ·
                refine ⟨39551190797995380858565451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26367460531996920572376967 39551190797995380858565451)
                ·
                  refine ⟨59326786196993071287848177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39551190797995380858565451 59326786196993071287848177)
                  ·
                    refine ⟨44495089647744803465886133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59326786196993071287848177 44495089647744803465886133)
                    ·
                      refine ⟨4171414654476075324926825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44495089647744803465886133 4171414654476075324926825)
                      ·
                        rfl

theorem cell23_8123801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_8123801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123801 prefixEnd_8123801 := by exact prefixLift 8123801
  have htrace : WordTrace (prefixWord ++ tailWord_8123801) baseStart_8123801 baseEnd_8123801 := by
    simpa [prefixWord, tailWord_8123801, baseEnd_8123801] using wordTrace_append hprefix tailTrace_8123801
  have hstable : (prefixWord ++ tailWord_8123801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123801).length < 2 ^ (prefixWord ++ tailWord_8123801).sum := by decide
  have hdescent : baseEnd_8123801 < baseStart_8123801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123811 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 4]
def baseStart_8123811 : Nat := 118140960795 + 8123811 * 2 ^ 59
def prefixEnd_8123811 : Nat := 4983230072969 + 3 ^ 40 * 8123811 * 2
def baseEnd_8123811 : Nat := 4171419789282620285801779

theorem tailTrace_8123811 : CollatzResearch.WordTrace tailWord_8123811 prefixEnd_8123811 4171419789282620285801779 := by
  unfold tailWord_8123811
  simp only [CollatzResearch.WordTrace]
  refine ⟨296299729171827658304451287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197533152781218438869634191 296299729171827658304451287)
  ·
    refine ⟨444449593757741487456676931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296299729171827658304451287 444449593757741487456676931)
    ·
      refine ⟨666674390636612231185015397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444449593757741487456676931 666674390636612231185015397)
      ·
        refine ⟨125001448244364793347190387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 666674390636612231185015397 125001448244364793347190387)
        ·
          refine ⟨187502172366547190020785581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125001448244364793347190387 187502172366547190020785581)
          ·
            refine ⟨70313314637455196257794593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187502172366547190020785581 70313314637455196257794593)
            ·
              refine ⟨52734985978091397193345945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70313314637455196257794593 52734985978091397193345945)
              ·
                refine ⟨39551239483568547895009459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52734985978091397193345945 39551239483568547895009459)
                ·
                  refine ⟨59326859225352821842514189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39551239483568547895009459 59326859225352821842514189)
                  ·
                    refine ⟨22247572209507308190942821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59326859225352821842514189 22247572209507308190942821)
                    ·
                      refine ⟨4171419789282620285801779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22247572209507308190942821 4171419789282620285801779)
                      ·
                        rfl

theorem cell23_8123811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_8123811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123811 prefixEnd_8123811 := by exact prefixLift 8123811
  have htrace : WordTrace (prefixWord ++ tailWord_8123811) baseStart_8123811 baseEnd_8123811 := by
    simpa [prefixWord, tailWord_8123811, baseEnd_8123811] using wordTrace_append hprefix tailTrace_8123811
  have hstable : (prefixWord ++ tailWord_8123811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123811).length < 2 ^ (prefixWord ++ tailWord_8123811).sum := by decide
  have hdescent : baseEnd_8123811 < baseStart_8123811 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123838 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_8123838 : Nat := 118140960795 + 8123838 * 2 ^ 59
def prefixEnd_8123838 : Nat := 4983230072969 + 3 ^ 40 * 8123838 * 2
def baseEnd_8123838 : Nat := 1390477884420097226721385

theorem tailTrace_8123838 : CollatzResearch.WordTrace tailWord_8123838 prefixEnd_8123838 1390477884420097226721385 := by
  unfold tailWord_8123838
  simp only [CollatzResearch.WordTrace]
  refine ⟨37037589242841230239460521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197533809295153227943789445 37037589242841230239460521)
  ·
    refine ⟨27778191932130922679595391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37037589242841230239460521 27778191932130922679595391)
    ·
      refine ⟨41667287898196384019393087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27778191932130922679595391 41667287898196384019393087)
      ·
        refine ⟨62500931847294576029089631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41667287898196384019393087 62500931847294576029089631)
        ·
          refine ⟨93751397770941864043634447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62500931847294576029089631 93751397770941864043634447)
          ·
            refine ⟨140627096656412796065451671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93751397770941864043634447 140627096656412796065451671)
            ·
              refine ⟨210940644984619194098177507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140627096656412796065451671 210940644984619194098177507)
              ·
                refine ⟨316410967476928791147266261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210940644984619194098177507 316410967476928791147266261)
                ·
                  refine ⟨7415882050240518542514053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 316410967476928791147266261 7415882050240518542514053)
                  ·
                    refine ⟨1390477884420097226721385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7415882050240518542514053 1390477884420097226721385)
                    ·
                      rfl

theorem cell23_8123838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_8123838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123838 prefixEnd_8123838 := by exact prefixLift 8123838
  have htrace : WordTrace (prefixWord ++ tailWord_8123838) baseStart_8123838 baseEnd_8123838 := by
    simpa [prefixWord, tailWord_8123838, baseEnd_8123838] using wordTrace_append hprefix tailTrace_8123838
  have hstable : (prefixWord ++ tailWord_8123838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123838).length < 2 ^ (prefixWord ++ tailWord_8123838).sum := by decide
  have hdescent : baseEnd_8123838 < baseStart_8123838 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123848 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 4, 2, 3]
def baseStart_8123848 : Nat := 118140960795 + 8123848 * 2 ^ 59
def prefixEnd_8123848 : Nat := 4983230072969 + 3 ^ 40 * 8123848 * 2
def baseEnd_8123848 : Nat := 4171438788066836641039109

theorem tailTrace_8123848 : CollatzResearch.WordTrace tailWord_8123848 prefixEnd_8123848 4171438788066836641039109 := by
  unfold tailWord_8123848
  simp only [CollatzResearch.WordTrace]
  refine ⟨148150539336346806811774099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197534052448462409082365465 148150539336346806811774099)
  ·
    refine ⟨222225809004520210217661149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148150539336346806811774099 222225809004520210217661149)
    ·
      refine ⟨83334678376695078831622931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222225809004520210217661149 83334678376695078831622931)
      ·
        refine ⟨125002017565042618247434397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83334678376695078831622931 125002017565042618247434397)
        ·
          refine ⟨46875756586890981842787899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125002017565042618247434397 46875756586890981842787899)
          ·
            refine ⟨70313634880336472764181849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46875756586890981842787899 70313634880336472764181849)
            ·
              refine ⟨52735226160252354573136387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70313634880336472764181849 52735226160252354573136387)
              ·
                refine ⟨79102839240378531859704581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52735226160252354573136387 79102839240378531859704581)
                ·
                  refine ⟨14831782357570974723694609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79102839240378531859704581 14831782357570974723694609)
                  ·
                    refine ⟨11123836768178231042770957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14831782357570974723694609 11123836768178231042770957)
                    ·
                      refine ⟨4171438788066836641039109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11123836768178231042770957 4171438788066836641039109)
                      ·
                        rfl

theorem cell23_8123848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_8123848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123848 prefixEnd_8123848 := by exact prefixLift 8123848
  have htrace : WordTrace (prefixWord ++ tailWord_8123848) baseStart_8123848 baseEnd_8123848 := by
    simpa [prefixWord, tailWord_8123848, baseEnd_8123848] using wordTrace_append hprefix tailTrace_8123848
  have hstable : (prefixWord ++ tailWord_8123848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123848).length < 2 ^ (prefixWord ++ tailWord_8123848).sum := by decide
  have hdescent : baseEnd_8123848 < baseStart_8123848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123855 : List Nat := [1, 1, 2, 1, 1, 4, 4, 4, 1, 4]
def baseStart_8123855 : Nat := 118140960795 + 8123855 * 2 ^ 59
def prefixEnd_8123855 : Nat := 4983230072969 + 3 ^ 40 * 8123855 * 2
def baseEnd_8123855 : Nat := 1390480794143806037883859

theorem tailTrace_8123855 : CollatzResearch.WordTrace tailWord_8123855 prefixEnd_8123855 1390480794143806037883859 := by
  unfold tailWord_8123855
  simp only [CollatzResearch.WordTrace]
  refine ⟨296301333983668253819053019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197534222655778835879368679 296301333983668253819053019)
  ·
    refine ⟨444452000975502380728579529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296301333983668253819053019 444452000975502380728579529)
    ·
      refine ⟨333339000731626785546434647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444452000975502380728579529 333339000731626785546434647)
      ·
        refine ⟨500008501097440178319651971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333339000731626785546434647 500008501097440178319651971)
        ·
          refine ⟨750012751646160267479477957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500008501097440178319651971 750012751646160267479477957)
          ·
            refine ⟨140627390933655050152402117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 750012751646160267479477957 140627390933655050152402117)
            ·
              refine ⟨26367635800060321903575397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140627390933655050152402117 26367635800060321903575397)
              ·
                refine ⟨4943931712511310356920387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26367635800060321903575397 4943931712511310356920387)
                ·
                  refine ⟨7415897568766965535380581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4943931712511310356920387 7415897568766965535380581)
                  ·
                    refine ⟨1390480794143806037883859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7415897568766965535380581 1390480794143806037883859)
                    ·
                      rfl

theorem cell23_8123855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 1, 4].length) (baseStart_8123855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123855 prefixEnd_8123855 := by exact prefixLift 8123855
  have htrace : WordTrace (prefixWord ++ tailWord_8123855) baseStart_8123855 baseEnd_8123855 := by
    simpa [prefixWord, tailWord_8123855, baseEnd_8123855] using wordTrace_append hprefix tailTrace_8123855
  have hstable : (prefixWord ++ tailWord_8123855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123855).length < 2 ^ (prefixWord ++ tailWord_8123855).sum := by decide
  have hdescent : baseEnd_8123855 < baseStart_8123855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123862 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_8123862 : Nat := 118140960795 + 8123862 * 2 ^ 59
def prefixEnd_8123862 : Nat := 4983230072969 + 3 ^ 40 * 8123862 * 2
def baseEnd_8123862 : Nat := 4171445976795999586264045

theorem tailTrace_8123862 : CollatzResearch.WordTrace tailWord_8123862 prefixEnd_8123862 4171445976795999586264045 := by
  unfold tailWord_8123862
  simp only [CollatzResearch.WordTrace]
  refine ⟨18518849330915180875909865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197534392863095262676371893 18518849330915180875909865)
  ·
    refine ⟨13889136998186385656932399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18518849330915180875909865 13889136998186385656932399)
    ·
      refine ⟨20833705497279578485398599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13889136998186385656932399 20833705497279578485398599)
      ·
        refine ⟨31250558245919367728097899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20833705497279578485398599 31250558245919367728097899)
        ·
          refine ⟨46875837368879051592146849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31250558245919367728097899 46875837368879051592146849)
          ·
            refine ⟨35156878026659288694110137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46875837368879051592146849 35156878026659288694110137)
            ·
              refine ⟨26367658519994466520582603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35156878026659288694110137 26367658519994466520582603)
              ·
                refine ⟨39551487779991699780873905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26367658519994466520582603 39551487779991699780873905)
                ·
                  refine ⟨29663615834993774835655429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39551487779991699780873905 29663615834993774835655429)
                  ·
                    refine ⟨5561927969061332781685393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29663615834993774835655429 5561927969061332781685393)
                    ·
                      refine ⟨4171445976795999586264045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5561927969061332781685393 4171445976795999586264045)
                      ·
                        rfl

theorem cell23_8123862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_8123862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123862 prefixEnd_8123862 := by exact prefixLift 8123862
  have htrace : WordTrace (prefixWord ++ tailWord_8123862) baseStart_8123862 baseEnd_8123862 := by
    simpa [prefixWord, tailWord_8123862, baseEnd_8123862] using wordTrace_append hprefix tailTrace_8123862
  have hstable : (prefixWord ++ tailWord_8123862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123862).length < 2 ^ (prefixWord ++ tailWord_8123862).sum := by decide
  have hdescent : baseEnd_8123862 < baseStart_8123862 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123871 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 6]
def baseStart_8123871 : Nat := 118140960795 + 8123871 * 2 ^ 59
def prefixEnd_8123871 : Nat := 4983230072969 + 3 ^ 40 * 8123871 * 2
def baseEnd_8123871 : Nat := 4171450598121890051051503

theorem tailTrace_8123871 : CollatzResearch.WordTrace tailWord_8123871 prefixEnd_8123871 4171450598121890051051503 := by
  unfold tailWord_8123871
  simp only [CollatzResearch.WordTrace]
  refine ⟨296301917551610288551635467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197534611701073525701090311 296301917551610288551635467)
  ·
    refine ⟨444452876327415432827453201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296301917551610288551635467 444452876327415432827453201)
    ·
      refine ⟨333339657245561574620589901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444452876327415432827453201 333339657245561574620589901)
      ·
        refine ⟨125002371467085590482721213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333339657245561574620589901 125002371467085590482721213)
        ·
          refine ⟨46875889300157096431020455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125002371467085590482721213 46875889300157096431020455)
          ·
            refine ⟨70313833950235644646530683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46875889300157096431020455 70313833950235644646530683)
            ·
              refine ⟨105470750925353466969796025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70313833950235644646530683 105470750925353466969796025)
              ·
                refine ⟨79103063194015100227347019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105470750925353466969796025 79103063194015100227347019)
                ·
                  refine ⟨118654594791022650341020529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79103063194015100227347019 118654594791022650341020529)
                  ·
                    refine ⟨88990946093266987755765397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118654594791022650341020529 88990946093266987755765397)
                    ·
                      refine ⟨4171450598121890051051503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88990946093266987755765397 4171450598121890051051503)
                      ·
                        rfl

theorem cell23_8123871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_8123871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123871 prefixEnd_8123871 := by exact prefixLift 8123871
  have htrace : WordTrace (prefixWord ++ tailWord_8123871) baseStart_8123871 baseEnd_8123871 := by
    simpa [prefixWord, tailWord_8123871, baseEnd_8123871] using wordTrace_append hprefix tailTrace_8123871
  have hstable : (prefixWord ++ tailWord_8123871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123871).length < 2 ^ (prefixWord ++ tailWord_8123871).sum := by decide
  have hdescent : baseEnd_8123871 < baseStart_8123871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123881 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 7, 5]
def baseStart_8123881 : Nat := 118140960795 + 8123881 * 2 ^ 59
def prefixEnd_8123881 : Nat := 4983230072969 + 3 ^ 40 * 8123881 * 2
def baseEnd_8123881 : Nat := 1390485244309478337308819

theorem tailTrace_8123881 : CollatzResearch.WordTrace tailWord_8123881 prefixEnd_8123881 1390485244309478337308819 := by
  unfold tailWord_8123881
  simp only [CollatzResearch.WordTrace]
  refine ⟨296302282281574060259499497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197534854854382706839666331 296302282281574060259499497)
  ·
    refine ⟨222226711711180545194624623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296302282281574060259499497 222226711711180545194624623)
    ·
      refine ⟨333340067566770817791936935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222226711711180545194624623 333340067566770817791936935)
      ·
        refine ⟨500010101350156226687905403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333340067566770817791936935 500010101350156226687905403)
        ·
          refine ⟨750015152025234340031858105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500010101350156226687905403 750015152025234340031858105)
          ·
            refine ⟨562511364018925755023893579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 750015152025234340031858105 562511364018925755023893579)
            ·
              refine ⟨843767046028388632535840369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562511364018925755023893579 843767046028388632535840369)
              ·
                refine ⟨632825284521291474401880277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843767046028388632535840369 632825284521291474401880277)
                ·
                  refine ⟨14831842605967768931294069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 632825284521291474401880277 14831842605967768931294069)
                  ·
                    refine ⟨1390485244309478337308819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14831842605967768931294069 1390485244309478337308819)
                    ·
                      rfl

theorem cell23_8123881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 5].length) (baseStart_8123881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123881 prefixEnd_8123881 := by exact prefixLift 8123881
  have htrace : WordTrace (prefixWord ++ tailWord_8123881) baseStart_8123881 baseEnd_8123881 := by
    simpa [prefixWord, tailWord_8123881, baseEnd_8123881] using wordTrace_append hprefix tailTrace_8123881
  have hstable : (prefixWord ++ tailWord_8123881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123881).length < 2 ^ (prefixWord ++ tailWord_8123881).sum := by decide
  have hdescent : baseEnd_8123881 < baseStart_8123881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123898 : List Nat := [3, 1, 1, 1, 1, 2, 3, 5, 1, 5]
def baseStart_8123898 : Nat := 118140960795 + 8123898 * 2 ^ 59
def prefixEnd_8123898 : Nat := 4983230072969 + 3 ^ 40 * 8123898 * 2
def baseEnd_8123898 : Nat := 1390488154033187148471293

theorem tailTrace_8123898 : CollatzResearch.WordTrace tailWord_8123898 prefixEnd_8123898 1390488154033187148471293 := by
  unfold tailWord_8123898
  simp only [CollatzResearch.WordTrace]
  refine ⟨74075725580628118040717087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197535268215008314775245565 74075725580628118040717087)
  ·
    refine ⟨111113588370942177061075631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74075725580628118040717087 111113588370942177061075631)
    ·
      refine ⟨166670382556413265591613447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111113588370942177061075631 166670382556413265591613447)
      ·
        refine ⟨250005573834619898387420171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166670382556413265591613447 250005573834619898387420171)
        ·
          refine ⟨375008360751929847581130257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250005573834619898387420171 375008360751929847581130257)
          ·
            refine ⟨281256270563947385685847693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375008360751929847581130257 281256270563947385685847693)
            ·
              refine ⟨105471101461480269632192885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281256270563947385685847693 105471101461480269632192885)
              ·
                refine ⟨9887915762013775278018083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105471101461480269632192885 9887915762013775278018083)
                ·
                  refine ⟨14831873643020662917027125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9887915762013775278018083 14831873643020662917027125)
                  ·
                    refine ⟨1390488154033187148471293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14831873643020662917027125 1390488154033187148471293)
                    ·
                      rfl

theorem cell23_8123898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_8123898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123898 prefixEnd_8123898 := by exact prefixLift 8123898
  have htrace : WordTrace (prefixWord ++ tailWord_8123898) baseStart_8123898 baseEnd_8123898 := by
    simpa [prefixWord, tailWord_8123898, baseEnd_8123898] using wordTrace_append hprefix tailTrace_8123898
  have hstable : (prefixWord ++ tailWord_8123898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123898).length < 2 ^ (prefixWord ++ tailWord_8123898).sum := by decide
  have hdescent : baseEnd_8123898 < baseStart_8123898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123906 : List Nat := [3, 4, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_8123906 : Nat := 118140960795 + 8123906 * 2 ^ 59
def prefixEnd_8123906 : Nat := 4983230072969 + 3 ^ 40 * 8123906 * 2
def baseEnd_8123906 : Nat := 1390489523314932471371281

theorem tailTrace_8123906 : CollatzResearch.WordTrace tailWord_8123906 prefixEnd_8123906 1390489523314932471371281 := by
  unfold tailWord_8123906
  simp only [CollatzResearch.WordTrace]
  refine ⟨74075798526620872382289893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197535462737655659686106381 74075798526620872382289893)
  ·
    refine ⟨13889212223741413571679355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74075798526620872382289893 13889212223741413571679355)
    ·
      refine ⟨20833818335612120357519033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13889212223741413571679355 20833818335612120357519033)
      ·
        refine ⟨15625363751709090268139275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20833818335612120357519033 15625363751709090268139275)
        ·
          refine ⟨23438045627563635402208913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15625363751709090268139275 23438045627563635402208913)
          ·
            refine ⟨17578534220672726551656685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23438045627563635402208913 17578534220672726551656685)
            ·
              refine ⟨6591950332752272456871257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17578534220672726551656685 6591950332752272456871257)
              ·
                refine ⟨4943962749564204342653443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6591950332752272456871257 4943962749564204342653443)
                ·
                  refine ⟨7415944124346306513980165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4943962749564204342653443 7415944124346306513980165)
                  ·
                    refine ⟨1390489523314932471371281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7415944124346306513980165 1390489523314932471371281)
                    ·
                      rfl

theorem cell23_8123906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_8123906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123906 prefixEnd_8123906 := by exact prefixLift 8123906
  have htrace : WordTrace (prefixWord ++ tailWord_8123906) baseStart_8123906 baseEnd_8123906 := by
    simpa [prefixWord, tailWord_8123906, baseEnd_8123906] using wordTrace_append hprefix tailTrace_8123906
  have hstable : (prefixWord ++ tailWord_8123906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123906).length < 2 ^ (prefixWord ++ tailWord_8123906).sum := by decide
  have hdescent : baseEnd_8123906 < baseStart_8123906 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123912 : List Nat := [2, 1, 3, 2, 1, 1, 2, 6, 1, 1, 3]
def baseStart_8123912 : Nat := 118140960795 + 8123912 * 2 ^ 59
def prefixEnd_8123912 : Nat := 4983230072969 + 3 ^ 40 * 8123912 * 2
def baseEnd_8123912 : Nat := 4171471650828724390638815

theorem tailTrace_8123912 : CollatzResearch.WordTrace tailWord_8123912 prefixEnd_8123912 4171471650828724390638815 := by
  unfold tailWord_8123912
  simp only [CollatzResearch.WordTrace]
  refine ⟨148151706472230876276938995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197535608629641168369251993 148151706472230876276938995)
  ·
    refine ⟨222227559708346314415408493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148151706472230876276938995 222227559708346314415408493)
    ·
      refine ⟨83335334890629867905778185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222227559708346314415408493 83335334890629867905778185)
      ·
        refine ⟨62501501167972400929333639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83335334890629867905778185 62501501167972400929333639)
        ·
          refine ⟨93752251751958601394000459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62501501167972400929333639 93752251751958601394000459)
          ·
            refine ⟨140628377627937902091000689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93752251751958601394000459 140628377627937902091000689)
            ·
              refine ⟨105471283220953426568250517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140628377627937902091000689 105471283220953426568250517)
              ·
                refine ⟨4943966400982191870386743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105471283220953426568250517 4943966400982191870386743)
                ·
                  refine ⟨7415949601473287805580115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4943966400982191870386743 7415949601473287805580115)
                  ·
                    refine ⟨11123924402209931708370173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7415949601473287805580115 11123924402209931708370173)
                    ·
                      refine ⟨4171471650828724390638815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11123924402209931708370173 4171471650828724390638815)
                      ·
                        rfl

theorem cell23_8123912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_8123912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123912 prefixEnd_8123912 := by exact prefixLift 8123912
  have htrace : WordTrace (prefixWord ++ tailWord_8123912) baseStart_8123912 baseEnd_8123912 := by
    simpa [prefixWord, tailWord_8123912, baseEnd_8123912] using wordTrace_append hprefix tailTrace_8123912
  have hstable : (prefixWord ++ tailWord_8123912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123912).length < 2 ^ (prefixWord ++ tailWord_8123912).sum := by decide
  have hdescent : baseEnd_8123912 < baseStart_8123912 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123935 : List Nat := [1, 1, 2, 4, 1, 1, 5, 2, 1, 1, 4]
def baseStart_8123935 : Nat := 118140960795 + 8123935 * 2 ^ 59
def prefixEnd_8123935 : Nat := 4983230072969 + 3 ^ 40 * 8123935 * 2
def baseEnd_8123935 : Nat := 4171483460883777800651209

theorem tailTrace_8123935 : CollatzResearch.WordTrace tailWord_8123935 prefixEnd_8123935 4171483460883777800651209 := by
  unfold tailWord_8123935
  simp only [CollatzResearch.WordTrace]
  refine ⟨296304251823378427481965259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197536167882252284987976839 296304251823378427481965259)
  ·
    refine ⟨444456377735067641222947889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296304251823378427481965259 444456377735067641222947889)
    ·
      refine ⟨333342283301300730917210917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444456377735067641222947889 333342283301300730917210917)
      ·
        refine ⟨62501678118993887046977047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333342283301300730917210917 62501678118993887046977047)
        ·
          refine ⟨93752517178490830570465571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62501678118993887046977047 93752517178490830570465571)
          ·
            refine ⟨140628775767736245855698357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93752517178490830570465571 140628775767736245855698357)
            ·
              refine ⟨13183947728225273048971721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140628775767736245855698357 13183947728225273048971721)
              ·
                refine ⟨9887960796168954786728791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13183947728225273048971721 9887960796168954786728791)
                ·
                  refine ⟨14831941194253432180093187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9887960796168954786728791 14831941194253432180093187)
                  ·
                    refine ⟨22247911791380148270139781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14831941194253432180093187 22247911791380148270139781)
                    ·
                      refine ⟨4171483460883777800651209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22247911791380148270139781 4171483460883777800651209)
                      ·
                        rfl

theorem cell23_8123935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_8123935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123935 prefixEnd_8123935 := by exact prefixLift 8123935
  have htrace : WordTrace (prefixWord ++ tailWord_8123935) baseStart_8123935 baseEnd_8123935 := by
    simpa [prefixWord, tailWord_8123935, baseEnd_8123935] using wordTrace_append hprefix tailTrace_8123935
  have hstable : (prefixWord ++ tailWord_8123935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123935).length < 2 ^ (prefixWord ++ tailWord_8123935).sum := by decide
  have hdescent : baseEnd_8123935 < baseStart_8123935 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123938 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_8123938 : Nat := 118140960795 + 8123938 * 2 ^ 59
def prefixEnd_8123938 : Nat := 4983230072969 + 3 ^ 40 * 8123938 * 2
def baseEnd_8123938 : Nat := 4171485001325741288913695

theorem tailTrace_8123938 : CollatzResearch.WordTrace tailWord_8123938 prefixEnd_8123938 4171485001325741288913695 := by
  unfold tailWord_8123938
  simp only [CollatzResearch.WordTrace]
  refine ⟨74076090310591889748581117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197536240828245039329549645 74076090310591889748581117)
  ·
    refine ⟨27778533866471958655717919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74076090310591889748581117 27778533866471958655717919)
    ·
      refine ⟨41667800799707937983576879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27778533866471958655717919 41667800799707937983576879)
      ·
        refine ⟨62501701199561906975365319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41667800799707937983576879 62501701199561906975365319)
        ·
          refine ⟨93752551799342860463047979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62501701199561906975365319 93752551799342860463047979)
          ·
            refine ⟨140628827699014290694571969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93752551799342860463047979 140628827699014290694571969)
            ·
              refine ⟨105471620774260718020928977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140628827699014290694571969 105471620774260718020928977)
              ·
                refine ⟨79103715580695538515696733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105471620774260718020928977 79103715580695538515696733)
                ·
                  refine ⟨29663893342760826943386275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79103715580695538515696733 29663893342760826943386275)
                  ·
                    refine ⟨44495840014141240415079413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29663893342760826943386275 44495840014141240415079413)
                    ·
                      refine ⟨4171485001325741288913695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44495840014141240415079413 4171485001325741288913695)
                      ·
                        rfl

theorem cell23_8123938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_8123938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123938 prefixEnd_8123938 := by exact prefixLift 8123938
  have htrace : WordTrace (prefixWord ++ tailWord_8123938) baseStart_8123938 baseEnd_8123938 := by
    simpa [prefixWord, tailWord_8123938, baseEnd_8123938] using wordTrace_append hprefix tailTrace_8123938
  have hstable : (prefixWord ++ tailWord_8123938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123938).length < 2 ^ (prefixWord ++ tailWord_8123938).sum := by decide
  have hdescent : baseEnd_8123938 < baseStart_8123938 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123955 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 1, 1, 5]
def baseStart_8123955 : Nat := 118140960795 + 8123955 * 2 ^ 59
def prefixEnd_8123955 : Nat := 4983230072969 + 3 ^ 40 * 8123955 * 2
def baseEnd_8123955 : Nat := 4171493730496867722401117

theorem tailTrace_8123955 : CollatzResearch.WordTrace tailWord_8123955 prefixEnd_8123955 4171493730496867722401117 := by
  unfold tailWord_8123955
  simp only [CollatzResearch.WordTrace]
  refine ⟨296304981283305970897693319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197536654188870647265128879 296304981283305970897693319)
  ·
    refine ⟨444457471924958956346539979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296304981283305970897693319 444457471924958956346539979)
    ·
      refine ⟨666686207887438434519809969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444457471924958956346539979 666686207887438434519809969)
      ·
        refine ⟨500014655915578825889857477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666686207887438434519809969 500014655915578825889857477)
        ·
          refine ⟨93752747984171029854348277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 500014655915578825889857477 93752747984171029854348277)
          ·
            refine ⟨8789320123516034048845151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93752747984171029854348277 8789320123516034048845151)
            ·
              refine ⟨13183980185274051073267727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8789320123516034048845151 13183980185274051073267727)
              ·
                refine ⟨19775970277911076609901591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13183980185274051073267727 19775970277911076609901591)
                ·
                  refine ⟨29663955416866614914852387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19775970277911076609901591 29663955416866614914852387)
                  ·
                    refine ⟨44495933125299922372278581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29663955416866614914852387 44495933125299922372278581)
                    ·
                      refine ⟨4171493730496867722401117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44495933125299922372278581 4171493730496867722401117)
                      ·
                        rfl

theorem cell23_8123955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 1, 5].length) (baseStart_8123955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123955 prefixEnd_8123955 := by exact prefixLift 8123955
  have htrace : WordTrace (prefixWord ++ tailWord_8123955) baseStart_8123955 baseEnd_8123955 := by
    simpa [prefixWord, tailWord_8123955, baseEnd_8123955] using wordTrace_append hprefix tailTrace_8123955
  have hstable : (prefixWord ++ tailWord_8123955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123955).length < 2 ^ (prefixWord ++ tailWord_8123955).sum := by decide
  have hdescent : baseEnd_8123955 < baseStart_8123955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123958 : List Nat := [5, 1, 2, 1, 14]
def baseStart_8123958 : Nat := 118140960795 + 8123958 * 2 ^ 59
def prefixEnd_8123958 : Nat := 4983230072969 + 3 ^ 40 * 8123958 * 2
def baseEnd_8123958 : Nat := 5722215735169864486507

theorem tailTrace_8123958 : CollatzResearch.WordTrace tailWord_8123958 prefixEnd_8123958 5722215735169864486507 := by
  unfold tailWord_8123958
  simp only [CollatzResearch.WordTrace]
  refine ⟨18519068168893443900628283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197536727134863401606701685 18519068168893443900628283)
  ·
    refine ⟨27778602253340165850942425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18519068168893443900628283 27778602253340165850942425)
    ·
      refine ⟨20833951690005124388206819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27778602253340165850942425 20833951690005124388206819)
      ·
        refine ⟨31250927535007686582310229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20833951690005124388206819 31250927535007686582310229)
        ·
          refine ⟨5722215735169864486507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 31250927535007686582310229 5722215735169864486507)
          ·
            rfl

theorem cell23_8123958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 14].length) (baseStart_8123958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123958 prefixEnd_8123958 := by exact prefixLift 8123958
  have htrace : WordTrace (prefixWord ++ tailWord_8123958) baseStart_8123958 baseEnd_8123958 := by
    simpa [prefixWord, tailWord_8123958, baseEnd_8123958] using wordTrace_append hprefix tailTrace_8123958
  have hstable : (prefixWord ++ tailWord_8123958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123958).length < 2 ^ (prefixWord ++ tailWord_8123958).sum := by decide
  have hdescent : baseEnd_8123958 < baseStart_8123958 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123968 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 3]
def baseStart_8123968 : Nat := 118140960795 + 8123968 * 2 ^ 59
def prefixEnd_8123968 : Nat := 4983230072969 + 3 ^ 40 * 8123968 * 2
def baseEnd_8123968 : Nat := 4171500405745376171538557

theorem tailTrace_8123968 : CollatzResearch.WordTrace tailWord_8123968 prefixEnd_8123968 4171500405745376171538557 := by
  unfold tailWord_8123968
  simp only [CollatzResearch.WordTrace]
  refine ⟨148152727716129437058958279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197536970288172582745277705 148152727716129437058958279)
  ·
    refine ⟨222229091574194155588437419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148152727716129437058958279 222229091574194155588437419)
    ·
      refine ⟨333343637361291233382656129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222229091574194155588437419 333343637361291233382656129)
      ·
        refine ⟨250007728020968425036992097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333343637361291233382656129 250007728020968425036992097)
        ·
          refine ⟨187505796015726318777744073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250007728020968425036992097 187505796015726318777744073)
          ·
            refine ⟨140629347011794739083308055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187505796015726318777744073 140629347011794739083308055)
            ·
              refine ⟨210944020517692108624962083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140629347011794739083308055 210944020517692108624962083)
              ·
                refine ⟨316416030776538162937443125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210944020517692108624962083 316416030776538162937443125)
                ·
                  refine ⟨29664002885300452775385293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 316416030776538162937443125 29664002885300452775385293)
                  ·
                    refine ⟨11124001081987669790769485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29664002885300452775385293 11124001081987669790769485)
                    ·
                      refine ⟨4171500405745376171538557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11124001081987669790769485 4171500405745376171538557)
                      ·
                        rfl

theorem cell23_8123968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_8123968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123968 prefixEnd_8123968 := by exact prefixLift 8123968
  have htrace : WordTrace (prefixWord ++ tailWord_8123968) baseStart_8123968 baseEnd_8123968 := by
    simpa [prefixWord, tailWord_8123968, baseEnd_8123968] using wordTrace_append hprefix tailTrace_8123968
  have hstable : (prefixWord ++ tailWord_8123968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123968).length < 2 ^ (prefixWord ++ tailWord_8123968).sum := by decide
  have hdescent : baseEnd_8123968 < baseStart_8123968 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123975 : List Nat := [1, 1, 4, 1, 5, 2, 1, 8]
def baseStart_8123975 : Nat := 118140960795 + 8123975 * 2 ^ 59
def prefixEnd_8123975 : Nat := 4983230072969 + 3 ^ 40 * 8123975 * 2
def baseEnd_8123975 : Nat := 154500148152220653487075

theorem tailTrace_8123975 : CollatzResearch.WordTrace tailWord_8123975 prefixEnd_8123975 154500148152220653487075 := by
  unfold tailWord_8123975
  simp only [CollatzResearch.WordTrace]
  refine ⟨296305710743233514313421379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197537140495489009542280919 296305710743233514313421379)
  ·
    refine ⟨444458566114850271470132069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296305710743233514313421379 444458566114850271470132069)
    ·
      refine ⟨83335981146534425900649763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 444458566114850271470132069 83335981146534425900649763)
      ·
        refine ⟨125003971719801638850974645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83335981146534425900649763 125003971719801638850974645)
        ·
          refine ⟨11719122348731403642278873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125003971719801638850974645 11719122348731403642278873)
          ·
            refine ⟨8789341761548552731709155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11719122348731403642278873 8789341761548552731709155)
            ·
              refine ⟨13184012642322829097563733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8789341761548552731709155 13184012642322829097563733)
              ·
                refine ⟨154500148152220653487075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13184012642322829097563733 154500148152220653487075)
                ·
                  rfl

theorem cell23_8123975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 8].length) (baseStart_8123975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123975 prefixEnd_8123975 := by exact prefixLift 8123975
  have htrace : WordTrace (prefixWord ++ tailWord_8123975) baseStart_8123975 baseEnd_8123975 := by
    simpa [prefixWord, tailWord_8123975, baseEnd_8123975] using wordTrace_append hprefix tailTrace_8123975
  have hstable : (prefixWord ++ tailWord_8123975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123975).length < 2 ^ (prefixWord ++ tailWord_8123975).sum := by decide
  have hdescent : baseEnd_8123975 < baseStart_8123975 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123985 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 1, 3, 3]
def baseStart_8123985 : Nat := 118140960795 + 8123985 * 2 ^ 59
def prefixEnd_8123985 : Nat := 4983230072969 + 3 ^ 40 * 8123985 * 2
def baseEnd_8123985 : Nat := 4171509134916502605025979

theorem tailTrace_8123985 : CollatzResearch.WordTrace tailWord_8123985 prefixEnd_8123985 4171509134916502605025979 := by
  unfold tailWord_8123985
  simp only [CollatzResearch.WordTrace]
  refine ⟨296306075473197286021285409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197537383648798190680856939 296306075473197286021285409)
  ·
    refine ⟨222229556604897964515964057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296306075473197286021285409 222229556604897964515964057)
    ·
      refine ⟨166672167453673473386973043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222229556604897964515964057 166672167453673473386973043)
      ·
        refine ⟨250008251180510210080459565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166672167453673473386973043 250008251180510210080459565)
        ·
          refine ⟨93753094192691328780172337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250008251180510210080459565 93753094192691328780172337)
          ·
            refine ⟨70314820644518496585129253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93753094192691328780172337 70314820644518496585129253)
            ·
              refine ⟨13184028870847218109711735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70314820644518496585129253 13184028870847218109711735)
              ·
                refine ⟨19776043306270827164567603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13184028870847218109711735 19776043306270827164567603)
                ·
                  refine ⟨29664064959406240746851405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19776043306270827164567603 29664064959406240746851405)
                  ·
                    refine ⟨11124024359777340280069277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29664064959406240746851405 11124024359777340280069277)
                    ·
                      refine ⟨4171509134916502605025979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11124024359777340280069277 4171509134916502605025979)
                      ·
                        rfl

theorem cell23_8123985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_8123985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123985 prefixEnd_8123985 := by exact prefixLift 8123985
  have htrace : WordTrace (prefixWord ++ tailWord_8123985) baseStart_8123985 baseEnd_8123985 := by
    simpa [prefixWord, tailWord_8123985, baseEnd_8123985] using wordTrace_append hprefix tailTrace_8123985
  have hstable : (prefixWord ++ tailWord_8123985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123985).length < 2 ^ (prefixWord ++ tailWord_8123985).sum := by decide
  have hdescent : baseEnd_8123985 < baseStart_8123985 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123988 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_8123988 : Nat := 118140960795 + 8123988 * 2 ^ 59
def prefixEnd_8123988 : Nat := 4983230072969 + 3 ^ 40 * 8123988 * 2
def baseEnd_8123988 : Nat := 1390503558452822031096155

theorem tailTrace_8123988 : CollatzResearch.WordTrace tailWord_8123988 prefixEnd_8123988 1390503558452822031096155 := by
  unfold tailWord_8123988
  simp only [CollatzResearch.WordTrace]
  refine ⟨148153092446093208766822309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197537456594790945022429745 148153092446093208766822309)
  ·
    refine ⟨27778704833642476643779183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148153092446093208766822309 27778704833642476643779183)
    ·
      refine ⟨41668057250463714965668775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27778704833642476643779183 41668057250463714965668775)
      ·
        refine ⟨62502085875695572448503163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41668057250463714965668775 62502085875695572448503163)
        ·
          refine ⟨93753128813543358672754745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62502085875695572448503163 93753128813543358672754745)
          ·
            refine ⟨70314846610157519004566059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93753128813543358672754745 70314846610157519004566059)
            ·
              refine ⟨105472269915236278506849089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70314846610157519004566059 105472269915236278506849089)
              ·
                refine ⟨79104202436427208880136817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105472269915236278506849089 79104202436427208880136817)
                ·
                  refine ⟨59328151827320406660102613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79104202436427208880136817 59328151827320406660102613)
                  ·
                    refine ⟨1390503558452822031096155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59328151827320406660102613 1390503558452822031096155)
                    ·
                      rfl

theorem cell23_8123988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_8123988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123988 prefixEnd_8123988 := by exact prefixLift 8123988
  have htrace : WordTrace (prefixWord ++ tailWord_8123988) baseStart_8123988 baseEnd_8123988 := by
    simpa [prefixWord, tailWord_8123988, baseEnd_8123988] using wordTrace_append hprefix tailTrace_8123988
  have hstable : (prefixWord ++ tailWord_8123988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123988).length < 2 ^ (prefixWord ++ tailWord_8123988).sum := by decide
  have hdescent : baseEnd_8123988 < baseStart_8123988 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8123990 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_8123990 : Nat := 118140960795 + 8123990 * 2 ^ 59
def prefixEnd_8123990 : Nat := 4983230072969 + 3 ^ 40 * 8123990 * 2
def baseEnd_8123990 : Nat := 4171511702319775085463457

theorem tailTrace_8123990 : CollatzResearch.WordTrace tailWord_8123990 prefixEnd_8123990 4171511702319775085463457 := by
  unfold tailWord_8123990
  simp only [CollatzResearch.WordTrace]
  refine ⟨18519141114886198242201089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197537505225452781250144949 18519141114886198242201089)
  ·
    refine ⟨13889355836164648681650817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18519141114886198242201089 13889355836164648681650817)
    ·
      refine ⟨10417016877123486511238113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13889355836164648681650817 10417016877123486511238113)
      ·
        refine ⟨7812762657842614883428585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10417016877123486511238113 7812762657842614883428585)
        ·
          refine ⟨5859571993381961162571439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7812762657842614883428585 5859571993381961162571439)
          ·
            refine ⟨8789357990072941743857159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5859571993381961162571439 8789357990072941743857159)
            ·
              refine ⟨13184036985109412615785739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8789357990072941743857159 13184036985109412615785739)
              ·
                refine ⟨19776055477664118923678609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13184036985109412615785739 19776055477664118923678609)
                ·
                  refine ⟨14832041608248089192758957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19776055477664118923678609 14832041608248089192758957)
                  ·
                    refine ⟨5562015603093033447284609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14832041608248089192758957 5562015603093033447284609)
                    ·
                      refine ⟨4171511702319775085463457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5562015603093033447284609 4171511702319775085463457)
                      ·
                        rfl

theorem cell23_8123990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_8123990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8123990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8123990 prefixEnd_8123990 := by exact prefixLift 8123990
  have htrace : WordTrace (prefixWord ++ tailWord_8123990) baseStart_8123990 baseEnd_8123990 := by
    simpa [prefixWord, tailWord_8123990, baseEnd_8123990] using wordTrace_append hprefix tailTrace_8123990
  have hstable : (prefixWord ++ tailWord_8123990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8123990).length < 2 ^ (prefixWord ++ tailWord_8123990).sum := by decide
  have hdescent : baseEnd_8123990 < baseStart_8123990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8123990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124028 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_8124028 : Nat := 118140960795 + 8124028 * 2 ^ 59
def prefixEnd_8124028 : Nat := 4983230072969 + 3 ^ 40 * 8124028 * 2
def baseEnd_8124028 : Nat := 4171531214584645936788281

theorem tailTrace_8124028 : CollatzResearch.WordTrace tailWord_8124028 prefixEnd_8124028 4171531214584645936788281 := by
  unfold tailWord_8124028
  simp only [CollatzResearch.WordTrace]
  refine ⟨148153821906020752182550369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197538429208027669576733825 148153821906020752182550369)
  ·
    refine ⟨111115366429515564136912777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148153821906020752182550369 111115366429515564136912777)
    ·
      refine ⟨83336524822136673102684583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111115366429515564136912777 83336524822136673102684583)
      ·
        refine ⟨125004787233205009654026875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83336524822136673102684583 125004787233205009654026875)
        ·
          refine ⟨187507180849807514481040313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125004787233205009654026875 187507180849807514481040313)
          ·
            refine ⟨140630385637355635860780235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187507180849807514481040313 140630385637355635860780235)
            ·
              refine ⟨210945578456033453791170353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140630385637355635860780235 210945578456033453791170353)
              ·
                refine ⟨158209183842025090343377765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210945578456033453791170353 158209183842025090343377765)
                ·
                  refine ⟨29664221970379704439383331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158209183842025090343377765 29664221970379704439383331)
                  ·
                    refine ⟨44496332955569556659074997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29664221970379704439383331 44496332955569556659074997)
                    ·
                      refine ⟨4171531214584645936788281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44496332955569556659074997 4171531214584645936788281)
                      ·
                        rfl

theorem cell23_8124028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_8124028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124028 prefixEnd_8124028 := by exact prefixLift 8124028
  have htrace : WordTrace (prefixWord ++ tailWord_8124028) baseStart_8124028 baseEnd_8124028 := by
    simpa [prefixWord, tailWord_8124028, baseEnd_8124028] using wordTrace_append hprefix tailTrace_8124028
  have hstable : (prefixWord ++ tailWord_8124028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124028).length < 2 ^ (prefixWord ++ tailWord_8124028).sum := by decide
  have hdescent : baseEnd_8124028 < baseStart_8124028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124036 : List Nat := [2, 3, 2, 1, 4, 1, 3, 1, 2, 1, 3]
def baseStart_8124036 : Nat := 118140960795 + 8124036 * 2 ^ 59
def prefixEnd_8124036 : Nat := 4983230072969 + 3 ^ 40 * 8124036 * 2
def baseEnd_8124036 : Nat := 4171535322429881905488245

theorem tailTrace_8124036 : CollatzResearch.WordTrace tailWord_8124036 prefixEnd_8124036 4171535322429881905488245 := by
  unfold tailWord_8124036
  simp only [CollatzResearch.WordTrace]
  refine ⟨148153967798006260865695981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197538623730675014487594641 148153967798006260865695981)
  ·
    refine ⟨55557737924252347824635993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148153967798006260865695981 55557737924252347824635993)
    ·
      refine ⟨41668303443189260868476995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55557737924252347824635993 41668303443189260868476995)
      ·
        refine ⟨62502455164783891302715493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41668303443189260868476995 62502455164783891302715493)
        ·
          refine ⟨11719210343396979619259155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62502455164783891302715493 11719210343396979619259155)
          ·
            refine ⟨17578815515095469428888733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11719210343396979619259155 17578815515095469428888733)
            ·
              refine ⟨6592055818160801035833275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17578815515095469428888733 6592055818160801035833275)
              ·
                refine ⟨9888083727241201553749913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6592055818160801035833275 9888083727241201553749913)
                ·
                  refine ⟨7416062795430901165312435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9888083727241201553749913 7416062795430901165312435)
                  ·
                    refine ⟨11124094193146351747968653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7416062795430901165312435 11124094193146351747968653)
                    ·
                      refine ⟨4171535322429881905488245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11124094193146351747968653 4171535322429881905488245)
                      ·
                        rfl

theorem cell23_8124036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_8124036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124036 prefixEnd_8124036 := by exact prefixLift 8124036
  have htrace : WordTrace (prefixWord ++ tailWord_8124036) baseStart_8124036 baseEnd_8124036 := by
    simpa [prefixWord, tailWord_8124036, baseEnd_8124036] using wordTrace_append hprefix tailTrace_8124036
  have hstable : (prefixWord ++ tailWord_8124036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124036).length < 2 ^ (prefixWord ++ tailWord_8124036).sum := by decide
  have hdescent : baseEnd_8124036 < baseStart_8124036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124062 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_8124062 : Nat := 118140960795 + 8124062 * 2 ^ 59
def prefixEnd_8124062 : Nat := 4983230072969 + 3 ^ 40 * 8124062 * 2
def baseEnd_8124062 : Nat := 4171548672926898803763125

theorem tailTrace_8124062 : CollatzResearch.WordTrace tailWord_8124062 prefixEnd_8124062 4171548672926898803763125 := by
  unfold tailWord_8124062
  simp only [CollatzResearch.WordTrace]
  refine ⟨37038610486739791021479805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197539255929278885447892293 37038610486739791021479805)
  ·
    refine ⟨13889478932527421633054927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37038610486739791021479805 13889478932527421633054927)
    ·
      refine ⟨20834218398791132449582391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13889478932527421633054927 20834218398791132449582391)
      ·
        refine ⟨31251327598186698674373587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20834218398791132449582391 31251327598186698674373587)
        ·
          refine ⟨46876991397280048011560381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31251327598186698674373587 46876991397280048011560381)
          ·
            refine ⟨17578871773980018004335143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46876991397280048011560381 17578871773980018004335143)
            ·
              refine ⟨26368307660970027006502715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17578871773980018004335143 26368307660970027006502715)
              ·
                refine ⟨39552461491455040509754073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26368307660970027006502715 39552461491455040509754073)
                ·
                  refine ⟨29664346118591280382315555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39552461491455040509754073 29664346118591280382315555)
                  ·
                    refine ⟨44496519177886920573473333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29664346118591280382315555 44496519177886920573473333)
                    ·
                      refine ⟨4171548672926898803763125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44496519177886920573473333 4171548672926898803763125)
                      ·
                        rfl

theorem cell23_8124062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_8124062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124062 prefixEnd_8124062 := by exact prefixLift 8124062
  have htrace : WordTrace (prefixWord ++ tailWord_8124062) baseStart_8124062 baseEnd_8124062 := by
    simpa [prefixWord, tailWord_8124062, baseEnd_8124062] using wordTrace_append hprefix tailTrace_8124062
  have hstable : (prefixWord ++ tailWord_8124062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124062).length < 2 ^ (prefixWord ++ tailWord_8124062).sum := by decide
  have hdescent : baseEnd_8124062 < baseStart_8124062 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124132 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 2, 4, 2]
def baseStart_8124132 : Nat := 118140960795 + 8124132 * 2 ^ 59
def prefixEnd_8124132 : Nat := 4983230072969 + 3 ^ 40 * 8124132 * 2
def baseEnd_8124132 : Nat := 4171584616572713529887803

theorem tailTrace_8124132 : CollatzResearch.WordTrace tailWord_8124132 prefixEnd_8124132 4171584616572713529887803 := by
  unfold tailWord_8124132
  simp only [CollatzResearch.WordTrace]
  refine ⟨148155718501832365063443325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197540958002443153417924433 148155718501832365063443325)
  ·
    refine ⟨55558394438187136898791247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148155718501832365063443325 55558394438187136898791247)
    ·
      refine ⟨83337591657280705348186871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55558394438187136898791247 83337591657280705348186871)
      ·
        refine ⟨125006387485921058022280307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83337591657280705348186871 125006387485921058022280307)
        ·
          refine ⟨187509581228881587033420461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125006387485921058022280307 187509581228881587033420461)
          ·
            refine ⟨70316092960830595137532673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187509581228881587033420461 70316092960830595137532673)
            ·
              refine ⟨52737069720622946353149505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70316092960830595137532673 52737069720622946353149505)
              ·
                refine ⟨39552802290467209764862129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52737069720622946353149505 39552802290467209764862129)
                ·
                  refine ⟨29664601717850407323646597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39552802290467209764862129 29664601717850407323646597)
                  ·
                    refine ⟨5562112822096951373183737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29664601717850407323646597 5562112822096951373183737)
                    ·
                      refine ⟨4171584616572713529887803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5562112822096951373183737 4171584616572713529887803)
                      ·
                        rfl

theorem cell23_8124132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_8124132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124132 prefixEnd_8124132 := by exact prefixLift 8124132
  have htrace : WordTrace (prefixWord ++ tailWord_8124132) baseStart_8124132 baseEnd_8124132 := by
    simpa [prefixWord, tailWord_8124132, baseEnd_8124132] using wordTrace_append hprefix tailTrace_8124132
  have hstable : (prefixWord ++ tailWord_8124132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124132).length < 2 ^ (prefixWord ++ tailWord_8124132).sum := by decide
  have hdescent : baseEnd_8124132 < baseStart_8124132 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124142 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 3, 4]
def baseStart_8124142 : Nat := 118140960795 + 8124142 * 2 ^ 59
def prefixEnd_8124142 : Nat := 4983230072969 + 3 ^ 40 * 8124142 * 2
def baseEnd_8124142 : Nat := 1390529917126419496920919

theorem tailTrace_8124142 : CollatzResearch.WordTrace tailWord_8124142 prefixEnd_8124142 1390529917126419496920919 := by
  unfold tailWord_8124142
  simp only [CollatzResearch.WordTrace]
  refine ⟨37038975216703562729343835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197541201155752334556500453 37038975216703562729343835)
  ·
    refine ⟨55558462825055344094015753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37038975216703562729343835 55558462825055344094015753)
    ·
      refine ⟨41668847118791508070511815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55558462825055344094015753 41668847118791508070511815)
      ·
        refine ⟨62503270678187262105767723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41668847118791508070511815 62503270678187262105767723)
        ·
          refine ⟨93754906017280893158651585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62503270678187262105767723 93754906017280893158651585)
          ·
            refine ⟨70316179512960669868988689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93754906017280893158651585 70316179512960669868988689)
            ·
              refine ⟨52737134634720502401741517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70316179512960669868988689 52737134634720502401741517)
              ·
                refine ⟨19776425488020188400653069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52737134634720502401741517 19776425488020188400653069)
                ·
                  refine ⟨7416159558007570650244901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19776425488020188400653069 7416159558007570650244901)
                  ·
                    refine ⟨1390529917126419496920919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7416159558007570650244901 1390529917126419496920919)
                    ·
                      rfl

theorem cell23_8124142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_8124142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124142 prefixEnd_8124142 := by exact prefixLift 8124142
  have htrace : WordTrace (prefixWord ++ tailWord_8124142) baseStart_8124142 baseEnd_8124142 := by
    simpa [prefixWord, tailWord_8124142, baseEnd_8124142] using wordTrace_append hprefix tailTrace_8124142
  have hstable : (prefixWord ++ tailWord_8124142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124142).length < 2 ^ (prefixWord ++ tailWord_8124142).sum := by decide
  have hdescent : baseEnd_8124142 < baseStart_8124142 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124206 : List Nat := [4, 1, 3, 2, 2, 1, 3, 1, 6]
def baseStart_8124206 : Nat := 118140960795 + 8124206 * 2 ^ 59
def prefixEnd_8124206 : Nat := 4983230072969 + 3 ^ 40 * 8124206 * 2
def baseEnd_8124206 : Nat := 463513623793460693373607

theorem tailTrace_8124206 : CollatzResearch.WordTrace tailWord_8124206 prefixEnd_8124206 463513623793460693373607 := by
  unfold tailWord_8124206
  simp only [CollatzResearch.WordTrace]
  refine ⟨37039267000674580095635059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197542757336931093843386981 37039267000674580095635059)
  ·
    refine ⟨55558900501011870143452589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37039267000674580095635059 55558900501011870143452589)
    ·
      refine ⟨20834587687879451303794721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55558900501011870143452589 20834587687879451303794721)
      ·
        refine ⟨15625940765909588477846041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20834587687879451303794721 15625940765909588477846041)
        ·
          refine ⟨11719455574432191358384531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15625940765909588477846041 11719455574432191358384531)
          ·
            refine ⟨17579183361648287037576797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11719455574432191358384531 17579183361648287037576797)
            ·
              refine ⟨6592193760618107639091299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17579183361648287037576797 6592193760618107639091299)
              ·
                refine ⟨9888290640927161458636949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6592193760618107639091299 9888290640927161458636949)
                ·
                  refine ⟨463513623793460693373607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9888290640927161458636949 463513623793460693373607)
                  ·
                    rfl

theorem cell23_8124206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_8124206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124206 prefixEnd_8124206 := by exact prefixLift 8124206
  have htrace : WordTrace (prefixWord ++ tailWord_8124206) baseStart_8124206 baseEnd_8124206 := by
    simpa [prefixWord, tailWord_8124206, baseEnd_8124206] using wordTrace_append hprefix tailTrace_8124206
  have hstable : (prefixWord ++ tailWord_8124206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124206).length < 2 ^ (prefixWord ++ tailWord_8124206).sum := by decide
  have hdescent : baseEnd_8124206 < baseStart_8124206 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124215 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 1, 6]
def baseStart_8124215 : Nat := 118140960795 + 8124215 * 2 ^ 59
def prefixEnd_8124215 : Nat := 4983230072969 + 3 ^ 40 * 8124215 * 2
def baseEnd_8124215 : Nat := 1390542411822345568383307

theorem tailTrace_8124215 : CollatzResearch.WordTrace tailWord_8124215 prefixEnd_8124215 1390542411822345568383307 := by
  unfold tailWord_8124215
  simp only [CollatzResearch.WordTrace]
  refine ⟨296314464262364035302158099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197542976174909356868105399 296314464262364035302158099)
  ·
    refine ⟨444471696393546052953237149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296314464262364035302158099 444471696393546052953237149)
    ·
      refine ⟨166676886147579769857463931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444471696393546052953237149 166676886147579769857463931)
      ·
        refine ⟨250015329221369654786195897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166676886147579769857463931 250015329221369654786195897)
        ·
          refine ⟨187511496916027241089646923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250015329221369654786195897 187511496916027241089646923)
          ·
            refine ⟨281267245374040861634470385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187511496916027241089646923 281267245374040861634470385)
            ·
              refine ⟨210950434030530646225852789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281267245374040861634470385 210950434030530646225852789)
              ·
                refine ⟨19776603190362248083673699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210950434030530646225852789 19776603190362248083673699)
                ·
                  refine ⟨29664904785543372125510549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19776603190362248083673699 29664904785543372125510549)
                  ·
                    refine ⟨1390542411822345568383307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29664904785543372125510549 1390542411822345568383307)
                    ·
                      rfl

theorem cell23_8124215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_8124215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124215 prefixEnd_8124215 := by exact prefixLift 8124215
  have htrace : WordTrace (prefixWord ++ tailWord_8124215) baseStart_8124215 baseEnd_8124215 := by
    simpa [prefixWord, tailWord_8124215, baseEnd_8124215] using wordTrace_append hprefix tailTrace_8124215
  have hstable : (prefixWord ++ tailWord_8124215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124215).length < 2 ^ (prefixWord ++ tailWord_8124215).sum := by decide
  have hdescent : baseEnd_8124215 < baseStart_8124215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124232 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 4, 4]
def baseStart_8124232 : Nat := 118140960795 + 8124232 * 2 ^ 59
def prefixEnd_8124232 : Nat := 4983230072969 + 3 ^ 40 * 8124232 * 2
def baseEnd_8124232 : Nat := 1390545321546054379545781

theorem tailTrace_8124232 : CollatzResearch.WordTrace tailWord_8124232 prefixEnd_8124232 1390545321546054379545781 := by
  unfold tailWord_8124232
  simp only [CollatzResearch.WordTrace]
  refine ⟨148157542151651223602763475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197543389535534964803684633 148157542151651223602763475)
  ·
    refine ⟨222236313227476835404145213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148157542151651223602763475 222236313227476835404145213)
    ·
      refine ⟨83338617460303813276554455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222236313227476835404145213 83338617460303813276554455)
      ·
        refine ⟨125007926190455719914831683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83338617460303813276554455 125007926190455719914831683)
        ·
          refine ⟨187511889285683579872247525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125007926190455719914831683 187511889285683579872247525)
          ·
            refine ⟨35158479241065671226046411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187511889285683579872247525 35158479241065671226046411)
            ·
              refine ⟨52737718861598506839069617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35158479241065671226046411 52737718861598506839069617)
              ·
                refine ⟨39553289146198880129302213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52737718861598506839069617 39553289146198880129302213)
                ·
                  refine ⟨7416241714912290024244165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39553289146198880129302213 7416241714912290024244165)
                  ·
                    refine ⟨1390545321546054379545781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7416241714912290024244165 1390545321546054379545781)
                    ·
                      rfl

theorem cell23_8124232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_8124232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124232 prefixEnd_8124232 := by exact prefixLift 8124232
  have htrace : WordTrace (prefixWord ++ tailWord_8124232) baseStart_8124232 baseEnd_8124232 := by
    simpa [prefixWord, tailWord_8124232, baseEnd_8124232] using wordTrace_append hprefix tailTrace_8124232
  have hstable : (prefixWord ++ tailWord_8124232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124232).length < 2 ^ (prefixWord ++ tailWord_8124232).sum := by decide
  have hdescent : baseEnd_8124232 < baseStart_8124232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124242 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_8124242 : Nat := 118140960795 + 8124242 * 2 ^ 59
def prefixEnd_8124242 : Nat := 4983230072969 + 3 ^ 40 * 8124242 * 2
def baseEnd_8124242 : Nat := 4171641099444708099512297

theorem tailTrace_8124242 : CollatzResearch.WordTrace tailWord_8124242 prefixEnd_8124242 4171641099444708099512297 := by
  unfold tailWord_8124242
  simp only [CollatzResearch.WordTrace]
  refine ⟨74078862258316554728347745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197543632688844145942260653 74078862258316554728347745)
  ·
    refine ⟨55559146693737416046260809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74078862258316554728347745 55559146693737416046260809)
    ·
      refine ⟨41669360020303062034695607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55559146693737416046260809 41669360020303062034695607)
      ·
        refine ⟨62504040030454593052043411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41669360020303062034695607 62504040030454593052043411)
        ·
          refine ⟨93756060045681889578065117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62504040030454593052043411 93756060045681889578065117)
          ·
            refine ⟨35158522517130708591774419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93756060045681889578065117 35158522517130708591774419)
            ·
              refine ⟨52737783775696062887661629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35158522517130708591774419 52737783775696062887661629)
              ·
                refine ⟨19776668915886023582873111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52737783775696062887661629 19776668915886023582873111)
                ·
                  refine ⟨29665003373829035374309667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19776668915886023582873111 29665003373829035374309667)
                  ·
                    refine ⟨44497505060743553061464501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29665003373829035374309667 44497505060743553061464501)
                    ·
                      refine ⟨4171641099444708099512297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44497505060743553061464501 4171641099444708099512297)
                      ·
                        rfl

theorem cell23_8124242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_8124242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124242 prefixEnd_8124242 := by exact prefixLift 8124242
  have htrace : WordTrace (prefixWord ++ tailWord_8124242) baseStart_8124242 baseEnd_8124242 := by
    simpa [prefixWord, tailWord_8124242, baseEnd_8124242] using wordTrace_append hprefix tailTrace_8124242
  have hstable : (prefixWord ++ tailWord_8124242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124242).length < 2 ^ (prefixWord ++ tailWord_8124242).sum := by decide
  have hdescent : baseEnd_8124242 < baseStart_8124242 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124245 : List Nat := [1, 3, 2, 2, 2, 2, 11]
def baseStart_8124245 : Nat := 118140960795 + 8124245 * 2 ^ 59
def prefixEnd_8124245 : Nat := 4983230072969 + 3 ^ 40 * 8124245 * 2
def baseEnd_8124245 : Nat := 51501760986255204787343

theorem tailTrace_8124245 : CollatzResearch.WordTrace tailWord_8124245 prefixEnd_8124245 51501760986255204787343 := by
  unfold tailWord_8124245
  simp only [CollatzResearch.WordTrace]
  refine ⟨296315558452255350425750189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197543705634836900283833459 296315558452255350425750189)
  ·
    refine ⟨111118334419595756409656321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296315558452255350425750189 111118334419595756409656321)
    ·
      refine ⟨83338750814696817307242241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111118334419595756409656321 83338750814696817307242241)
      ·
        refine ⟨62504063111022612980431681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83338750814696817307242241 62504063111022612980431681)
        ·
          refine ⟨46878047333266959735323761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62504063111022612980431681 46878047333266959735323761)
          ·
            refine ⟨35158535499950219801492821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46878047333266959735323761 35158535499950219801492821)
            ·
              refine ⟨51501760986255204787343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35158535499950219801492821 51501760986255204787343)
              ·
                rfl

theorem cell23_8124245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 11].length) (baseStart_8124245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124245 prefixEnd_8124245 := by exact prefixLift 8124245
  have htrace : WordTrace (prefixWord ++ tailWord_8124245) baseStart_8124245 baseEnd_8124245 := by
    simpa [prefixWord, tailWord_8124245, baseEnd_8124245] using wordTrace_append hprefix tailTrace_8124245
  have hstable : (prefixWord ++ tailWord_8124245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124245).length < 2 ^ (prefixWord ++ tailWord_8124245).sum := by decide
  have hdescent : baseEnd_8124245 < baseStart_8124245 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124256 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 3, 2, 2]
def baseStart_8124256 : Nat := 118140960795 + 8124256 * 2 ^ 59
def prefixEnd_8124256 : Nat := 4983230072969 + 3 ^ 40 * 8124256 * 2
def baseEnd_8124256 : Nat := 4171648288173871044737233

theorem tailTrace_8124256 : CollatzResearch.WordTrace tailWord_8124256 prefixEnd_8124256 4171648288173871044737233 := by
  unfold tailWord_8124256
  simp only [CollatzResearch.WordTrace]
  refine ⟨148157979827607749652200311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197543973103476999536267081 148157979827607749652200311)
  ·
    refine ⟨222236969741411624478300467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148157979827607749652200311 222236969741411624478300467)
    ·
      refine ⟨333355454612117436717450701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222236969741411624478300467 333355454612117436717450701)
      ·
        refine ⟨125008295479544038769044013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333355454612117436717450701 125008295479544038769044013)
        ·
          refine ⟨46878110804829014538391505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125008295479544038769044013 46878110804829014538391505)
          ·
            refine ⟨35158583103621760903793629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46878110804829014538391505 35158583103621760903793629)
            ·
              refine ⟨13184468663858160338922611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35158583103621760903793629 13184468663858160338922611)
              ·
                refine ⟨19776702995787240508383917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13184468663858160338922611 19776702995787240508383917)
                ·
                  refine ⟨7416263623420215190643969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19776702995787240508383917 7416263623420215190643969)
                  ·
                    refine ⟨5562197717565161392982977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7416263623420215190643969 5562197717565161392982977)
                    ·
                      refine ⟨4171648288173871044737233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5562197717565161392982977 4171648288173871044737233)
                      ·
                        rfl

theorem cell23_8124256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_8124256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124256 prefixEnd_8124256 := by exact prefixLift 8124256
  have htrace : WordTrace (prefixWord ++ tailWord_8124256) baseStart_8124256 baseEnd_8124256 := by
    simpa [prefixWord, tailWord_8124256, baseEnd_8124256] using wordTrace_append hprefix tailTrace_8124256
  have hstable : (prefixWord ++ tailWord_8124256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124256).length < 2 ^ (prefixWord ++ tailWord_8124256).sum := by decide
  have hdescent : baseEnd_8124256 < baseStart_8124256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124272 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 3]
def baseStart_8124272 : Nat := 118140960795 + 8124272 * 2 ^ 59
def prefixEnd_8124272 : Nat := 4983230072969 + 3 ^ 40 * 8124272 * 2
def baseEnd_8124272 : Nat := 4171656503864342982137159

theorem tailTrace_8124272 : CollatzResearch.WordTrace tailWord_8124272 prefixEnd_8124272 4171656503864342982137159 := by
  unfold tailWord_8124272
  simp only [CollatzResearch.WordTrace]
  refine ⟨148158271611578767018491535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197544362148771689357988713 148158271611578767018491535)
  ·
    refine ⟨222237407417368150527737303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148158271611578767018491535 222237407417368150527737303)
    ·
      refine ⟨333356111126052225791605955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222237407417368150527737303 333356111126052225791605955)
      ·
        refine ⟨500034166689078338687408933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333356111126052225791605955 500034166689078338687408933)
        ·
          refine ⟨93756406254202188503889175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 500034166689078338687408933 93756406254202188503889175)
          ·
            refine ⟨140634609381303282755833763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93756406254202188503889175 140634609381303282755833763)
            ·
              refine ⟨210951914071954924133750645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140634609381303282755833763 210951914071954924133750645)
              ·
                refine ⟨19776741944245774137539123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210951914071954924133750645 19776741944245774137539123)
                ·
                  refine ⟨29665112916368661206308685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19776741944245774137539123 29665112916368661206308685)
                  ·
                    refine ⟨11124417343638247952365757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29665112916368661206308685 11124417343638247952365757)
                    ·
                      refine ⟨4171656503864342982137159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11124417343638247952365757 4171656503864342982137159)
                      ·
                        rfl

theorem cell23_8124272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 3].length) (baseStart_8124272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124272 prefixEnd_8124272 := by exact prefixLift 8124272
  have htrace : WordTrace (prefixWord ++ tailWord_8124272) baseStart_8124272 baseEnd_8124272 := by
    simpa [prefixWord, tailWord_8124272, baseEnd_8124272] using wordTrace_append hprefix tailTrace_8124272
  have hstable : (prefixWord ++ tailWord_8124272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124272).length < 2 ^ (prefixWord ++ tailWord_8124272).sum := by decide
  have hdescent : baseEnd_8124272 < baseStart_8124272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124286 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_8124286 : Nat := 118140960795 + 8124286 * 2 ^ 59
def prefixEnd_8124286 : Nat := 4983230072969 + 3 ^ 40 * 8124286 * 2
def baseEnd_8124286 : Nat := 4171663692593505927362095

theorem tailTrace_8124286 : CollatzResearch.WordTrace tailWord_8124286 prefixEnd_8124286 4171663692593505927362095 := by
  unfold tailWord_8124286
  simp only [CollatzResearch.WordTrace]
  refine ⟨37039631730638351803499089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197544702563404542951995141 37039631730638351803499089)
  ·
    refine ⟨27779723797978763852624317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37039631730638351803499089 27779723797978763852624317)
    ·
      refine ⟨10417396424242036444734119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27779723797978763852624317 10417396424242036444734119)
      ·
        refine ⟨15626094636363054667101179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10417396424242036444734119 15626094636363054667101179)
        ·
          refine ⟨23439141954544582000651769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15626094636363054667101179 23439141954544582000651769)
          ·
            refine ⟨17579356465908436500488827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23439141954544582000651769 17579356465908436500488827)
            ·
              refine ⟨26369034698862654750733241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17579356465908436500488827 26369034698862654750733241)
              ·
                refine ⟨19776776024146991063049931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26369034698862654750733241 19776776024146991063049931)
                ·
                  refine ⟨29665164036220486594574897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19776776024146991063049931 29665164036220486594574897)
                  ·
                    refine ⟨22248873027165364945931173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29665164036220486594574897 22248873027165364945931173)
                    ·
                      refine ⟨4171663692593505927362095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22248873027165364945931173 4171663692593505927362095)
                      ·
                        rfl

theorem cell23_8124286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_8124286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124286 prefixEnd_8124286 := by exact prefixLift 8124286
  have htrace : WordTrace (prefixWord ++ tailWord_8124286) baseStart_8124286 baseEnd_8124286 := by
    simpa [prefixWord, tailWord_8124286, baseEnd_8124286] using wordTrace_append hprefix tailTrace_8124286
  have hstable : (prefixWord ++ tailWord_8124286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124286).length < 2 ^ (prefixWord ++ tailWord_8124286).sum := by decide
  have hdescent : baseEnd_8124286 < baseStart_8124286 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124316 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 3, 3, 2]
def baseStart_8124316 : Nat := 118140960795 + 8124316 * 2 ^ 59
def prefixEnd_8124316 : Nat := 4983230072969 + 3 ^ 40 * 8124316 * 2
def baseEnd_8124316 : Nat := 4171679097013140809986957

theorem tailTrace_8124316 : CollatzResearch.WordTrace tailWord_8124316 prefixEnd_8124316 4171679097013140809986957 := by
  unfold tailWord_8124316
  simp only [CollatzResearch.WordTrace]
  refine ⟨148159074017499064775792401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197545432023332086367723201 148159074017499064775792401)
  ·
    refine ⟨111119305513124298581844301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148159074017499064775792401 111119305513124298581844301)
    ·
      refine ⟨41669739567421611968191613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111119305513124298581844301 41669739567421611968191613)
      ·
        refine ⟨15626152337783104488071855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41669739567421611968191613 15626152337783104488071855)
        ·
          refine ⟨23439228506674656732107783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15626152337783104488071855 23439228506674656732107783)
          ·
            refine ⟨35158842760011985098161675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23439228506674656732107783 35158842760011985098161675)
            ·
              refine ⟨52738264140017977647242513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35158842760011985098161675 52738264140017977647242513)
              ·
                refine ⟨39553698105013483235431885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52738264140017977647242513 39553698105013483235431885)
                ·
                  refine ⟨14832636789380056213286957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39553698105013483235431885 14832636789380056213286957)
                  ·
                    refine ⟨5562238796017521079982609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14832636789380056213286957 5562238796017521079982609)
                    ·
                      refine ⟨4171679097013140809986957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5562238796017521079982609 4171679097013140809986957)
                      ·
                        rfl

theorem cell23_8124316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_8124316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124316 prefixEnd_8124316 := by exact prefixLift 8124316
  have htrace : WordTrace (prefixWord ++ tailWord_8124316) baseStart_8124316 baseEnd_8124316 := by
    simpa [prefixWord, tailWord_8124316, baseEnd_8124316] using wordTrace_append hprefix tailTrace_8124316
  have hstable : (prefixWord ++ tailWord_8124316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124316).length < 2 ^ (prefixWord ++ tailWord_8124316).sum := by decide
  have hdescent : baseEnd_8124316 < baseStart_8124316 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124350 : List Nat := [4, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2]
def baseStart_8124350 : Nat := 118140960795 + 8124350 * 2 ^ 59
def prefixEnd_8124350 : Nat := 4983230072969 + 3 ^ 40 * 8124350 * 2
def baseEnd_8124350 : Nat := 4171696555355393676961801

theorem tailTrace_8124350 : CollatzResearch.WordTrace tailWord_8124350 prefixEnd_8124350 4171696555355393676961801 := by
  unfold tailWord_8124350
  simp only [CollatzResearch.WordTrace]
  refine ⟨37039923514609369169790313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197546258744583302238881669 37039923514609369169790313)
  ·
    refine ⟨27779942635957026877342735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37039923514609369169790313 27779942635957026877342735)
    ·
      refine ⟨41669913953935540316014103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27779942635957026877342735 41669913953935540316014103)
      ·
        refine ⟨62504870930903310474021155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41669913953935540316014103 62504870930903310474021155)
        ·
          refine ⟨93757306396354965711031733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62504870930903310474021155 93757306396354965711031733)
          ·
            refine ⟨8789747474658278035409225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93757306396354965711031733 8789747474658278035409225)
            ·
              refine ⟨6592310605993708526556919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8789747474658278035409225 6592310605993708526556919)
              ·
                refine ⟨9888465908990562789835379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6592310605993708526556919 9888465908990562789835379)
                ·
                  refine ⟨14832698863485844184753069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9888465908990562789835379 14832698863485844184753069)
                  ·
                    refine ⟨5562262073807191569282401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14832698863485844184753069 5562262073807191569282401)
                    ·
                      refine ⟨4171696555355393676961801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5562262073807191569282401 4171696555355393676961801)
                      ·
                        rfl

theorem cell23_8124350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_8124350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124350 prefixEnd_8124350 := by exact prefixLift 8124350
  have htrace : WordTrace (prefixWord ++ tailWord_8124350) baseStart_8124350 baseEnd_8124350 := by
    simpa [prefixWord, tailWord_8124350, baseEnd_8124350] using wordTrace_append hprefix tailTrace_8124350
  have hstable : (prefixWord ++ tailWord_8124350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124350).length < 2 ^ (prefixWord ++ tailWord_8124350).sum := by decide
  have hdescent : baseEnd_8124350 < baseStart_8124350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124392 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_8124392 : Nat := 118140960795 + 8124392 * 2 ^ 59
def prefixEnd_8124392 : Nat := 4983230072969 + 3 ^ 40 * 8124392 * 2
def baseEnd_8124392 : Nat := 4171718121542882512636607

theorem tailTrace_8124392 : CollatzResearch.WordTrace tailWord_8124392 prefixEnd_8124392 4171718121542882512636607 := by
  unfold tailWord_8124392
  simp only [CollatzResearch.WordTrace]
  refine ⟨148160459991361397265675715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197547279988481863020900953 148160459991361397265675715)
  ·
    refine ⟨222240689987042095898513573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148160459991361397265675715 222240689987042095898513573)
    ·
      refine ⟨41670129372570392980971295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222240689987042095898513573 41670129372570392980971295)
      ·
        refine ⟨62505194058855589471456943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41670129372570392980971295 62505194058855589471456943)
        ·
          refine ⟨93757791088283384207185415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62505194058855589471456943 93757791088283384207185415)
          ·
            refine ⟨140636686632425076310778123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93757791088283384207185415 140636686632425076310778123)
            ·
              refine ⟨210955029948637614466167185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140636686632425076310778123 210955029948637614466167185)
              ·
                refine ⟨158216272461478210849625389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210955029948637614466167185 158216272461478210849625389)
                ·
                  refine ⟨59331102173054329068609521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158216272461478210849625389 59331102173054329068609521)
                  ·
                    refine ⟨44498326629790746801457141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59331102173054329068609521 44498326629790746801457141)
                    ·
                      refine ⟨4171718121542882512636607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44498326629790746801457141 4171718121542882512636607)
                      ·
                        rfl

theorem cell23_8124392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_8124392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124392 prefixEnd_8124392 := by exact prefixLift 8124392
  have htrace : WordTrace (prefixWord ++ tailWord_8124392) baseStart_8124392 baseEnd_8124392 := by
    simpa [prefixWord, tailWord_8124392, baseEnd_8124392] using wordTrace_append hprefix tailTrace_8124392
  have hstable : (prefixWord ++ tailWord_8124392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124392).length < 2 ^ (prefixWord ++ tailWord_8124392).sum := by decide
  have hdescent : baseEnd_8124392 < baseStart_8124392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124419 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 4, 4, 2]
def baseStart_8124419 : Nat := 118140960795 + 8124419 * 2 ^ 59
def prefixEnd_8124419 : Nat := 4983230072969 + 3 ^ 40 * 8124419 * 2
def baseEnd_8124419 : Nat := 4171731985520553906998983

theorem tailTrace_8124419 : CollatzResearch.WordTrace tailWord_8124419 prefixEnd_8124419 4171731985520553906998983 := by
  unfold tailWord_8124419
  simp only [CollatzResearch.WordTrace]
  refine ⟨296321904753624978142584311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197547936502416652095056207 296321904753624978142584311)
  ·
    refine ⟨444482857130437467213876467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296321904753624978142584311 444482857130437467213876467)
    ·
      refine ⟨666724285695656200820814701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444482857130437467213876467 666724285695656200820814701)
      ·
        refine ⟨250021607135871075307805513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 666724285695656200820814701 250021607135871075307805513)
        ·
          refine ⟨187516205351903306480854135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250021607135871075307805513 187516205351903306480854135)
          ·
            refine ⟨281274308027854959721281203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187516205351903306480854135 281274308027854959721281203)
            ·
              refine ⟨421911462041782439581921805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281274308027854959721281203 421911462041782439581921805)
              ·
                refine ⟨158216798265668414843220677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421911462041782439581921805 158216798265668414843220677)
                ·
                  refine ⟨29665649674812827783103877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158216798265668414843220677 29665649674812827783103877)
                  ·
                    refine ⟨5562309314027405209331977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29665649674812827783103877 5562309314027405209331977)
                    ·
                      refine ⟨4171731985520553906998983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5562309314027405209331977 4171731985520553906998983)
                      ·
                        rfl

theorem cell23_8124419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 4, 2].length) (baseStart_8124419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124419 prefixEnd_8124419 := by exact prefixLift 8124419
  have htrace : WordTrace (prefixWord ++ tailWord_8124419) baseStart_8124419 baseEnd_8124419 := by
    simpa [prefixWord, tailWord_8124419, baseEnd_8124419] using wordTrace_append hprefix tailTrace_8124419
  have hstable : (prefixWord ++ tailWord_8124419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124419).length < 2 ^ (prefixWord ++ tailWord_8124419).sum := by decide
  have hdescent : baseEnd_8124419 < baseStart_8124419 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124420 : List Nat := [2, 3, 2, 4, 1, 1, 3, 2, 5]
def baseStart_8124420 : Nat := 118140960795 + 8124420 * 2 ^ 59
def prefixEnd_8124420 : Nat := 4983230072969 + 3 ^ 40 * 8124420 * 2
def baseEnd_8124420 : Nat := 463525833222356489231831

theorem tailTrace_8124420 : CollatzResearch.WordTrace tailWord_8124420 prefixEnd_8124420 463525833222356489231831 := by
  unfold tailWord_8124420
  simp only [CollatzResearch.WordTrace]
  refine ⟨148160970613310677656685357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197547960817747570208913809 148160970613310677656685357)
  ·
    refine ⟨55560363979991504121257009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148160970613310677656685357 55560363979991504121257009)
    ·
      refine ⟨41670272984993628090942757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55560363979991504121257009 41670272984993628090942757)
      ·
        refine ⟨7813176184686305267051767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41670272984993628090942757 7813176184686305267051767)
        ·
          refine ⟨11719764277029457900577651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7813176184686305267051767 11719764277029457900577651)
          ·
            refine ⟨17579646415544186850866477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11719764277029457900577651 17579646415544186850866477)
            ·
              refine ⟨6592367405829070069074929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17579646415544186850866477 6592367405829070069074929)
              ·
                refine ⟨4944275554371802551806197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6592367405829070069074929 4944275554371802551806197)
                ·
                  refine ⟨463525833222356489231831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4944275554371802551806197 463525833222356489231831)
                  ·
                    rfl

theorem cell23_8124420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_8124420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124420 prefixEnd_8124420 := by exact prefixLift 8124420
  have htrace : WordTrace (prefixWord ++ tailWord_8124420) baseStart_8124420 baseEnd_8124420 := by
    simpa [prefixWord, tailWord_8124420, baseEnd_8124420] using wordTrace_append hprefix tailTrace_8124420
  have hstable : (prefixWord ++ tailWord_8124420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124420).length < 2 ^ (prefixWord ++ tailWord_8124420).sum := by decide
  have hdescent : baseEnd_8124420 < baseStart_8124420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124480 : List Nat := [2, 1, 1, 2, 2, 6, 2, 2, 1, 4]
def baseStart_8124480 : Nat := 118140960795 + 8124480 * 2 ^ 59
def prefixEnd_8124480 : Nat := 4983230072969 + 3 ^ 40 * 8124480 * 2
def baseEnd_8124480 : Nat := 1390587769280159389445401

theorem tailTrace_8124480 : CollatzResearch.WordTrace tailWord_8124480 prefixEnd_8124480 1390587769280159389445401 := by
  unfold tailWord_8124480
  simp only [CollatzResearch.WordTrace]
  refine ⟨148162064803201992780277447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197549419737602657040369929 148162064803201992780277447)
  ·
    refine ⟨222243097204802989170416171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148162064803201992780277447 222243097204802989170416171)
    ·
      refine ⟨333364645807204483755624257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222243097204802989170416171 333364645807204483755624257)
      ·
        refine ⟨250023484355403362816718193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333364645807204483755624257 250023484355403362816718193)
        ·
          refine ⟨187517613266552522112538645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250023484355403362816718193 187517613266552522112538645)
          ·
            refine ⟨8789888121869649474025249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187517613266552522112538645 8789888121869649474025249)
            ·
              refine ⟨6592416091402237105518937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8789888121869649474025249 6592416091402237105518937)
              ·
                refine ⟨4944312068551677829139203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6592416091402237105518937 4944312068551677829139203)
                ·
                  refine ⟨7416468102827516743708805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4944312068551677829139203 7416468102827516743708805)
                  ·
                    refine ⟨1390587769280159389445401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7416468102827516743708805 1390587769280159389445401)
                    ·
                      rfl

theorem cell23_8124480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 1, 4].length) (baseStart_8124480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124480 prefixEnd_8124480 := by exact prefixLift 8124480
  have htrace : WordTrace (prefixWord ++ tailWord_8124480) baseStart_8124480 baseEnd_8124480 := by
    simpa [prefixWord, tailWord_8124480, baseEnd_8124480] using wordTrace_append hprefix tailTrace_8124480
  have hstable : (prefixWord ++ tailWord_8124480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124480).length < 2 ^ (prefixWord ++ tailWord_8124480).sum := by decide
  have hdescent : baseEnd_8124480 < baseStart_8124480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124519 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 1, 6]
def baseStart_8124519 : Nat := 118140960795 + 8124519 * 2 ^ 59
def prefixEnd_8124519 : Nat := 4983230072969 + 3 ^ 40 * 8124519 * 2
def baseEnd_8124519 : Nat := 1390594444528667838582841

theorem tailTrace_8124519 : CollatzResearch.WordTrace tailWord_8124519 prefixEnd_8124519 1390594444528667838582841 := by
  unfold tailWord_8124519
  simp only [CollatzResearch.WordTrace]
  refine ⟨296325552053262695221224611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197550368035508463480816407 296325552053262695221224611)
  ·
    refine ⟨444488328079894042831836917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296325552053262695221224611 444488328079894042831836917)
    ·
      refine ⟨41670780757490066515484711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 444488328079894042831836917 41670780757490066515484711)
      ·
        refine ⟨62506171136235099773227067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41670780757490066515484711 62506171136235099773227067)
        ·
          refine ⟨93759256704352649659840601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62506171136235099773227067 93759256704352649659840601)
          ·
            refine ⟨70319442528264487244880451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93759256704352649659840601 70319442528264487244880451)
            ·
              refine ⟨105479163792396730867320677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70319442528264487244880451 105479163792396730867320677)
              ·
                refine ⟨19777343211074387037622627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105479163792396730867320677 19777343211074387037622627)
                ·
                  refine ⟨29666014816611580556433941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19777343211074387037622627 29666014816611580556433941)
                  ·
                    refine ⟨1390594444528667838582841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29666014816611580556433941 1390594444528667838582841)
                    ·
                      rfl

theorem cell23_8124519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_8124519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124519 prefixEnd_8124519 := by exact prefixLift 8124519
  have htrace : WordTrace (prefixWord ++ tailWord_8124519) baseStart_8124519 baseEnd_8124519 := by
    simpa [prefixWord, tailWord_8124519, baseEnd_8124519] using wordTrace_append hprefix tailTrace_8124519
  have hstable : (prefixWord ++ tailWord_8124519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124519).length < 2 ^ (prefixWord ++ tailWord_8124519).sum := by decide
  have hdescent : baseEnd_8124519 < baseStart_8124519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124529 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 1, 1, 5]
def baseStart_8124529 : Nat := 118140960795 + 8124529 * 2 ^ 59
def prefixEnd_8124529 : Nat := 4983230072969 + 3 ^ 40 * 8124529 * 2
def baseEnd_8124529 : Nat := 4171788468392548476623477

theorem tailTrace_8124529 : CollatzResearch.WordTrace tailWord_8124529 prefixEnd_8124529 4171788468392548476623477 := by
  unfold tailWord_8124529
  simp only [CollatzResearch.WordTrace]
  refine ⟨296325916783226466929088641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197550611188817644619392427 296325916783226466929088641)
  ·
    refine ⟨222244437587419850196816481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296325916783226466929088641 222244437587419850196816481)
    ·
      refine ⟨166683328190564887647612361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222244437587419850196816481 166683328190564887647612361)
      ·
        refine ⟨125012496142923665735709271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166683328190564887647612361 125012496142923665735709271)
        ·
          refine ⟨187518744214385498603563907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125012496142923665735709271 187518744214385498603563907)
          ·
            refine ⟨281278116321578247905345861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187518744214385498603563907 281278116321578247905345861)
            ·
              refine ⟨52739646810295921482252349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281278116321578247905345861 52739646810295921482252349)
              ·
                refine ⟨19777367553860970555844631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52739646810295921482252349 19777367553860970555844631)
                ·
                  refine ⟨29666051330791455833766947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19777367553860970555844631 29666051330791455833766947)
                  ·
                    refine ⟨44499076996187183750650421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29666051330791455833766947 44499076996187183750650421)
                    ·
                      refine ⟨4171788468392548476623477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44499076996187183750650421 4171788468392548476623477)
                      ·
                        rfl

theorem cell23_8124529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_8124529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124529 prefixEnd_8124529 := by exact prefixLift 8124529
  have htrace : WordTrace (prefixWord ++ tailWord_8124529) baseStart_8124529 baseEnd_8124529 := by
    simpa [prefixWord, tailWord_8124529, baseEnd_8124529] using wordTrace_append hprefix tailTrace_8124529
  have hstable : (prefixWord ++ tailWord_8124529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124529).length < 2 ^ (prefixWord ++ tailWord_8124529).sum := by decide
  have hdescent : baseEnd_8124529 < baseStart_8124529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124553 : List Nat := [1, 2, 1, 1, 4, 2, 5, 1, 2, 4]
def baseStart_8124553 : Nat := 118140960795 + 8124553 * 2 ^ 59
def prefixEnd_8124553 : Nat := 4983230072969 + 3 ^ 40 * 8124553 * 2
def baseEnd_8124553 : Nat := 1390600263976085460907789

theorem tailTrace_8124553 : CollatzResearch.WordTrace tailWord_8124553 prefixEnd_8124553 1390600263976085460907789 := by
  unfold tailWord_8124553
  simp only [CollatzResearch.WordTrace]
  refine ⟨296326792135139519027962313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197551194756759679351974875 296326792135139519027962313)
  ·
    refine ⟨222245094101354639270971735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296326792135139519027962313 222245094101354639270971735)
    ·
      refine ⟨333367641152031958906457603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222245094101354639270971735 333367641152031958906457603)
      ·
        refine ⟨500051461728047938359686405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333367641152031958906457603 500051461728047938359686405)
        ·
          refine ⟨93759649074008988442441201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 500051461728047938359686405 93759649074008988442441201)
          ·
            refine ⟨70319736805506741331830901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93759649074008988442441201 70319736805506741331830901)
            ·
              refine ⟨6592475325516256999859147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70319736805506741331830901 6592475325516256999859147)
              ·
                refine ⟨9888712988274385499788721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6592475325516256999859147 9888712988274385499788721)
                ·
                  refine ⟨7416534741205789124841541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9888712988274385499788721 7416534741205789124841541)
                  ·
                    refine ⟨1390600263976085460907789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7416534741205789124841541 1390600263976085460907789)
                    ·
                      rfl

theorem cell23_8124553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 2, 4].length) (baseStart_8124553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124553 prefixEnd_8124553 := by exact prefixLift 8124553
  have htrace : WordTrace (prefixWord ++ tailWord_8124553) baseStart_8124553 baseEnd_8124553 := by
    simpa [prefixWord, tailWord_8124553, baseEnd_8124553] using wordTrace_append hprefix tailTrace_8124553
  have hstable : (prefixWord ++ tailWord_8124553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124553).length < 2 ^ (prefixWord ++ tailWord_8124553).sum := by decide
  have hdescent : baseEnd_8124553 < baseStart_8124553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124577 : List Nat := [1, 2, 3, 3, 1, 2, 3, 3, 1, 2, 2]
def baseStart_8124577 : Nat := 118140960795 + 8124577 * 2 ^ 59
def prefixEnd_8124577 : Nat := 4983230072969 + 3 ^ 40 * 8124577 * 2
def baseEnd_8124577 : Nat := 4171813115463964288823257

theorem tailTrace_8124577 : CollatzResearch.WordTrace tailWord_8124577 prefixEnd_8124577 4171813115463964288823257 := by
  unfold tailWord_8124577
  simp only [CollatzResearch.WordTrace]
  refine ⟨296327667487052571126835985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197551778324701714084557323 296327667487052571126835985)
  ·
    refine ⟨222245750615289428345126989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296327667487052571126835985 222245750615289428345126989)
    ·
      refine ⟨83342156480733535629422621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222245750615289428345126989 83342156480733535629422621)
      ·
        refine ⟨31253308680275075861033483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83342156480733535629422621 31253308680275075861033483)
        ·
          refine ⟨46879963020412613791550225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31253308680275075861033483 46879963020412613791550225)
          ·
            refine ⟨35159972265309460343662669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46879963020412613791550225 35159972265309460343662669)
            ·
              refine ⟨13184989599491047628873501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35159972265309460343662669 13184989599491047628873501)
              ·
                refine ⟨4944371099809142860827563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13184989599491047628873501 4944371099809142860827563)
                ·
                  refine ⟨7416556649713714291241345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4944371099809142860827563 7416556649713714291241345)
                  ·
                    refine ⟨5562417487285285718431009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7416556649713714291241345 5562417487285285718431009)
                    ·
                      refine ⟨4171813115463964288823257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5562417487285285718431009 4171813115463964288823257)
                      ·
                        rfl

theorem cell23_8124577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_8124577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124577 prefixEnd_8124577 := by exact prefixLift 8124577
  have htrace : WordTrace (prefixWord ++ tailWord_8124577) baseStart_8124577 baseEnd_8124577 := by
    simpa [prefixWord, tailWord_8124577, baseEnd_8124577] using wordTrace_append hprefix tailTrace_8124577
  have hstable : (prefixWord ++ tailWord_8124577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124577).length < 2 ^ (prefixWord ++ tailWord_8124577).sum := by decide
  have hdescent : baseEnd_8124577 < baseStart_8124577 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124583 : List Nat := [1, 1, 6, 2, 3, 1, 9]
def baseStart_8124583 : Nat := 118140960795 + 8124583 * 2 ^ 59
def prefixEnd_8124583 : Nat := 4983230072969 + 3 ^ 40 * 8124583 * 2
def baseEnd_8124583 : Nat := 51503903658615941547509

theorem tailTrace_8124583 : CollatzResearch.WordTrace tailWord_8124583 prefixEnd_8124583 51503903658615941547509 := by
  unfold tailWord_8124583
  simp only [CollatzResearch.WordTrace]
  refine ⟨296327886325030834151554403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197551924216687222767702935 296327886325030834151554403)
  ·
    refine ⟨444491829487546251227331605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296327886325030834151554403 444491829487546251227331605)
    ·
      refine ⟨20835554507228730526281169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 444491829487546251227331605 20835554507228730526281169)
      ·
        refine ⟨15626665880421547894710877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20835554507228730526281169 15626665880421547894710877)
        ·
          refine ⟨5859999705158080460516579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15626665880421547894710877 5859999705158080460516579)
          ·
            refine ⟨8789999557737120690774869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5859999705158080460516579 8789999557737120690774869)
            ·
              refine ⟨51503903658615941547509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8789999557737120690774869 51503903658615941547509)
              ·
                rfl

theorem cell23_8124583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 9].length) (baseStart_8124583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124583 prefixEnd_8124583 := by exact prefixLift 8124583
  have htrace : WordTrace (prefixWord ++ tailWord_8124583) baseStart_8124583 baseEnd_8124583 := by
    simpa [prefixWord, tailWord_8124583, baseEnd_8124583] using wordTrace_append hprefix tailTrace_8124583
  have hstable : (prefixWord ++ tailWord_8124583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124583).length < 2 ^ (prefixWord ++ tailWord_8124583).sum := by decide
  have hdescent : baseEnd_8124583 < baseStart_8124583 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124619 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 5]
def baseStart_8124619 : Nat := 118140960795 + 8124619 * 2 ^ 59
def prefixEnd_8124619 : Nat := 4983230072969 + 3 ^ 40 * 8124619 * 2
def baseEnd_8124619 : Nat := 4171834681651453124498063

theorem tailTrace_8124619 : CollatzResearch.WordTrace tailWord_8124619 prefixEnd_8124619 4171834681651453124498063 := by
  unfold tailWord_8124619
  simp only [CollatzResearch.WordTrace]
  refine ⟨296329199352900412299864911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197552799568600274866576607 296329199352900412299864911)
  ·
    refine ⟨444493799029350618449797367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296329199352900412299864911 444493799029350618449797367)
    ·
      refine ⟨666740698544025927674696051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444493799029350618449797367 666740698544025927674696051)
      ·
        refine ⟨1000111047816038891512044077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666740698544025927674696051 1000111047816038891512044077)
        ·
          refine ⟨375041642931014584317016529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1000111047816038891512044077 375041642931014584317016529)
          ·
            refine ⟨281281232198260938237762397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375041642931014584317016529 281281232198260938237762397)
            ·
              refine ⟨105480462074347851839160899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281281232198260938237762397 105480462074347851839160899)
              ·
                refine ⟨158220693111521777758741349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105480462074347851839160899 158220693111521777758741349)
                ·
                  refine ⟨29666379958410333329764003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158220693111521777758741349 29666379958410333329764003)
                  ·
                    refine ⟨44499569937615499994646005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29666379958410333329764003 44499569937615499994646005)
                    ·
                      refine ⟨4171834681651453124498063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44499569937615499994646005 4171834681651453124498063)
                      ·
                        rfl

theorem cell23_8124619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 5].length) (baseStart_8124619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124619 prefixEnd_8124619 := by exact prefixLift 8124619
  have htrace : WordTrace (prefixWord ++ tailWord_8124619) baseStart_8124619 baseEnd_8124619 := by
    simpa [prefixWord, tailWord_8124619, baseEnd_8124619] using wordTrace_append hprefix tailTrace_8124619
  have hstable : (prefixWord ++ tailWord_8124619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124619).length < 2 ^ (prefixWord ++ tailWord_8124619).sum := by decide
  have hdescent : baseEnd_8124619 < baseStart_8124619 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124633 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 6, 2, 2]
def baseStart_8124633 : Nat := 118140960795 + 8124633 * 2 ^ 59
def prefixEnd_8124633 : Nat := 4983230072969 + 3 ^ 40 * 8124633 * 2
def baseEnd_8124633 : Nat := 4171841870380616069722999

theorem tailTrace_8124633 : CollatzResearch.WordTrace tailWord_8124633 prefixEnd_8124633 4171841870380616069722999 := by
  unfold tailWord_8124633
  simp only [CollatzResearch.WordTrace]
  refine ⟨296329709974849692690874553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197553139983233128460583035 296329709974849692690874553)
  ·
    refine ⟨222247282481137269518155915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296329709974849692690874553 222247282481137269518155915)
    ·
      refine ⟨333370923721705904277233873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222247282481137269518155915 333370923721705904277233873)
      ·
        refine ⟨250028192791279428207925405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333370923721705904277233873 250028192791279428207925405)
        ·
          refine ⟨93760572296729785577972027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250028192791279428207925405 93760572296729785577972027)
          ·
            refine ⟨140640858445094678366958041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93760572296729785577972027 140640858445094678366958041)
            ·
              refine ⟨105480643833821008775218531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140640858445094678366958041 105480643833821008775218531)
              ·
                refine ⟨158220965750731513162827797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105480643833821008775218531 158220965750731513162827797)
                ·
                  refine ⟨7416607769565539679507553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158220965750731513162827797 7416607769565539679507553)
                  ·
                    refine ⟨5562455827174154759630665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7416607769565539679507553 5562455827174154759630665)
                    ·
                      refine ⟨4171841870380616069722999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5562455827174154759630665 4171841870380616069722999)
                      ·
                        rfl

theorem cell23_8124633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 2, 2].length) (baseStart_8124633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124633 prefixEnd_8124633 := by exact prefixLift 8124633
  have htrace : WordTrace (prefixWord ++ tailWord_8124633) baseStart_8124633 baseEnd_8124633 := by
    simpa [prefixWord, tailWord_8124633, baseEnd_8124633] using wordTrace_append hprefix tailTrace_8124633
  have hstable : (prefixWord ++ tailWord_8124633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124633).length < 2 ^ (prefixWord ++ tailWord_8124633).sum := by decide
  have hdescent : baseEnd_8124633 < baseStart_8124633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124666 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3]
def baseStart_8124666 : Nat := 118140960795 + 8124666 * 2 ^ 59
def prefixEnd_8124666 : Nat := 4983230072969 + 3 ^ 40 * 8124666 * 2
def baseEnd_8124666 : Nat := 4171858815242214440610347

theorem tailTrace_8124666 : CollatzResearch.WordTrace tailWord_8124666 prefixEnd_8124666 4171858815242214440610347 := by
  unfold tailWord_8124666
  simp only [CollatzResearch.WordTrace]
  refine ⟨74082728395932534831706463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197553942389153426217883901 74082728395932534831706463)
  ·
    refine ⟨111124092593898802247559695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74082728395932534831706463 111124092593898802247559695)
    ·
      refine ⟨166686138890848203371339543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111124092593898802247559695 166686138890848203371339543)
      ·
        refine ⟨250029208336272305057009315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166686138890848203371339543 250029208336272305057009315)
        ·
          refine ⟨375043812504408457585513973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250029208336272305057009315 375043812504408457585513973)
          ·
            refine ⟨35160357422288292898641935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 375043812504408457585513973 35160357422288292898641935)
            ·
              refine ⟨52740536133432439347962903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35160357422288292898641935 52740536133432439347962903)
              ·
                refine ⟨79110804200148659021944355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52740536133432439347962903 79110804200148659021944355)
                ·
                  refine ⟨118666206300222988532916533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79110804200148659021944355 118666206300222988532916533)
                  ·
                    refine ⟨11124956840645905174960925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118666206300222988532916533 11124956840645905174960925)
                    ·
                      refine ⟨4171858815242214440610347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11124956840645905174960925 4171858815242214440610347)
                      ·
                        rfl

theorem cell23_8124666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_8124666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124666 prefixEnd_8124666 := by exact prefixLift 8124666
  have htrace : WordTrace (prefixWord ++ tailWord_8124666) baseStart_8124666 baseEnd_8124666 := by
    simpa [prefixWord, tailWord_8124666, baseEnd_8124666] using wordTrace_append hprefix tailTrace_8124666
  have hstable : (prefixWord ++ tailWord_8124666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124666).length < 2 ^ (prefixWord ++ tailWord_8124666).sum := by decide
  have hdescent : baseEnd_8124666 < baseStart_8124666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124686 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 1, 7]
def baseStart_8124686 : Nat := 118140960795 + 8124686 * 2 ^ 59
def prefixEnd_8124686 : Nat := 4983230072969 + 3 ^ 40 * 8124686 * 2
def baseEnd_8124686 : Nat := 1390623028285101454120085

theorem tailTrace_8124686 : CollatzResearch.WordTrace tailWord_8124686 prefixEnd_8124686 1390623028285101454120085 := by
  unfold tailWord_8124686
  simp only [CollatzResearch.WordTrace]
  refine ⟨37041455380457210342819239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197554428695771788495035941 37041455380457210342819239)
  ·
    refine ⟨55562183070685815514228859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37041455380457210342819239 55562183070685815514228859)
    ·
      refine ⟨83343274606028723271343289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55562183070685815514228859 83343274606028723271343289)
      ·
        refine ⟨62507455954521542453507467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83343274606028723271343289 62507455954521542453507467)
        ·
          refine ⟨93761183931782313680261201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62507455954521542453507467 93761183931782313680261201)
          ·
            refine ⟨70320887948836735260195901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93761183931782313680261201 70320887948836735260195901)
            ·
              refine ⟨26370332980813775722573463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70320887948836735260195901 26370332980813775722573463)
              ·
                refine ⟨39555499471220663583860195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26370332980813775722573463 39555499471220663583860195)
                ·
                  refine ⟨59333249206830995375790293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39555499471220663583860195 59333249206830995375790293)
                  ·
                    refine ⟨1390623028285101454120085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59333249206830995375790293 1390623028285101454120085)
                    ·
                      rfl

theorem cell23_8124686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_8124686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124686 prefixEnd_8124686 := by exact prefixLift 8124686
  have htrace : WordTrace (prefixWord ++ tailWord_8124686) baseStart_8124686 baseEnd_8124686 := by
    simpa [prefixWord, tailWord_8124686, baseEnd_8124686] using wordTrace_append hprefix tailTrace_8124686
  have hstable : (prefixWord ++ tailWord_8124686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124686).length < 2 ^ (prefixWord ++ tailWord_8124686).sum := by decide
  have hdescent : baseEnd_8124686 < baseStart_8124686 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124701 : List Nat := [1, 4, 2, 3, 3, 1, 1, 2, 2, 2, 2]
def baseStart_8124701 : Nat := 118140960795 + 8124701 * 2 ^ 59
def prefixEnd_8124701 : Nat := 4983230072969 + 3 ^ 40 * 8124701 * 2
def baseEnd_8124701 : Nat := 4171876787065121803672687

theorem tailTrace_8124701 : CollatzResearch.WordTrace tailWord_8124701 prefixEnd_8124701 4171876787065121803672687 := by
  unfold tailWord_8124701
  simp only [CollatzResearch.WordTrace]
  refine ⟨296332190138603340304349957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197554793425735560202899971 296332190138603340304349957)
  ·
    refine ⟨55562285650988126307065617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296332190138603340304349957 55562285650988126307065617)
    ·
      refine ⟨41671714238241094730299213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55562285650988126307065617 41671714238241094730299213)
      ·
        refine ⟨15626892839340410523862205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41671714238241094730299213 15626892839340410523862205)
        ·
          refine ⟨5860084814752653946448327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15626892839340410523862205 5860084814752653946448327)
          ·
            refine ⟨8790127222128980919672491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5860084814752653946448327 8790127222128980919672491)
            ·
              refine ⟨13185190833193471379508737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8790127222128980919672491 13185190833193471379508737)
              ·
                refine ⟨9888893124895103534631553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13185190833193471379508737 9888893124895103534631553)
                ·
                  refine ⟨7416669843671327650973665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9888893124895103534631553 7416669843671327650973665)
                  ·
                    refine ⟨5562502382753495738230249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7416669843671327650973665 5562502382753495738230249)
                    ·
                      refine ⟨4171876787065121803672687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5562502382753495738230249 4171876787065121803672687)
                      ·
                        rfl

theorem cell23_8124701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_8124701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124701 prefixEnd_8124701 := by exact prefixLift 8124701
  have htrace : WordTrace (prefixWord ++ tailWord_8124701) baseStart_8124701 baseEnd_8124701 := by
    simpa [prefixWord, tailWord_8124701, baseEnd_8124701] using wordTrace_append hprefix tailTrace_8124701
  have hstable : (prefixWord ++ tailWord_8124701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124701).length < 2 ^ (prefixWord ++ tailWord_8124701).sum := by decide
  have hdescent : baseEnd_8124701 < baseStart_8124701 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124723 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 2, 4, 2]
def baseStart_8124723 : Nat := 118140960795 + 8124723 * 2 ^ 59
def prefixEnd_8124723 : Nat := 4983230072969 + 3 ^ 40 * 8124723 * 2
def baseEnd_8124723 : Nat := 4171888083639520717597585

theorem tailTrace_8124723 : CollatzResearch.WordTrace tailWord_8124723 prefixEnd_8124723 4171888083639520717597585 := by
  unfold tailWord_8124723
  simp only [CollatzResearch.WordTrace]
  refine ⟨296332992544523638061650823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197555328363015758707767215 296332992544523638061650823)
  ·
    refine ⟨444499488816785457092476235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296332992544523638061650823 444499488816785457092476235)
    ·
      refine ⟨666749233225178185638714353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444499488816785457092476235 666749233225178185638714353)
      ·
        refine ⟨500061924918883639229035765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666749233225178185638714353 500061924918883639229035765)
        ·
          refine ⟨46880805461145341177722103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 500061924918883639229035765 46880805461145341177722103)
          ·
            refine ⟨70321208191718011766583155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46880805461145341177722103 70321208191718011766583155)
            ·
              refine ⟨105481812287577017649874733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70321208191718011766583155 105481812287577017649874733)
              ·
                refine ⟨39555679607841381618703025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105481812287577017649874733 39555679607841381618703025)
                ·
                  refine ⟨29666759705881036214027269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39555679607841381618703025 29666759705881036214027269)
                  ·
                    refine ⟨5562517444852694290130113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29666759705881036214027269 5562517444852694290130113)
                    ·
                      refine ⟨4171888083639520717597585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5562517444852694290130113 4171888083639520717597585)
                      ·
                        rfl

theorem cell23_8124723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 4, 2].length) (baseStart_8124723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124723 prefixEnd_8124723 := by exact prefixLift 8124723
  have htrace : WordTrace (prefixWord ++ tailWord_8124723) baseStart_8124723 baseEnd_8124723 := by
    simpa [prefixWord, tailWord_8124723, baseEnd_8124723] using wordTrace_append hprefix tailTrace_8124723
  have hstable : (prefixWord ++ tailWord_8124723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124723).length < 2 ^ (prefixWord ++ tailWord_8124723).sum := by decide
  have hdescent : baseEnd_8124723 < baseStart_8124723 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124743 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 3]
def baseStart_8124743 : Nat := 118140960795 + 8124743 * 2 ^ 59
def prefixEnd_8124743 : Nat := 4983230072969 + 3 ^ 40 * 8124743 * 2
def baseEnd_8124743 : Nat := 4171898353252610639347493

theorem tailTrace_8124743 : CollatzResearch.WordTrace tailWord_8124743 prefixEnd_8124743 4171898353252610639347493 := by
  unfold tailWord_8124743
  simp only [CollatzResearch.WordTrace]
  refine ⟨296333722004451181477378883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197555814669634120984919255 296333722004451181477378883)
  ·
    refine ⟨444500583006676772216068325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296333722004451181477378883 444500583006676772216068325)
    ·
      refine ⟨83343859313751894790512811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 444500583006676772216068325 83343859313751894790512811)
      ·
        refine ⟨125015788970627842185769217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83343859313751894790512811 125015788970627842185769217)
        ·
          refine ⟨93761841727970881639326913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125015788970627842185769217 93761841727970881639326913)
          ·
            refine ⟨70321381295978161229495185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93761841727970881639326913 70321381295978161229495185)
            ·
              refine ⟨52741035971983620922121389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70321381295978161229495185 52741035971983620922121389)
              ·
                refine ⟨19777888489493857845795521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52741035971983620922121389 19777888489493857845795521)
                ·
                  refine ⟨14833416367120393384346641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19777888489493857845795521 14833416367120393384346641)
                  ·
                    refine ⟨11125062275340295038259981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14833416367120393384346641 11125062275340295038259981)
                    ·
                      refine ⟨4171898353252610639347493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11125062275340295038259981 4171898353252610639347493)
                      ·
                        rfl

theorem cell23_8124743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_8124743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124743 prefixEnd_8124743 := by exact prefixLift 8124743
  have htrace : WordTrace (prefixWord ++ tailWord_8124743) baseStart_8124743 baseEnd_8124743 := by
    simpa [prefixWord, tailWord_8124743, baseEnd_8124743] using wordTrace_append hprefix tailTrace_8124743
  have hstable : (prefixWord ++ tailWord_8124743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124743).length < 2 ^ (prefixWord ++ tailWord_8124743).sum := by decide
  have hdescent : baseEnd_8124743 < baseStart_8124743 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124750 : List Nat := [4, 1, 1, 1, 1, 1, 2, 7, 1, 4]
def baseStart_8124750 : Nat := 118140960795 + 8124750 * 2 ^ 59
def prefixEnd_8124750 : Nat := 4983230072969 + 3 ^ 40 * 8124750 * 2
def baseEnd_8124750 : Nat := 1390633982539064037319987

theorem tailTrace_8124750 : CollatzResearch.WordTrace tailWord_8124750 prefixEnd_8124750 1390633982539064037319987 := by
  unfold tailWord_8124750
  simp only [CollatzResearch.WordTrace]
  refine ⟨37041747164428227709110463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197555984876950547781922469 37041747164428227709110463)
  ·
    refine ⟨55562620746642341563665695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37041747164428227709110463 55562620746642341563665695)
    ·
      refine ⟨83343931119963512345498543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55562620746642341563665695 83343931119963512345498543)
      ·
        refine ⟨125015896679945268518247815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83343931119963512345498543 125015896679945268518247815)
        ·
          refine ⟨187523845019917902777371723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125015896679945268518247815 187523845019917902777371723)
          ·
            refine ⟨281285767529876854166057585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187523845019917902777371723 281285767529876854166057585)
            ·
              refine ⟨210964325647407640624543189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281285767529876854166057585 210964325647407640624543189)
              ·
                refine ⟨4944476382361116577137731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 210964325647407640624543189 4944476382361116577137731)
                ·
                  refine ⟨7416714573541674865706597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4944476382361116577137731 7416714573541674865706597)
                  ·
                    refine ⟨1390633982539064037319987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7416714573541674865706597 1390633982539064037319987)
                    ·
                      rfl

theorem cell23_8124750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_8124750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124750 prefixEnd_8124750 := by exact prefixLift 8124750
  have htrace : WordTrace (prefixWord ++ tailWord_8124750) baseStart_8124750 baseEnd_8124750 := by
    simpa [prefixWord, tailWord_8124750, baseEnd_8124750] using wordTrace_append hprefix tailTrace_8124750
  have hstable : (prefixWord ++ tailWord_8124750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124750).length < 2 ^ (prefixWord ++ tailWord_8124750).sum := by decide
  have hdescent : baseEnd_8124750 < baseStart_8124750 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124783 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 1, 5, 2]
def baseStart_8124783 : Nat := 118140960795 + 8124783 * 2 ^ 59
def prefixEnd_8124783 : Nat := 4983230072969 + 3 ^ 40 * 8124783 * 2
def baseEnd_8124783 : Nat := 4171918892478790482847309

theorem tailTrace_8124783 : CollatzResearch.WordTrace tailWord_8124783 prefixEnd_8124783 4171918892478790482847309 := by
  unfold tailWord_8124783
  simp only [CollatzResearch.WordTrace]
  refine ⟨296335180924306268308835003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197556787282870845539223335 296335180924306268308835003)
  ·
    refine ⟨444502771386459402463252505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296335180924306268308835003 444502771386459402463252505)
    ·
      refine ⟨333377078539844551847439379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444502771386459402463252505 333377078539844551847439379)
      ·
        refine ⟨500065617809766827771159069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333377078539844551847439379 500065617809766827771159069)
        ·
          refine ⟨187524606678662560414184651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500065617809766827771159069 187524606678662560414184651)
          ·
            refine ⟨281286910017993840621276977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187524606678662560414184651 281286910017993840621276977)
            ·
              refine ⟨210965182513495380465957733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281286910017993840621276977 210965182513495380465957733)
              ·
                refine ⟨39555971721280383837367075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210965182513495380465957733 39555971721280383837367075)
                ·
                  refine ⟨59333957581920575756050613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39555971721280383837367075 59333957581920575756050613)
                  ·
                    refine ⟨5562558523305053977129745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59333957581920575756050613 5562558523305053977129745)
                    ·
                      refine ⟨4171918892478790482847309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5562558523305053977129745 4171918892478790482847309)
                      ·
                        rfl

theorem cell23_8124783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 5, 2].length) (baseStart_8124783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124783 prefixEnd_8124783 := by exact prefixLift 8124783
  have htrace : WordTrace (prefixWord ++ tailWord_8124783) baseStart_8124783 baseEnd_8124783 := by
    simpa [prefixWord, tailWord_8124783, baseEnd_8124783] using wordTrace_append hprefix tailTrace_8124783
  have hstable : (prefixWord ++ tailWord_8124783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124783).length < 2 ^ (prefixWord ++ tailWord_8124783).sum := by decide
  have hdescent : baseEnd_8124783 < baseStart_8124783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124807 : List Nat := [1, 1, 4, 2, 2, 1, 2, 5, 1, 1, 3]
def baseStart_8124807 : Nat := 118140960795 + 8124807 * 2 ^ 59
def prefixEnd_8124807 : Nat := 4983230072969 + 3 ^ 40 * 8124807 * 2
def baseEnd_8124807 : Nat := 4171931216014498388947199

theorem tailTrace_8124807 : CollatzResearch.WordTrace tailWord_8124807 prefixEnd_8124807 4171931216014498388947199 := by
  unfold tailWord_8124807
  simp only [CollatzResearch.WordTrace]
  refine ⟨296336056276219320407708675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197557370850812880271805783 296336056276219320407708675)
  ·
    refine ⟨444504084414328980611563013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296336056276219320407708675 444504084414328980611563013)
    ·
      refine ⟨83344515827686683864668065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 444504084414328980611563013 83344515827686683864668065)
      ·
        refine ⟨62508386870765012898501049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83344515827686683864668065 62508386870765012898501049)
        ·
          refine ⟨46881290153073759673875787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62508386870765012898501049 46881290153073759673875787)
          ·
            refine ⟨70321935229610639510813681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46881290153073759673875787 70321935229610639510813681)
            ·
              refine ⟨52741451422207979633110261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70321935229610639510813681 52741451422207979633110261)
              ·
                refine ⟨4944511070831998090604087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52741451422207979633110261 4944511070831998090604087)
                ·
                  refine ⟨7416766606247997135906131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4944511070831998090604087 7416766606247997135906131)
                  ·
                    refine ⟨11125149909371995703859197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7416766606247997135906131 11125149909371995703859197)
                    ·
                      refine ⟨4171931216014498388947199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11125149909371995703859197 4171931216014498388947199)
                      ·
                        rfl

theorem cell23_8124807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_8124807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124807 prefixEnd_8124807 := by exact prefixLift 8124807
  have htrace : WordTrace (prefixWord ++ tailWord_8124807) baseStart_8124807 baseEnd_8124807 := by
    simpa [prefixWord, tailWord_8124807, baseEnd_8124807] using wordTrace_append hprefix tailTrace_8124807
  have hstable : (prefixWord ++ tailWord_8124807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124807).length < 2 ^ (prefixWord ++ tailWord_8124807).sum := by decide
  have hdescent : baseEnd_8124807 < baseStart_8124807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124816 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 5]
def baseStart_8124816 : Nat := 118140960795 + 8124816 * 2 ^ 59
def prefixEnd_8124816 : Nat := 4983230072969 + 3 ^ 40 * 8124816 * 2
def baseEnd_8124816 : Nat := 4171935837340388853734657

theorem tailTrace_8124816 : CollatzResearch.WordTrace tailWord_8124816 prefixEnd_8124816 4171935837340388853734657 := by
  unfold tailWord_8124816
  simp only [CollatzResearch.WordTrace]
  refine ⟨148168192266593357472393151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197557589688791143296524201 148168192266593357472393151)
  ·
    refine ⟨222252288399890036208589727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148168192266593357472393151 222252288399890036208589727)
    ·
      refine ⟨333378432599835054312884591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222252288399890036208589727 333378432599835054312884591)
      ·
        refine ⟨500067648899752581469326887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333378432599835054312884591 500067648899752581469326887)
        ·
          refine ⟨750101473349628872203990331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500067648899752581469326887 750101473349628872203990331)
          ·
            refine ⟨1125152210024443308305985497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750101473349628872203990331 1125152210024443308305985497)
            ·
              refine ⟨843864157518332481229489123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1125152210024443308305985497 843864157518332481229489123)
              ·
                refine ⟨1265796236277498721844233685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843864157518332481229489123 1265796236277498721844233685)
                ·
                  refine ⟨29667099287753876293224227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1265796236277498721844233685 29667099287753876293224227)
                  ·
                    refine ⟨44500648931630814439836341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29667099287753876293224227 44500648931630814439836341)
                    ·
                      refine ⟨4171935837340388853734657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44500648931630814439836341 4171935837340388853734657)
                      ·
                        rfl

theorem cell23_8124816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_8124816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124816 prefixEnd_8124816 := by exact prefixLift 8124816
  have htrace : WordTrace (prefixWord ++ tailWord_8124816) baseStart_8124816 baseEnd_8124816 := by
    simpa [prefixWord, tailWord_8124816, baseEnd_8124816] using wordTrace_append hprefix tailTrace_8124816
  have hstable : (prefixWord ++ tailWord_8124816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124816).length < 2 ^ (prefixWord ++ tailWord_8124816).sum := by decide
  have hdescent : baseEnd_8124816 < baseStart_8124816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124823 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 4, 4]
def baseStart_8124823 : Nat := 118140960795 + 8124823 * 2 ^ 59
def prefixEnd_8124823 : Nat := 4983230072969 + 3 ^ 40 * 8124823 * 2
def baseEnd_8124823 : Nat := 1390646477234990108782375

theorem tailTrace_8124823 : CollatzResearch.WordTrace tailWord_8124823 prefixEnd_8124823 1390646477234990108782375 := by
  unfold tailWord_8124823
  simp only [CollatzResearch.WordTrace]
  refine ⟨296336639844161355140291123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197557759896107570093527415 296336639844161355140291123)
  ·
    refine ⟨444504959766242032710436685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296336639844161355140291123 444504959766242032710436685)
    ·
      refine ⟨166689359912340762266413757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444504959766242032710436685 166689359912340762266413757)
      ·
        refine ⟨62508509967127785849905159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166689359912340762266413757 62508509967127785849905159)
        ·
          refine ⟨93762764950691678774857739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62508509967127785849905159 93762764950691678774857739)
          ·
            refine ⟨140644147426037518162286609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93762764950691678774857739 140644147426037518162286609)
            ·
              refine ⟨105483110569528138621714957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140644147426037518162286609 105483110569528138621714957)
              ·
                refine ⟨39556166463573051983143109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105483110569528138621714957 39556166463573051983143109)
                ·
                  refine ⟨7416781211919947246839333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39556166463573051983143109 7416781211919947246839333)
                  ·
                    refine ⟨1390646477234990108782375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7416781211919947246839333 1390646477234990108782375)
                    ·
                      rfl

theorem cell23_8124823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_8124823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124823 prefixEnd_8124823 := by exact prefixLift 8124823
  have htrace : WordTrace (prefixWord ++ tailWord_8124823) baseStart_8124823 baseEnd_8124823 := by
    simpa [prefixWord, tailWord_8124823, baseEnd_8124823] using wordTrace_append hprefix tailTrace_8124823
  have hstable : (prefixWord ++ tailWord_8124823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124823).length < 2 ^ (prefixWord ++ tailWord_8124823).sum := by decide
  have hdescent : baseEnd_8124823 < baseStart_8124823 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124824 : List Nat := [2, 1, 2, 5, 1, 2, 1, 4, 1, 1, 3]
def baseStart_8124824 : Nat := 118140960795 + 8124824 * 2 ^ 59
def prefixEnd_8124824 : Nat := 4983230072969 + 3 ^ 40 * 8124824 * 2
def baseEnd_8124824 : Nat := 4171939945185624822434621

theorem tailTrace_8124824 : CollatzResearch.WordTrace tailWord_8124824 prefixEnd_8124824 4171939945185624822434621 := by
  unfold tailWord_8124824
  simp only [CollatzResearch.WordTrace]
  refine ⟨148168338158578866155538763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197557784211438488207385017 148168338158578866155538763)
  ·
    refine ⟨222252507237868299233308145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148168338158578866155538763 222252507237868299233308145)
    ·
      refine ⟨166689380428401224424981109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222252507237868299233308145 166689380428401224424981109)
      ·
        refine ⟨15627129415162614789841979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166689380428401224424981109 15627129415162614789841979)
        ·
          refine ⟨23440694122743922184762969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15627129415162614789841979 23440694122743922184762969)
          ·
            refine ⟨17580520592057941638572227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23440694122743922184762969 17580520592057941638572227)
            ·
              refine ⟨26370780888086912457858341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17580520592057941638572227 26370780888086912457858341)
              ·
                refine ⟨4944521416516296085848439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26370780888086912457858341 4944521416516296085848439)
                ·
                  refine ⟨7416782124774444128772659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4944521416516296085848439 7416782124774444128772659)
                  ·
                    refine ⟨11125173187161666193158989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7416782124774444128772659 11125173187161666193158989)
                    ·
                      refine ⟨4171939945185624822434621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11125173187161666193158989 4171939945185624822434621)
                      ·
                        rfl

theorem cell23_8124824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_8124824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124824 prefixEnd_8124824 := by exact prefixLift 8124824
  have htrace : WordTrace (prefixWord ++ tailWord_8124824) baseStart_8124824 baseEnd_8124824 := by
    simpa [prefixWord, tailWord_8124824, baseEnd_8124824] using wordTrace_append hprefix tailTrace_8124824
  have hstable : (prefixWord ++ tailWord_8124824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124824).length < 2 ^ (prefixWord ++ tailWord_8124824).sum := by decide
  have hdescent : baseEnd_8124824 < baseStart_8124824 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124840 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 1, 6]
def baseStart_8124840 : Nat := 118140960795 + 8124840 * 2 ^ 59
def prefixEnd_8124840 : Nat := 4983230072969 + 3 ^ 40 * 8124840 * 2
def baseEnd_8124840 : Nat := 1390649386958698919944849

theorem tailTrace_8124840 : CollatzResearch.WordTrace tailWord_8124840 prefixEnd_8124840 1390649386958698919944849 := by
  unfold tailWord_8124840
  simp only [CollatzResearch.WordTrace]
  refine ⟨148168629942549883521829987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197558173256733178029106649 148168629942549883521829987)
  ·
    refine ⟨222252944913824825282744981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148168629942549883521829987 222252944913824825282744981)
    ·
      refine ⟨10418106792835538685128671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 222252944913824825282744981 10418106792835538685128671)
      ·
        refine ⟨15627160189253308027693007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10418106792835538685128671 15627160189253308027693007)
        ·
          refine ⟨23440740283879962041539511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15627160189253308027693007 23440740283879962041539511)
          ·
            refine ⟨35161110425819943062309267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23440740283879962041539511 35161110425819943062309267)
            ·
              refine ⟨52741665638729914593463901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35161110425819943062309267 52741665638729914593463901)
              ·
                refine ⟨19778124614523717972548963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52741665638729914593463901 19778124614523717972548963)
                ·
                  refine ⟨29667186921785576958823445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19778124614523717972548963 29667186921785576958823445)
                  ·
                    refine ⟨1390649386958698919944849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29667186921785576958823445 1390649386958698919944849)
                    ·
                      rfl

theorem cell23_8124840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_8124840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124840 prefixEnd_8124840 := by exact prefixLift 8124840
  have htrace : WordTrace (prefixWord ++ tailWord_8124840) baseStart_8124840 baseEnd_8124840 := by
    simpa [prefixWord, tailWord_8124840, baseEnd_8124840] using wordTrace_append hprefix tailTrace_8124840
  have hstable : (prefixWord ++ tailWord_8124840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124840).length < 2 ^ (prefixWord ++ tailWord_8124840).sum := by decide
  have hdescent : baseEnd_8124840 < baseStart_8124840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124850 : List Nat := [3, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3]
def baseStart_8124850 : Nat := 118140960795 + 8124850 * 2 ^ 59
def prefixEnd_8124850 : Nat := 4983230072969 + 3 ^ 40 * 8124850 * 2
def baseEnd_8124850 : Nat := 4171953295682641720709501

theorem tailTrace_8124850 : CollatzResearch.WordTrace tailWord_8124850 prefixEnd_8124850 4171953295682641720709501 := by
  unfold tailWord_8124850
  simp only [CollatzResearch.WordTrace]
  refine ⟨74084406153765884687881001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197558416410042359167682669 74084406153765884687881001)
  ·
    refine ⟨55563304615324413515910751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74084406153765884687881001 55563304615324413515910751)
    ·
      refine ⟨83344956922986620273866127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55563304615324413515910751 83344956922986620273866127)
      ·
        refine ⟨125017435384479930410799191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83344956922986620273866127 125017435384479930410799191)
        ·
          refine ⟨187526153076719895616198787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125017435384479930410799191 187526153076719895616198787)
          ·
            refine ⟨281289229615079843424298181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187526153076719895616198787 281289229615079843424298181)
            ·
              refine ⟨52741730552827470642055909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281289229615079843424298181 52741730552827470642055909)
              ·
                refine ⟨9889074478655150745385483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52741730552827470642055909 9889074478655150745385483)
                ·
                  refine ⟨14833611717982726118078225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9889074478655150745385483 14833611717982726118078225)
                  ·
                    refine ⟨11125208788487044588558669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14833611717982726118078225 11125208788487044588558669)
                    ·
                      refine ⟨4171953295682641720709501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11125208788487044588558669 4171953295682641720709501)
                      ·
                        rfl

theorem cell23_8124850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_8124850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124850 prefixEnd_8124850 := by exact prefixLift 8124850
  have htrace : WordTrace (prefixWord ++ tailWord_8124850) baseStart_8124850 baseEnd_8124850 := by
    simpa [prefixWord, tailWord_8124850, baseEnd_8124850] using wordTrace_append hprefix tailTrace_8124850
  have hstable : (prefixWord ++ tailWord_8124850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124850).length < 2 ^ (prefixWord ++ tailWord_8124850).sum := by decide
  have hdescent : baseEnd_8124850 < baseStart_8124850 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124860 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_8124860 : Nat := 118140960795 + 8124860 * 2 ^ 59
def prefixEnd_8124860 : Nat := 4983230072969 + 3 ^ 40 * 8124860 * 2
def baseEnd_8124860 : Nat := 4171958430489186681584455

theorem tailTrace_8124860 : CollatzResearch.WordTrace tailWord_8124860 prefixEnd_8124860 4171958430489186681584455 := by
  unfold tailWord_8124860
  simp only [CollatzResearch.WordTrace]
  refine ⟨148168994672513655229694017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197558659563351540306258689 148168994672513655229694017)
  ·
    refine ⟨111126746004385241422270513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148168994672513655229694017 111126746004385241422270513)
    ·
      refine ⟨83345059503288931066702885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111126746004385241422270513 83345059503288931066702885)
      ·
        refine ⟨15627198656866674575006791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83345059503288931066702885 15627198656866674575006791)
        ·
          refine ⟨23440797985300011862510187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15627198656866674575006791 23440797985300011862510187)
          ·
            refine ⟨35161196977950017793765281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23440797985300011862510187 35161196977950017793765281)
            ·
              refine ⟨26370897733462513345323961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35161196977950017793765281 26370897733462513345323961)
              ·
                refine ⟨19778173300096885008992971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26370897733462513345323961 19778173300096885008992971)
                ·
                  refine ⟨29667259950145327513489457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19778173300096885008992971 29667259950145327513489457)
                  ·
                    refine ⟨22250444962608995635117093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29667259950145327513489457 22250444962608995635117093)
                    ·
                      refine ⟨4171958430489186681584455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22250444962608995635117093 4171958430489186681584455)
                      ·
                        rfl

theorem cell23_8124860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_8124860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124860 prefixEnd_8124860 := by exact prefixLift 8124860
  have htrace : WordTrace (prefixWord ++ tailWord_8124860) baseStart_8124860 baseEnd_8124860 := by
    simpa [prefixWord, tailWord_8124860, baseEnd_8124860] using wordTrace_append hprefix tailTrace_8124860
  have hstable : (prefixWord ++ tailWord_8124860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124860).length < 2 ^ (prefixWord ++ tailWord_8124860).sum := by decide
  have hdescent : baseEnd_8124860 < baseStart_8124860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124907 : List Nat := [1, 1, 1, 1, 2, 3, 6, 2, 1, 3, 2]
def baseStart_8124907 : Nat := 118140960795 + 8124907 * 2 ^ 59
def prefixEnd_8124907 : Nat := 4983230072969 + 3 ^ 40 * 8124907 * 2
def baseEnd_8124907 : Nat := 4171982564079947997696739

theorem tailTrace_8124907 : CollatzResearch.WordTrace tailWord_8124907 prefixEnd_8124907 4171982564079947997696739 := by
  unfold tailWord_8124907
  simp only [CollatzResearch.WordTrace]
  refine ⟨296339703575857037486348975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197559802383904691657565983 296339703575857037486348975)
  ·
    refine ⟨444509555363785556229523463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296339703575857037486348975 444509555363785556229523463)
    ·
      refine ⟨666764333045678334344285195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444509555363785556229523463 666764333045678334344285195)
      ·
        refine ⟨1000146499568517501516427793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666764333045678334344285195 1000146499568517501516427793)
        ·
          refine ⟨750109874676388126137320845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1000146499568517501516427793 750109874676388126137320845)
          ·
            refine ⟨281291203003645547301495317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 750109874676388126137320845 281291203003645547301495317)
            ·
              refine ⟨13185525140795885029757593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 281291203003645547301495317 13185525140795885029757593)
              ·
                refine ⟨9889143855596913772318195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13185525140795885029757593 9889143855596913772318195)
                ·
                  refine ⟨14833715783395370658477293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9889143855596913772318195 14833715783395370658477293)
                  ·
                    refine ⟨5562643418773263996928985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14833715783395370658477293 5562643418773263996928985)
                    ·
                      refine ⟨4171982564079947997696739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5562643418773263996928985 4171982564079947997696739)
                      ·
                        rfl

theorem cell23_8124907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 3, 2].length) (baseStart_8124907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124907 prefixEnd_8124907 := by exact prefixLift 8124907
  have htrace : WordTrace (prefixWord ++ tailWord_8124907) baseStart_8124907 baseEnd_8124907 := by
    simpa [prefixWord, tailWord_8124907, baseEnd_8124907] using wordTrace_append hprefix tailTrace_8124907
  have hstable : (prefixWord ++ tailWord_8124907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124907).length < 2 ^ (prefixWord ++ tailWord_8124907).sum := by decide
  have hdescent : baseEnd_8124907 < baseStart_8124907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124920 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 3, 4, 2]
def baseStart_8124920 : Nat := 118140960795 + 8124920 * 2 ^ 59
def prefixEnd_8124920 : Nat := 4983230072969 + 3 ^ 40 * 8124920 * 2
def baseEnd_8124920 : Nat := 4171989239328456446834179

theorem tailTrace_8124920 : CollatzResearch.WordTrace tailWord_8124920 prefixEnd_8124920 4171989239328456446834179 := by
  unfold tailWord_8124920
  simp only [CollatzResearch.WordTrace]
  refine ⟨148170088862404970353286107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197560118483206627137714809 148170088862404970353286107)
  ·
    refine ⟨222255133293607455529929161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148170088862404970353286107 222255133293607455529929161)
    ·
      refine ⟨166691349970205591647446871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222255133293607455529929161 166691349970205591647446871)
      ·
        refine ⟨250037024955308387471170307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166691349970205591647446871 250037024955308387471170307)
        ·
          refine ⟨375055537432962581206755461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250037024955308387471170307 375055537432962581206755461)
          ·
            refine ⟨70322913268680483976266649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 375055537432962581206755461 70322913268680483976266649)
            ·
              refine ⟨52742184951510362982199987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70322913268680483976266649 52742184951510362982199987)
              ·
                refine ⟨79113277427265544473299981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52742184951510362982199987 79113277427265544473299981)
                ·
                  refine ⟨29667479035224579177487493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79113277427265544473299981 29667479035224579177487493)
                  ·
                    refine ⟨5562652319104608595778905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29667479035224579177487493 5562652319104608595778905)
                    ·
                      refine ⟨4171989239328456446834179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5562652319104608595778905 4171989239328456446834179)
                      ·
                        rfl

theorem cell23_8124920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 3, 4, 2].length) (baseStart_8124920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124920 prefixEnd_8124920 := by exact prefixLift 8124920
  have htrace : WordTrace (prefixWord ++ tailWord_8124920) baseStart_8124920 baseEnd_8124920 := by
    simpa [prefixWord, tailWord_8124920, baseEnd_8124920] using wordTrace_append hprefix tailTrace_8124920
  have hstable : (prefixWord ++ tailWord_8124920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124920).length < 2 ^ (prefixWord ++ tailWord_8124920).sum := by decide
  have hdescent : baseEnd_8124920 < baseStart_8124920 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124933 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 4, 2, 4]
def baseStart_8124933 : Nat := 118140960795 + 8124933 * 2 ^ 59
def prefixEnd_8124933 : Nat := 4983230072969 + 3 ^ 40 * 8124933 * 2
def baseEnd_8124933 : Nat := 4171995914576964895971619

theorem tailTrace_8124933 : CollatzResearch.WordTrace tailWord_8124933 prefixEnd_8124933 4171995914576964895971619 := by
  unfold tailWord_8124933
  simp only [CollatzResearch.WordTrace]
  refine ⟨296340651873762843926795453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197560434582508562617863635 296340651873762843926795453)
  ·
    refine ⟨111127744452661066472548295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296340651873762843926795453 111127744452661066472548295)
    ·
      refine ⟨166691616678991599708822443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111127744452661066472548295 166691616678991599708822443)
      ·
        refine ⟨250037425018487399563233665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166691616678991599708822443 250037425018487399563233665)
        ·
          refine ⟨187528068763865549672425249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250037425018487399563233665 187528068763865549672425249)
          ·
            refine ⟨140646051572899162254318937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187528068763865549672425249 140646051572899162254318937)
            ·
              refine ⟨105484538679674371690739203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140646051572899162254318937 105484538679674371690739203)
              ·
                refine ⟨158226808019511557536108805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105484538679674371690739203 158226808019511557536108805)
                ·
                  refine ⟨29667526503658417038020401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158226808019511557536108805 29667526503658417038020401)
                  ·
                    refine ⟨22250644877743812778515301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29667526503658417038020401 22250644877743812778515301)
                    ·
                      refine ⟨4171995914576964895971619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22250644877743812778515301 4171995914576964895971619)
                      ·
                        rfl

theorem cell23_8124933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_8124933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124933 prefixEnd_8124933 := by exact prefixLift 8124933
  have htrace : WordTrace (prefixWord ++ tailWord_8124933) baseStart_8124933 baseEnd_8124933 := by
    simpa [prefixWord, tailWord_8124933, baseEnd_8124933] using wordTrace_append hprefix tailTrace_8124933
  have hstable : (prefixWord ++ tailWord_8124933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124933).length < 2 ^ (prefixWord ++ tailWord_8124933).sum := by decide
  have hdescent : baseEnd_8124933 < baseStart_8124933 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124948 : List Nat := [2, 4, 3, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_8124948 : Nat := 118140960795 + 8124948 * 2 ^ 59
def prefixEnd_8124948 : Nat := 4983230072969 + 3 ^ 40 * 8124948 * 2
def baseEnd_8124948 : Nat := 4172003616786782337284051

theorem tailTrace_8124948 : CollatzResearch.WordTrace tailWord_8124948 prefixEnd_8124948 4172003616786782337284051 := by
  unfold tailWord_8124948
  simp only [CollatzResearch.WordTrace]
  refine ⟨148170599484354250744295749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197560799312472334325727665 148170599484354250744295749)
  ·
    refine ⟨27781987403316422014555453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148170599484354250744295749 27781987403316422014555453)
    ·
      refine ⟨10418245276243658255458295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27781987403316422014555453 10418245276243658255458295)
      ·
        refine ⟨15627367914365487383187443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10418245276243658255458295 15627367914365487383187443)
        ·
          refine ⟨23441051871548231074781165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15627367914365487383187443 23441051871548231074781165)
          ·
            refine ⟨8790394451830586653042937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23441051871548231074781165 8790394451830586653042937)
            ·
              refine ⟨6592795838872939989782203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8790394451830586653042937 6592795838872939989782203)
              ·
                refine ⟨9889193758309409984673305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6592795838872939989782203 9889193758309409984673305)
                ·
                  refine ⟨7416895318732057488504979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9889193758309409984673305 7416895318732057488504979)
                  ·
                    refine ⟨11125342978098086232757469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7416895318732057488504979 11125342978098086232757469)
                    ·
                      refine ⟨4172003616786782337284051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11125342978098086232757469 4172003616786782337284051)
                      ·
                        rfl

theorem cell23_8124948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_8124948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124948 prefixEnd_8124948 := by exact prefixLift 8124948
  have htrace : WordTrace (prefixWord ++ tailWord_8124948) baseStart_8124948 baseEnd_8124948 := by
    simpa [prefixWord, tailWord_8124948, baseEnd_8124948] using wordTrace_append hprefix tailTrace_8124948
  have hstable : (prefixWord ++ tailWord_8124948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124948).length < 2 ^ (prefixWord ++ tailWord_8124948).sum := by decide
  have hdescent : baseEnd_8124948 < baseStart_8124948 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8124983 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 5]
def baseStart_8124983 : Nat := 118140960795 + 8124983 * 2 ^ 59
def prefixEnd_8124983 : Nat := 4983230072969 + 3 ^ 40 * 8124983 * 2
def baseEnd_8124983 : Nat := 4172021588609689700346389

theorem tailTrace_8124983 : CollatzResearch.WordTrace tailWord_8124983 prefixEnd_8124983 4172021588609689700346389 := by
  unfold tailWord_8124983
  simp only [CollatzResearch.WordTrace]
  refine ⟨296342475523581702466115603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197561650349054468310743735 296342475523581702466115603)
  ·
    refine ⟨444513713285372553699173405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296342475523581702466115603 444513713285372553699173405)
    ·
      refine ⟨166692642482014707637190027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444513713285372553699173405 166692642482014707637190027)
      ·
        refine ⟨250038963723022061455785041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166692642482014707637190027 250038963723022061455785041)
        ·
          refine ⟨187529222792266546091838781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250038963723022061455785041 187529222792266546091838781)
          ·
            refine ⟨70323458547099954784439543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187529222792266546091838781 70323458547099954784439543)
            ·
              refine ⟨105485187820649932176659315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70323458547099954784439543 105485187820649932176659315)
              ·
                refine ⟨158227781730974898264988973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105485187820649932176659315 158227781730974898264988973)
                ·
                  refine ⟨59335418149115586849370865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158227781730974898264988973 59335418149115586849370865)
                  ·
                    refine ⟨44501563611836690137028149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59335418149115586849370865 44501563611836690137028149)
                    ·
                      refine ⟨4172021588609689700346389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44501563611836690137028149 4172021588609689700346389)
                      ·
                        rfl

theorem cell23_8124983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_8124983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8124983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8124983 prefixEnd_8124983 := by exact prefixLift 8124983
  have htrace : WordTrace (prefixWord ++ tailWord_8124983) baseStart_8124983 baseEnd_8124983 := by
    simpa [prefixWord, tailWord_8124983, baseEnd_8124983] using wordTrace_append hprefix tailTrace_8124983
  have hstable : (prefixWord ++ tailWord_8124983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8124983).length < 2 ^ (prefixWord ++ tailWord_8124983).sum := by decide
  have hdescent : baseEnd_8124983 < baseStart_8124983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8124983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125010 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_8125010 : Nat := 118140960795 + 8125010 * 2 ^ 59
def prefixEnd_8125010 : Nat := 4983230072969 + 3 ^ 40 * 8125010 * 2
def baseEnd_8125010 : Nat := 4172035452587361094708765

theorem tailTrace_8125010 : CollatzResearch.WordTrace tailWord_8125010 prefixEnd_8125010 4172035452587361094708765 := by
  unfold tailWord_8125010
  simp only [CollatzResearch.WordTrace]
  refine ⟨74085865073620971519337121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197562306862989257384898989 74085865073620971519337121)
  ·
    refine ⟨55564398805215728639502841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74085865073620971519337121 55564398805215728639502841)
    ·
      refine ⟨41673299103911796479627131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55564398805215728639502841 41673299103911796479627131)
      ·
        refine ⟨62509948655867694719440697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41673299103911796479627131 62509948655867694719440697)
        ·
          refine ⟨46882461491900771039580523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62509948655867694719440697 46882461491900771039580523)
          ·
            refine ⟨70323692237851156559370785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46882461491900771039580523 70323692237851156559370785)
            ·
              refine ⟨52742769178388367419528089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70323692237851156559370785 52742769178388367419528089)
              ·
                refine ⟨39557076883791275564646067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52742769178388367419528089 39557076883791275564646067)
                ·
                  refine ⟨59335615325686913346969101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39557076883791275564646067 59335615325686913346969101)
                  ·
                    refine ⟨22250855747132592505113413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59335615325686913346969101 22250855747132592505113413)
                    ·
                      refine ⟨4172035452587361094708765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22250855747132592505113413 4172035452587361094708765)
                      ·
                        rfl

theorem cell23_8125010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_8125010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125010 prefixEnd_8125010 := by exact prefixLift 8125010
  have htrace : WordTrace (prefixWord ++ tailWord_8125010) baseStart_8125010 baseEnd_8125010 := by
    simpa [prefixWord, tailWord_8125010, baseEnd_8125010] using wordTrace_append hprefix tailTrace_8125010
  have hstable : (prefixWord ++ tailWord_8125010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125010).length < 2 ^ (prefixWord ++ tailWord_8125010).sum := by decide
  have hdescent : baseEnd_8125010 < baseStart_8125010 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125023 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 6]
def baseStart_8125023 : Nat := 118140960795 + 8125023 * 2 ^ 59
def prefixEnd_8125023 : Nat := 4983230072969 + 3 ^ 40 * 8125023 * 2
def baseEnd_8125023 : Nat := 4172042127835869543846205

theorem tailTrace_8125023 : CollatzResearch.WordTrace tailWord_8125023 prefixEnd_8125023 4172042127835869543846205 := by
  unfold tailWord_8125023
  simp only [CollatzResearch.WordTrace]
  refine ⟨296343934443436789297571723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197562622962291192865047815 296343934443436789297571723)
  ·
    refine ⟨444515901665155183946357585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296343934443436789297571723 444515901665155183946357585)
    ·
      refine ⟨333386926248866387959768189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444515901665155183946357585 333386926248866387959768189)
      ·
        refine ⟨125020097343324895484913071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333386926248866387959768189 125020097343324895484913071)
        ·
          refine ⟨187530146014987343227369607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125020097343324895484913071 187530146014987343227369607)
          ·
            refine ⟨281295219022481014841054411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187530146014987343227369607 281295219022481014841054411)
            ·
              refine ⟨421942828533721522261581617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281295219022481014841054411 421942828533721522261581617)
              ·
                refine ⟨316457121400291141696186213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421942828533721522261581617 316457121400291141696186213)
                ·
                  refine ⟨59335710262554589068034915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316457121400291141696186213 59335710262554589068034915)
                  ·
                    refine ⟨89003565393831883602052373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59335710262554589068034915 89003565393831883602052373)
                    ·
                      refine ⟨4172042127835869543846205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89003565393831883602052373 4172042127835869543846205)
                      ·
                        rfl

theorem cell23_8125023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_8125023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125023 prefixEnd_8125023 := by exact prefixLift 8125023
  have htrace : WordTrace (prefixWord ++ tailWord_8125023) baseStart_8125023 baseEnd_8125023 := by
    simpa [prefixWord, tailWord_8125023, baseEnd_8125023] using wordTrace_append hprefix tailTrace_8125023
  have hstable : (prefixWord ++ tailWord_8125023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125023).length < 2 ^ (prefixWord ++ tailWord_8125023).sum := by decide
  have hdescent : baseEnd_8125023 < baseStart_8125023 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125033 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 8]
def baseStart_8125033 : Nat := 118140960795 + 8125033 * 2 ^ 59
def prefixEnd_8125033 : Nat := 4983230072969 + 3 ^ 40 * 8125033 * 2
def baseEnd_8125033 : Nat := 463560806960268278302351

theorem tailTrace_8125033 : CollatzResearch.WordTrace tailWord_8125033 prefixEnd_8125033 463560806960268278302351 := by
  unfold tailWord_8125033
  simp only [CollatzResearch.WordTrace]
  refine ⟨296344299173400561005435753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197562866115600374003623835 296344299173400561005435753)
  ·
    refine ⟨222258224380050420754076815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296344299173400561005435753 222258224380050420754076815)
    ·
      refine ⟨333387336570075631131115223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222258224380050420754076815 333387336570075631131115223)
      ·
        refine ⟨500081004855113446696672835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333387336570075631131115223 500081004855113446696672835)
        ·
          refine ⟨750121507282670170045009253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500081004855113446696672835 750121507282670170045009253)
          ·
            refine ⟨140647782615500656883439235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 750121507282670170045009253 140647782615500656883439235)
            ·
              refine ⟨210971673923250985325158853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140647782615500656883439235 210971673923250985325158853)
              ·
                refine ⟨39557188860609559748467285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210971673923250985325158853 39557188860609559748467285)
                ·
                  refine ⟨463560806960268278302351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39557188860609559748467285 463560806960268278302351)
                  ·
                    rfl

theorem cell23_8125033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 8].length) (baseStart_8125033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125033 prefixEnd_8125033 := by exact prefixLift 8125033
  have htrace : WordTrace (prefixWord ++ tailWord_8125033) baseStart_8125033 baseEnd_8125033 := by
    simpa [prefixWord, tailWord_8125033, baseEnd_8125033] using wordTrace_append hprefix tailTrace_8125033
  have hstable : (prefixWord ++ tailWord_8125033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125033).length < 2 ^ (prefixWord ++ tailWord_8125033).sum := by decide
  have hdescent : baseEnd_8125033 < baseStart_8125033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125070 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_8125070 : Nat := 118140960795 + 8125070 * 2 ^ 59
def prefixEnd_8125070 : Nat := 4983230072969 + 3 ^ 40 * 8125070 * 2
def baseEnd_8125070 : Nat := 4172066261426630859958489

theorem tailTrace_8125070 : CollatzResearch.WordTrace tailWord_8125070 prefixEnd_8125070 4172066261426630859958489 := by
  unfold tailWord_8125070
  simp only [CollatzResearch.WordTrace]
  refine ⟨37043206084283314540566583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197563765782844344216355109 37043206084283314540566583)
  ·
    refine ⟨55564809126424971810849875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37043206084283314540566583 55564809126424971810849875)
    ·
      refine ⟨83347213689637457716274813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55564809126424971810849875 83347213689637457716274813)
      ·
        refine ⟨31255205133614046643603055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83347213689637457716274813 31255205133614046643603055)
        ·
          refine ⟨46882807700421069965404583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31255205133614046643603055 46882807700421069965404583)
          ·
            refine ⟨70324211550631604948106875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46882807700421069965404583 70324211550631604948106875)
            ·
              refine ⟨105486317325947407422160313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70324211550631604948106875 105486317325947407422160313)
              ·
                refine ⟨79114737994460555566620235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105486317325947407422160313 79114737994460555566620235)
                ·
                  refine ⟨118672106991690833349930353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79114737994460555566620235 118672106991690833349930353)
                  ·
                    refine ⟨89004080243768125012447765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118672106991690833349930353 89004080243768125012447765)
                    ·
                      refine ⟨4172066261426630859958489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89004080243768125012447765 4172066261426630859958489)
                      ·
                        rfl

theorem cell23_8125070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_8125070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125070 prefixEnd_8125070 := by exact prefixLift 8125070
  have htrace : WordTrace (prefixWord ++ tailWord_8125070) baseStart_8125070 baseEnd_8125070 := by
    simpa [prefixWord, tailWord_8125070, baseEnd_8125070] using wordTrace_append hprefix tailTrace_8125070
  have hstable : (prefixWord ++ tailWord_8125070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125070).length < 2 ^ (prefixWord ++ tailWord_8125070).sum := by decide
  have hdescent : baseEnd_8125070 < baseStart_8125070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125083 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 10]
def baseStart_8125083 : Nat := 118140960795 + 8125083 * 2 ^ 59
def prefixEnd_8125083 : Nat := 4983230072969 + 3 ^ 40 * 8125083 * 2
def baseEnd_8125083 : Nat := 4172072936675139309095929

theorem tailTrace_8125083 : CollatzResearch.WordTrace tailWord_8125083 prefixEnd_8125083 4172072936675139309095929 := by
  unfold tailWord_8125083
  simp only [CollatzResearch.WordTrace]
  refine ⟨296346122823219419544755903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197564081882146279696503935 296346122823219419544755903)
  ·
    refine ⟨444519184234829129317133855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296346122823219419544755903 444519184234829129317133855)
    ·
      refine ⟨666778776352243693975700783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444519184234829129317133855 666778776352243693975700783)
      ·
        refine ⟨1000168164528365540963551175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666778776352243693975700783 1000168164528365540963551175)
        ·
          refine ⟨1500252246792548311445326763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000168164528365540963551175 1500252246792548311445326763)
          ·
            refine ⟨2250378370188822467167990145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500252246792548311445326763 2250378370188822467167990145)
            ·
              refine ⟨1687783777641616850375992609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2250378370188822467167990145 1687783777641616850375992609)
              ·
                refine ⟨1265837833231212637781994457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1687783777641616850375992609 1265837833231212637781994457)
                ·
                  refine ⟨949378374923409478336495843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1265837833231212637781994457 949378374923409478336495843)
                  ·
                    refine ⟨1424067562385114217504743765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 949378374923409478336495843 1424067562385114217504743765)
                    ·
                      refine ⟨4172072936675139309095929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1424067562385114217504743765 4172072936675139309095929)
                      ·
                        rfl

theorem cell23_8125083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 10].length) (baseStart_8125083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125083 prefixEnd_8125083 := by exact prefixLift 8125083
  have htrace : WordTrace (prefixWord ++ tailWord_8125083) baseStart_8125083 baseEnd_8125083 := by
    simpa [prefixWord, tailWord_8125083, baseEnd_8125083] using wordTrace_append hprefix tailTrace_8125083
  have hstable : (prefixWord ++ tailWord_8125083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125083).length < 2 ^ (prefixWord ++ tailWord_8125083).sum := by decide
  have hdescent : baseEnd_8125083 < baseStart_8125083 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125088 : List Nat := [2, 1, 1, 4, 5, 1, 1, 3, 1, 4]
def baseStart_8125088 : Nat := 118140960795 + 8125088 * 2 ^ 59
def prefixEnd_8125088 : Nat := 4983230072969 + 3 ^ 40 * 8125088 * 2
def baseEnd_8125088 : Nat := 1390691834692803929844469

theorem tailTrace_8125088 : CollatzResearch.WordTrace tailWord_8125088 prefixEnd_8125088 1390691834692803929844469 := by
  unfold tailWord_8125088
  simp only [CollatzResearch.WordTrace]
  refine ⟨148173152594100652699343959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197564203458800870265791945 148173152594100652699343959)
  ·
    refine ⟨222259728891150979049015939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148173152594100652699343959 222259728891150979049015939)
    ·
      refine ⟨333389593336726468573523909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222259728891150979049015939 333389593336726468573523909)
      ·
        refine ⟨62510548750636212857535733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333389593336726468573523909 62510548750636212857535733)
        ·
          refine ⟨5860363945372144955393975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62510548750636212857535733 5860363945372144955393975)
          ·
            refine ⟨8790545918058217433090963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5860363945372144955393975 8790545918058217433090963)
            ·
              refine ⟨13185818877087326149636445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8790545918058217433090963 13185818877087326149636445)
              ·
                refine ⟨4944682078907747306113667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13185818877087326149636445 4944682078907747306113667)
                ·
                  refine ⟨7417023118361620959170501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4944682078907747306113667 7417023118361620959170501)
                  ·
                    refine ⟨1390691834692803929844469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7417023118361620959170501 1390691834692803929844469)
                    ·
                      rfl

theorem cell23_8125088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 1, 4].length) (baseStart_8125088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125088 prefixEnd_8125088 := by exact prefixLift 8125088
  have htrace : WordTrace (prefixWord ++ tailWord_8125088) baseStart_8125088 baseEnd_8125088 := by
    simpa [prefixWord, tailWord_8125088, baseEnd_8125088] using wordTrace_append hprefix tailTrace_8125088
  have hstable : (prefixWord ++ tailWord_8125088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125088).length < 2 ^ (prefixWord ++ tailWord_8125088).sum := by decide
  have hdescent : baseEnd_8125088 < baseStart_8125088 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125111 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 3, 1, 3]
def baseStart_8125111 : Nat := 118140960795 + 8125111 * 2 ^ 59
def prefixEnd_8125111 : Nat := 4983230072969 + 3 ^ 40 * 8125111 * 2
def baseEnd_8125111 : Nat := 4172087314133465199545801

theorem tailTrace_8125111 : CollatzResearch.WordTrace tailWord_8125111 prefixEnd_8125111 4172087314133465199545801 := by
  unfold tailWord_8125111
  simp only [CollatzResearch.WordTrace]
  refine ⟨296347144067117980326775187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197564762711411986884516791 296347144067117980326775187)
  ·
    refine ⟨444520716100676970490162781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296347144067117980326775187 444520716100676970490162781)
    ·
      refine ⟨166695268537753863933811043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444520716100676970490162781 166695268537753863933811043)
      ·
        refine ⟨250042902806630795900716565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166695268537753863933811043 250042902806630795900716565)
        ·
          refine ⟨11720761069060818557846089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 250042902806630795900716565 11720761069060818557846089)
          ·
            refine ⟨8790570801795613918384567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11720761069060818557846089 8790570801795613918384567)
            ·
              refine ⟨13185856202693420877576851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8790570801795613918384567 13185856202693420877576851)
              ·
                refine ⟨19778784304040131316365277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13185856202693420877576851 19778784304040131316365277)
                ·
                  refine ⟨7417044114015049243636979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19778784304040131316365277 7417044114015049243636979)
                  ·
                    refine ⟨11125566171022573865455469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7417044114015049243636979 11125566171022573865455469)
                    ·
                      refine ⟨4172087314133465199545801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11125566171022573865455469 4172087314133465199545801)
                      ·
                        rfl

theorem cell23_8125111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_8125111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125111 prefixEnd_8125111 := by exact prefixLift 8125111
  have htrace : WordTrace (prefixWord ++ tailWord_8125111) baseStart_8125111 baseEnd_8125111 := by
    simpa [prefixWord, tailWord_8125111, baseEnd_8125111] using wordTrace_append hprefix tailTrace_8125111
  have hstable : (prefixWord ++ tailWord_8125111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125111).length < 2 ^ (prefixWord ++ tailWord_8125111).sum := by decide
  have hdescent : baseEnd_8125111 < baseStart_8125111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125134 : List Nat := [4, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4]
def baseStart_8125134 : Nat := 118140960795 + 8125134 * 2 ^ 59
def prefixEnd_8125134 : Nat := 4983230072969 + 3 ^ 40 * 8125134 * 2
def baseEnd_8125134 : Nat := 4172099124188518609558195

theorem tailTrace_8125134 : CollatzResearch.WordTrace tailWord_8125134 prefixEnd_8125134 4172099124188518609558195 := by
  unfold tailWord_8125134
  simp only [CollatzResearch.WordTrace]
  refine ⟨37043497868254331906857807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197565321964023103503241637 37043497868254331906857807)
  ·
    refine ⟨55565246802381497860286711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37043497868254331906857807 55565246802381497860286711)
    ·
      refine ⟨83347870203572246790430067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55565246802381497860286711 83347870203572246790430067)
      ·
        refine ⟨125021805305358370185645101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83347870203572246790430067 125021805305358370185645101)
        ·
          refine ⟨46883176989509388819616913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125021805305358370185645101 46883176989509388819616913)
          ·
            refine ⟨35162382742132041614712685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46883176989509388819616913 35162382742132041614712685)
            ·
              refine ⟨13185893528299515605517257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35162382742132041614712685 13185893528299515605517257)
              ·
                refine ⟨9889420146224636704137943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13185893528299515605517257 9889420146224636704137943)
                ·
                  refine ⟨14834130219336955056206915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9889420146224636704137943 14834130219336955056206915)
                  ·
                    refine ⟨22251195329005432584310373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14834130219336955056206915 22251195329005432584310373)
                    ·
                      refine ⟨4172099124188518609558195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22251195329005432584310373 4172099124188518609558195)
                      ·
                        rfl

theorem cell23_8125134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_8125134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125134 prefixEnd_8125134 := by exact prefixLift 8125134
  have htrace : WordTrace (prefixWord ++ tailWord_8125134) baseStart_8125134 baseEnd_8125134 := by
    simpa [prefixWord, tailWord_8125134, baseEnd_8125134] using wordTrace_append hprefix tailTrace_8125134
  have hstable : (prefixWord ++ tailWord_8125134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125134).length < 2 ^ (prefixWord ++ tailWord_8125134).sum := by decide
  have hdescent : baseEnd_8125134 < baseStart_8125134 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125137 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 3, 2, 3]
def baseStart_8125137 : Nat := 118140960795 + 8125137 * 2 ^ 59
def prefixEnd_8125137 : Nat := 4983230072969 + 3 ^ 40 * 8125137 * 2
def baseEnd_8125137 : Nat := 4172100664630482097820681

theorem tailTrace_8125137 : CollatzResearch.WordTrace tailWord_8125137 prefixEnd_8125137 4172100664630482097820681 := by
  unfold tailWord_8125137
  simp only [CollatzResearch.WordTrace]
  refine ⟨296348092365023786767221665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197565394910015857844814443 296348092365023786767221665)
  ·
    refine ⟨222261069273767840075416249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296348092365023786767221665 222261069273767840075416249)
    ·
      refine ⟨166695801955325880056562187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222261069273767840075416249 166695801955325880056562187)
      ·
        refine ⟨250043702932988820084843281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166695801955325880056562187 250043702932988820084843281)
        ·
          refine ⟨187532777199741615063632461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250043702932988820084843281 187532777199741615063632461)
          ·
            refine ⟨70324791449903105648862173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187532777199741615063632461 70324791449903105648862173)
            ·
              refine ⟨26371796793713664618323315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70324791449903105648862173 26371796793713664618323315)
              ·
                refine ⟨39557695190570496927484973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26371796793713664618323315 39557695190570496927484973)
                ·
                  refine ⟨14834135696463936347806865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39557695190570496927484973 14834135696463936347806865)
                  ·
                    refine ⟨11125601772347952260855149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14834135696463936347806865 11125601772347952260855149)
                    ·
                      refine ⟨4172100664630482097820681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11125601772347952260855149 4172100664630482097820681)
                      ·
                        rfl

theorem cell23_8125137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_8125137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125137 prefixEnd_8125137 := by exact prefixLift 8125137
  have htrace : WordTrace (prefixWord ++ tailWord_8125137) baseStart_8125137 baseEnd_8125137 := by
    simpa [prefixWord, tailWord_8125137, baseEnd_8125137] using wordTrace_append hprefix tailTrace_8125137
  have hstable : (prefixWord ++ tailWord_8125137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125137).length < 2 ^ (prefixWord ++ tailWord_8125137).sum := by decide
  have hdescent : baseEnd_8125137 < baseStart_8125137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125194 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 3, 3, 2]
def baseStart_8125194 : Nat := 118140960795 + 8125194 * 2 ^ 59
def prefixEnd_8125194 : Nat := 4983230072969 + 3 ^ 40 * 8125194 * 2
def baseEnd_8125194 : Nat := 4172129933027788374807919

theorem tailTrace_8125194 : CollatzResearch.WordTrace tailWord_8125194 prefixEnd_8125194 4172129933027788374807919 := by
  unfold tailWord_8125194
  simp only [CollatzResearch.WordTrace]
  refine ⟨74087542831454321375511659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197566780883878190334697757 74087542831454321375511659)
  ·
    refine ⟨111131314247181482063267489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74087542831454321375511659 111131314247181482063267489)
    ·
      refine ⟨83348485685386111547450617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111131314247181482063267489 83348485685386111547450617)
      ·
        refine ⟨62511364264039583660587963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83348485685386111547450617 62511364264039583660587963)
        ·
          refine ⟨93767046396059375490881945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62511364264039583660587963 93767046396059375490881945)
          ·
            refine ⟨70325284797044531618161459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93767046396059375490881945 70325284797044531618161459)
            ·
              refine ⟨105487927195566797427242189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70325284797044531618161459 105487927195566797427242189)
              ·
                refine ⟨39557972698337549035215821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105487927195566797427242189 39557972698337549035215821)
                ·
                  refine ⟨14834239761876580888205933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39557972698337549035215821 14834239761876580888205933)
                  ·
                    refine ⟨5562839910703717833077225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14834239761876580888205933 5562839910703717833077225)
                    ·
                      refine ⟨4172129933027788374807919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5562839910703717833077225 4172129933027788374807919)
                      ·
                        rfl

theorem cell23_8125194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_8125194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125194 prefixEnd_8125194 := by exact prefixLift 8125194
  have htrace : WordTrace (prefixWord ++ tailWord_8125194) baseStart_8125194 baseEnd_8125194 := by
    simpa [prefixWord, tailWord_8125194, baseEnd_8125194] using wordTrace_append hprefix tailTrace_8125194
  have hstable : (prefixWord ++ tailWord_8125194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125194).length < 2 ^ (prefixWord ++ tailWord_8125194).sum := by decide
  have hdescent : baseEnd_8125194 < baseStart_8125194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125202 : List Nat := [3, 2, 4, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_8125202 : Nat := 118140960795 + 8125202 * 2 ^ 59
def prefixEnd_8125202 : Nat := 4983230072969 + 3 ^ 40 * 8125202 * 2
def baseEnd_8125202 : Nat := 4172134040873024343507883

theorem tailTrace_8125202 : CollatzResearch.WordTrace tailWord_8125202 prefixEnd_8125202 4172134040873024343507883 := by
  unfold tailWord_8125202
  simp only [CollatzResearch.WordTrace]
  refine ⟨74087615777447075717084465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197566975406525535245558573 74087615777447075717084465)
  ·
    refine ⟨55565711833085306787813349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74087615777447075717084465 55565711833085306787813349)
    ·
      refine ⟨10418570968703495022715003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55565711833085306787813349 10418570968703495022715003)
      ·
        refine ⟨15627856453055242534072505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10418570968703495022715003 15627856453055242534072505)
        ·
          refine ⟨11720892339791431900554379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15627856453055242534072505 11720892339791431900554379)
          ·
            refine ⟨17581338509687147850831569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11720892339791431900554379 17581338509687147850831569)
            ·
              refine ⟨13186003882265360888123677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17581338509687147850831569 13186003882265360888123677)
              ·
                refine ⟨4944751455849510333046379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13186003882265360888123677 4944751455849510333046379)
                ·
                  refine ⟨7417127183774265499569569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4944751455849510333046379 7417127183774265499569569)
                  ·
                    refine ⟨5562845387830699124677177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7417127183774265499569569 5562845387830699124677177)
                    ·
                      refine ⟨4172134040873024343507883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5562845387830699124677177 4172134040873024343507883)
                      ·
                        rfl

theorem cell23_8125202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_8125202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125202 prefixEnd_8125202 := by exact prefixLift 8125202
  have htrace : WordTrace (prefixWord ++ tailWord_8125202) baseStart_8125202 baseEnd_8125202 := by
    simpa [prefixWord, tailWord_8125202, baseEnd_8125202] using wordTrace_append hprefix tailTrace_8125202
  have hstable : (prefixWord ++ tailWord_8125202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125202).length < 2 ^ (prefixWord ++ tailWord_8125202).sum := by decide
  have hdescent : baseEnd_8125202 < baseStart_8125202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125218 : List Nat := [3, 3, 1, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_8125218 : Nat := 118140960795 + 8125218 * 2 ^ 59
def prefixEnd_8125218 : Nat := 4983230072969 + 3 ^ 40 * 8125218 * 2
def baseEnd_8125218 : Nat := 4172142256563496280907809

theorem tailTrace_8125218 : CollatzResearch.WordTrace tailWord_8125218 prefixEnd_8125218 4172142256563496280907809 := by
  unfold tailWord_8125218
  simp only [CollatzResearch.WordTrace]
  refine ⟨74087761669432584400230077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197567364451820225067280205 74087761669432584400230077)
  ·
    refine ⟨27782910626037219150086279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74087761669432584400230077 27782910626037219150086279)
    ·
      refine ⟨41674365939055828725129419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27782910626037219150086279 41674365939055828725129419)
      ·
        refine ⟨62511548908583743087694129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41674365939055828725129419 62511548908583743087694129)
        ·
          refine ⟨46883661681437807315770597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62511548908583743087694129 46883661681437807315770597)
          ·
            refine ⟨8790686565269588871706987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46883661681437807315770597 8790686565269588871706987)
            ·
              refine ⟨13186029847904383307560481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8790686565269588871706987 13186029847904383307560481)
              ·
                refine ⟨9889522385928287480670361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13186029847904383307560481 9889522385928287480670361)
                ·
                  refine ⟨7417141789446215610502771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9889522385928287480670361 7417141789446215610502771)
                  ·
                    refine ⟨11125712684169323415754157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7417141789446215610502771 11125712684169323415754157)
                    ·
                      refine ⟨4172142256563496280907809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11125712684169323415754157 4172142256563496280907809)
                      ·
                        rfl

theorem cell23_8125218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_8125218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125218 prefixEnd_8125218 := by exact prefixLift 8125218
  have htrace : WordTrace (prefixWord ++ tailWord_8125218) baseStart_8125218 baseEnd_8125218 := by
    simpa [prefixWord, tailWord_8125218, baseEnd_8125218] using wordTrace_append hprefix tailTrace_8125218
  have hstable : (prefixWord ++ tailWord_8125218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125218).length < 2 ^ (prefixWord ++ tailWord_8125218).sum := by decide
  have hdescent : baseEnd_8125218 < baseStart_8125218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125247 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 7]
def baseStart_8125247 : Nat := 118140960795 + 8125247 * 2 ^ 59
def prefixEnd_8125247 : Nat := 4983230072969 + 3 ^ 40 * 8125247 * 2
def baseEnd_8125247 : Nat := 463573016389164074160575

theorem tailTrace_8125247 : CollatzResearch.WordTrace tailWord_8125247 prefixEnd_8125247 463573016389164074160575 := by
  unfold tailWord_8125247
  simp only [CollatzResearch.WordTrace]
  refine ⟨296352104394625275553725995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197568069596416850369150663 296352104394625275553725995)
  ·
    refine ⟨444528156591937913330588993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296352104394625275553725995 444528156591937913330588993)
    ·
      refine ⟨333396117443953434997941745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444528156591937913330588993 333396117443953434997941745)
      ·
        refine ⟨250047088082965076248456309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333396117443953434997941745 250047088082965076248456309)
        ·
          refine ⟨23441914507777975898292779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250047088082965076248456309 23441914507777975898292779)
          ·
            refine ⟨35162871761666963847439169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23441914507777975898292779 35162871761666963847439169)
            ·
              refine ⟨26372153821250222885579377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35162871761666963847439169 26372153821250222885579377)
              ·
                refine ⟨19779115365937667164184533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26372153821250222885579377 19779115365937667164184533)
                ·
                  refine ⟨463573016389164074160575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19779115365937667164184533 463573016389164074160575)
                  ·
                    rfl

theorem cell23_8125247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 7].length) (baseStart_8125247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125247 prefixEnd_8125247 := by exact prefixLift 8125247
  have htrace : WordTrace (prefixWord ++ tailWord_8125247) baseStart_8125247 baseEnd_8125247 := by
    simpa [prefixWord, tailWord_8125247, baseEnd_8125247] using wordTrace_append hprefix tailTrace_8125247
  have hstable : (prefixWord ++ tailWord_8125247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125247).length < 2 ^ (prefixWord ++ tailWord_8125247).sum := by decide
  have hdescent : baseEnd_8125247 < baseStart_8125247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125261 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_8125261 : Nat := 118140960795 + 8125261 * 2 ^ 59
def prefixEnd_8125261 : Nat := 4983230072969 + 3 ^ 40 * 8125261 * 2
def baseEnd_8125261 : Nat := 4172164336231639612670111

theorem tailTrace_8125261 : CollatzResearch.WordTrace tailWord_8125261 prefixEnd_8125261 4172164336231639612670111 := by
  unfold tailWord_8125261
  simp only [CollatzResearch.WordTrace]
  refine ⟨296352615016574555944735637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197568410011049703963157091 296352615016574555944735637)
  ·
    refine ⟨13891528828901932309909483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 296352615016574555944735637 13891528828901932309909483)
    ·
      refine ⟨20837293243352898464864225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13891528828901932309909483 20837293243352898464864225)
      ·
        refine ⟨15627969932514673848648169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20837293243352898464864225 15627969932514673848648169)
        ·
          refine ⟨11720977449386005386486127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15627969932514673848648169 11720977449386005386486127)
          ·
            refine ⟨17581466174079008079729191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11720977449386005386486127 17581466174079008079729191)
            ·
              refine ⟨26372199261118512119593787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17581466174079008079729191 26372199261118512119593787)
              ·
                refine ⟨39558298891677768179390681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26372199261118512119593787 39558298891677768179390681)
                ·
                  refine ⟨29668724168758326134543011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39558298891677768179390681 29668724168758326134543011)
                  ·
                    refine ⟨44503086253137489201814517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29668724168758326134543011 44503086253137489201814517)
                    ·
                      refine ⟨4172164336231639612670111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44503086253137489201814517 4172164336231639612670111)
                      ·
                        rfl

theorem cell23_8125261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_8125261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125261 prefixEnd_8125261 := by exact prefixLift 8125261
  have htrace : WordTrace (prefixWord ++ tailWord_8125261) baseStart_8125261 baseEnd_8125261 := by
    simpa [prefixWord, tailWord_8125261, baseEnd_8125261] using wordTrace_append hprefix tailTrace_8125261
  have hstable : (prefixWord ++ tailWord_8125261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125261).length < 2 ^ (prefixWord ++ tailWord_8125261).sum := by decide
  have hdescent : baseEnd_8125261 < baseStart_8125261 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125264 : List Nat := [2, 1, 1, 1, 1, 4, 5, 3, 5]
def baseStart_8125264 : Nat := 118140960795 + 8125264 * 2 ^ 59
def prefixEnd_8125264 : Nat := 4983230072969 + 3 ^ 40 * 8125264 * 2
def baseEnd_8125264 : Nat := 463573986297067011214733

theorem tailTrace_8125264 : CollatzResearch.WordTrace tailWord_8125264 prefixEnd_8125264 463573986297067011214733 := by
  unfold tailWord_8125264
  simp only [CollatzResearch.WordTrace]
  refine ⟨148176362217781843728547423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197568482957042458304729897 148176362217781843728547423)
  ·
    refine ⟨222264543326672765592821135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148176362217781843728547423 222264543326672765592821135)
    ·
      refine ⟨333396814990009148389231703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222264543326672765592821135 333396814990009148389231703)
      ·
        refine ⟨500095222485013722583847555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333396814990009148389231703 500095222485013722583847555)
        ·
          refine ⟨750142833727520583875771333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500095222485013722583847555 750142833727520583875771333)
          ·
            refine ⟨140651781323910109476707125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 750142833727520583875771333 140651781323910109476707125)
            ·
              refine ⟨13186104499116572763441293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140651781323910109476707125 13186104499116572763441293)
              ·
                refine ⟨4944789187168714786290485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13186104499116572763441293 4944789187168714786290485)
                ·
                  refine ⟨463573986297067011214733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4944789187168714786290485 463573986297067011214733)
                  ·
                    rfl

theorem cell23_8125264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 5].length) (baseStart_8125264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125264 prefixEnd_8125264 := by exact prefixLift 8125264
  have htrace : WordTrace (prefixWord ++ tailWord_8125264) baseStart_8125264 baseEnd_8125264 := by
    simpa [prefixWord, tailWord_8125264, baseEnd_8125264] using wordTrace_append hprefix tailTrace_8125264
  have hstable : (prefixWord ++ tailWord_8125264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125264).length < 2 ^ (prefixWord ++ tailWord_8125264).sum := by decide
  have hdescent : baseEnd_8125264 < baseStart_8125264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125287 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_8125287 : Nat := 118140960795 + 8125287 * 2 ^ 59
def prefixEnd_8125287 : Nat := 4983230072969 + 3 ^ 40 * 8125287 * 2
def baseEnd_8125287 : Nat := 4172177686728656510944991

theorem tailTrace_8125287 : CollatzResearch.WordTrace tailWord_8125287 prefixEnd_8125287 4172177686728656510944991 := by
  unfold tailWord_8125287
  simp only [CollatzResearch.WordTrace]
  refine ⟨296353563314480362385182115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197569042209653574923454743 296353563314480362385182115)
  ·
    refine ⟨444530344971720543577773173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296353563314480362385182115 444530344971720543577773173)
    ·
      refine ⟨41674719841098800960416235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 444530344971720543577773173 41674719841098800960416235)
      ·
        refine ⟨62512079761648201440624353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41674719841098800960416235 62512079761648201440624353)
        ·
          refine ⟨46884059821236151080468265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62512079761648201440624353 46884059821236151080468265)
          ·
            refine ⟨35163044865927113310351199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46884059821236151080468265 35163044865927113310351199)
            ·
              refine ⟨52744567298890669965526799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35163044865927113310351199 52744567298890669965526799)
              ·
                refine ⟨79116850948336004948290199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52744567298890669965526799 79116850948336004948290199)
                ·
                  refine ⟨118675276422504007422435299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79116850948336004948290199 118675276422504007422435299)
                  ·
                    refine ⟨178012914633756011133652949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118675276422504007422435299 178012914633756011133652949)
                    ·
                      refine ⟨4172177686728656510944991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178012914633756011133652949 4172177686728656510944991)
                      ·
                        rfl

theorem cell23_8125287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_8125287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125287 prefixEnd_8125287 := by exact prefixLift 8125287
  have htrace : WordTrace (prefixWord ++ tailWord_8125287) baseStart_8125287 baseEnd_8125287 := by
    simpa [prefixWord, tailWord_8125287, baseEnd_8125287] using wordTrace_append hprefix tailTrace_8125287
  have hstable : (prefixWord ++ tailWord_8125287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125287).length < 2 ^ (prefixWord ++ tailWord_8125287).sum := by decide
  have hdescent : baseEnd_8125287 < baseStart_8125287 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125434 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4]
def baseStart_8125434 : Nat := 118140960795 + 8125434 * 2 ^ 59
def prefixEnd_8125434 : Nat := 4983230072969 + 3 ^ 40 * 8125434 * 2
def baseEnd_8125434 : Nat := 4172253168384867435806815

theorem tailTrace_8125434 : CollatzResearch.WordTrace tailWord_8125434 prefixEnd_8125434 4172253168384867435806815 := by
  unfold tailWord_8125434
  simp only [CollatzResearch.WordTrace]
  refine ⟨74089731211236951622695839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197572616563298537660522237 74089731211236951622695839)
  ·
    refine ⟨111134596816855427434043759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74089731211236951622695839 111134596816855427434043759)
    ·
      refine ⟨166701895225283141151065639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111134596816855427434043759 166701895225283141151065639)
      ·
        refine ⟨250052842837924711726598459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166701895225283141151065639 250052842837924711726598459)
        ·
          refine ⟨375079264256887067589897689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250052842837924711726598459 375079264256887067589897689)
          ·
            refine ⟨281309448192665300692423267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375079264256887067589897689 281309448192665300692423267)
            ·
              refine ⟨421964172288997951038634901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281309448192665300692423267 421964172288997951038634901)
              ·
                refine ⟨19779570576046778954936011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 421964172288997951038634901 19779570576046778954936011)
                ·
                  refine ⟨29669355864070168432404017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19779570576046778954936011 29669355864070168432404017)
                  ·
                    refine ⟨22252016898052626324303013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29669355864070168432404017 22252016898052626324303013)
                    ·
                      refine ⟨4172253168384867435806815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22252016898052626324303013 4172253168384867435806815)
                      ·
                        rfl

theorem cell23_8125434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_8125434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125434 prefixEnd_8125434 := by exact prefixLift 8125434
  have htrace : WordTrace (prefixWord ++ tailWord_8125434) baseStart_8125434 baseEnd_8125434 := by
    simpa [prefixWord, tailWord_8125434, baseEnd_8125434] using wordTrace_append hprefix tailTrace_8125434
  have hstable : (prefixWord ++ tailWord_8125434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125434).length < 2 ^ (prefixWord ++ tailWord_8125434).sum := by decide
  have hdescent : baseEnd_8125434 < baseStart_8125434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125441 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_8125441 : Nat := 118140960795 + 8125441 * 2 ^ 59
def prefixEnd_8125441 : Nat := 4983230072969 + 3 ^ 40 * 8125441 * 2
def baseEnd_8125441 : Nat := 4172256762749448908419283

theorem tailTrace_8125441 : CollatzResearch.WordTrace tailWord_8125441 prefixEnd_8125441 4172256762749448908419283 := by
  unfold tailWord_8125441
  simp only [CollatzResearch.WordTrace]
  refine ⟨296359180155922446686288177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197572786770614964457525451 296359180155922446686288177)
  ·
    refine ⟨222269385116941835014716133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296359180155922446686288177 222269385116941835014716133)
    ·
      refine ⟨41675509709426594065259275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222269385116941835014716133 41675509709426594065259275)
      ·
        refine ⟨62513264564139891097888913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41675509709426594065259275 62513264564139891097888913)
        ·
          refine ⟨46884948423104918323416685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62513264564139891097888913 46884948423104918323416685)
          ·
            refine ⟨17581855658664344371281257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46884948423104918323416685 17581855658664344371281257)
            ·
              refine ⟨13186391743998258278460943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17581855658664344371281257 13186391743998258278460943)
              ·
                refine ⟨19779587615997387417691415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13186391743998258278460943 19779587615997387417691415)
                ·
                  refine ⟨29669381423996081126537123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19779587615997387417691415 29669381423996081126537123)
                  ·
                    refine ⟨44504072135994121689805685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29669381423996081126537123 44504072135994121689805685)
                    ·
                      refine ⟨4172256762749448908419283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44504072135994121689805685 4172256762749448908419283)
                      ·
                        rfl

theorem cell23_8125441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_8125441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125441 prefixEnd_8125441 := by exact prefixLift 8125441
  have htrace : WordTrace (prefixWord ++ tailWord_8125441) baseStart_8125441 baseEnd_8125441 := by
    simpa [prefixWord, tailWord_8125441, baseEnd_8125441] using wordTrace_append hprefix tailTrace_8125441
  have hstable : (prefixWord ++ tailWord_8125441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125441).length < 2 ^ (prefixWord ++ tailWord_8125441).sum := by decide
  have hdescent : baseEnd_8125441 < baseStart_8125441 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125442 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_8125442 : Nat := 118140960795 + 8125442 * 2 ^ 59
def prefixEnd_8125442 : Nat := 4983230072969 + 3 ^ 40 * 8125442 * 2
def baseEnd_8125442 : Nat := 4172257276230103404506779

theorem tailTrace_8125442 : CollatzResearch.WordTrace tailWord_8125442 prefixEnd_8125442 4172257276230103404506779 := by
  unfold tailWord_8125442
  simp only [CollatzResearch.WordTrace]
  refine ⟨74089804157229705964268645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197572811085945882571383053 74089804157229705964268645)
  ·
    refine ⟨13891838279480569868300371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74089804157229705964268645 13891838279480569868300371)
    ·
      refine ⟨20837757419220854802450557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13891838279480569868300371 20837757419220854802450557)
      ·
        refine ⟨7814159032207820550918959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20837757419220854802450557 7814159032207820550918959)
        ·
          refine ⟨11721238548311730826378439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7814159032207820550918959 11721238548311730826378439)
          ·
            refine ⟨17581857822467596239567659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11721238548311730826378439 17581857822467596239567659)
            ·
              refine ⟨26372786733701394359351489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17581857822467596239567659 26372786733701394359351489)
              ·
                refine ⟨19779590050276045769513617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26372786733701394359351489 19779590050276045769513617)
                ·
                  refine ⟨14834692537707034327135213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19779590050276045769513617 14834692537707034327135213)
                  ·
                    refine ⟨5563009701640137872675705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14834692537707034327135213 5563009701640137872675705)
                    ·
                      refine ⟨4172257276230103404506779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5563009701640137872675705 4172257276230103404506779)
                      ·
                        rfl

theorem cell23_8125442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_8125442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125442 prefixEnd_8125442 := by exact prefixLift 8125442
  have htrace : WordTrace (prefixWord ++ tailWord_8125442) baseStart_8125442 baseEnd_8125442 := by
    simpa [prefixWord, tailWord_8125442, baseEnd_8125442] using wordTrace_append hprefix tailTrace_8125442
  have hstable : (prefixWord ++ tailWord_8125442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125442).length < 2 ^ (prefixWord ++ tailWord_8125442).sum := by decide
  have hdescent : baseEnd_8125442 < baseStart_8125442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125472 : List Nat := [2, 1, 1, 7, 2, 1, 1, 2, 1, 1, 4]
def baseStart_8125472 : Nat := 118140960795 + 8125472 * 2 ^ 59
def prefixEnd_8125472 : Nat := 4983230072969 + 3 ^ 40 * 8125472 * 2
def baseEnd_8125472 : Nat := 4172272680649738287131641

theorem tailTrace_8125472 : CollatzResearch.WordTrace tailWord_8125472 prefixEnd_8125472 4172272680649738287131641 := by
  unfold tailWord_8125472
  simp only [CollatzResearch.WordTrace]
  refine ⟨148180155409405069490333335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197573540545873425987111113 148180155409405069490333335)
  ·
    refine ⟨222270233114107604235500003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148180155409405069490333335 222270233114107604235500003)
    ·
      refine ⟨333405349671161406353250005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222270233114107604235500003 333405349671161406353250005)
      ·
        refine ⟨7814187882917845461404297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 333405349671161406353250005 7814187882917845461404297)
        ·
          refine ⟨5860640912188384096053223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7814187882917845461404297 5860640912188384096053223)
          ·
            refine ⟨8790961368282576144079835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5860640912188384096053223 8790961368282576144079835)
            ·
              refine ⟨13186442052423864216119753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8790961368282576144079835 13186442052423864216119753)
              ·
                refine ⟨9889831539317898162089815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13186442052423864216119753 9889831539317898162089815)
                ·
                  refine ⟨14834747308976847243134723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9889831539317898162089815 14834747308976847243134723)
                  ·
                    refine ⟨22252120963465270864702085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14834747308976847243134723 22252120963465270864702085)
                    ·
                      refine ⟨4172272680649738287131641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22252120963465270864702085 4172272680649738287131641)
                      ·
                        rfl

theorem cell23_8125472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_8125472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125472 prefixEnd_8125472 := by exact prefixLift 8125472
  have htrace : WordTrace (prefixWord ++ tailWord_8125472) baseStart_8125472 baseEnd_8125472 := by
    simpa [prefixWord, tailWord_8125472, baseEnd_8125472] using wordTrace_append hprefix tailTrace_8125472
  have hstable : (prefixWord ++ tailWord_8125472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125472).length < 2 ^ (prefixWord ++ tailWord_8125472).sum := by decide
  have hdescent : baseEnd_8125472 < baseStart_8125472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125492 : List Nat := [2, 5, 1, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_8125492 : Nat := 118140960795 + 8125492 * 2 ^ 59
def prefixEnd_8125492 : Nat := 4983230072969 + 3 ^ 40 * 8125492 * 2
def baseEnd_8125492 : Nat := 4172282950262828208881549

theorem tailTrace_8125492 : CollatzResearch.WordTrace tailWord_8125492 prefixEnd_8125492 4172282950262828208881549 := by
  unfold tailWord_8125492
  simp only [CollatzResearch.WordTrace]
  refine ⟨148180520139368841198197365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197574026852491788264263153 148180520139368841198197365)
  ·
    refine ⟨13891923763065828862331003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148180520139368841198197365 13891923763065828862331003)
    ·
      refine ⟨20837885644598743293496505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13891923763065828862331003 20837885644598743293496505)
      ·
        refine ⟨15628414233449057470122379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20837885644598743293496505 15628414233449057470122379)
        ·
          refine ⟨23442621350173586205183569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15628414233449057470122379 23442621350173586205183569)
          ·
            refine ⟨17581966012630189653887677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23442621350173586205183569 17581966012630189653887677)
            ·
              refine ⟨6593237254736321120207879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17581966012630189653887677 6593237254736321120207879)
              ·
                refine ⟨9889855882104481680311819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593237254736321120207879 9889855882104481680311819)
                ·
                  refine ⟨14834783823156722520467729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9889855882104481680311819 14834783823156722520467729)
                  ·
                    refine ⟨11126087867367541890350797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14834783823156722520467729 11126087867367541890350797)
                    ·
                      refine ⟨4172282950262828208881549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11126087867367541890350797 4172282950262828208881549)
                      ·
                        rfl

theorem cell23_8125492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_8125492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125492 prefixEnd_8125492 := by exact prefixLift 8125492
  have htrace : WordTrace (prefixWord ++ tailWord_8125492) baseStart_8125492 baseEnd_8125492 := by
    simpa [prefixWord, tailWord_8125492, baseEnd_8125492] using wordTrace_append hprefix tailTrace_8125492
  have hstable : (prefixWord ++ tailWord_8125492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125492).length < 2 ^ (prefixWord ++ tailWord_8125492).sum := by decide
  have hdescent : baseEnd_8125492 < baseStart_8125492 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125498 : List Nat := [3, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2]
def baseStart_8125498 : Nat := 118140960795 + 8125498 * 2 ^ 59
def prefixEnd_8125498 : Nat := 4983230072969 + 3 ^ 40 * 8125498 * 2
def baseEnd_8125498 : Nat := 4172286031146755185406521

theorem tailTrace_8125498 : CollatzResearch.WordTrace tailWord_8125498 prefixEnd_8125498 4172286031146755185406521 := by
  unfold tailWord_8125498
  simp only [CollatzResearch.WordTrace]
  refine ⟨74090314779178986355278287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197574172744477296947408765 74090314779178986355278287)
  ·
    refine ⟨111135472168768479532917431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74090314779178986355278287 111135472168768479532917431)
    ·
      refine ⟨166703208253152719299376147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111135472168768479532917431 166703208253152719299376147)
      ·
        refine ⟨250054812379729078949064221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166703208253152719299376147 250054812379729078949064221)
        ·
          refine ⟨93770554642398404605899083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250054812379729078949064221 93770554642398404605899083)
          ·
            refine ⟨140655831963597606908848625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93770554642398404605899083 140655831963597606908848625)
            ·
              refine ⟨105491873972698205181636469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140655831963597606908848625 105491873972698205181636469)
              ·
                refine ⟨9889863184940456735778419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105491873972698205181636469 9889863184940456735778419)
                ·
                  refine ⟨14834794777410685103667629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9889863184940456735778419 14834794777410685103667629)
                  ·
                    refine ⟨5563048041529006913875361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14834794777410685103667629 5563048041529006913875361)
                    ·
                      refine ⟨4172286031146755185406521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5563048041529006913875361 4172286031146755185406521)
                      ·
                        rfl

theorem cell23_8125498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2].length) (baseStart_8125498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125498 prefixEnd_8125498 := by exact prefixLift 8125498
  have htrace : WordTrace (prefixWord ++ tailWord_8125498) baseStart_8125498 baseEnd_8125498 := by
    simpa [prefixWord, tailWord_8125498, baseEnd_8125498] using wordTrace_append hprefix tailTrace_8125498
  have hstable : (prefixWord ++ tailWord_8125498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125498).length < 2 ^ (prefixWord ++ tailWord_8125498).sum := by decide
  have hdescent : baseEnd_8125498 < baseStart_8125498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125504 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 2, 6]
def baseStart_8125504 : Nat := 118140960795 + 8125504 * 2 ^ 59
def prefixEnd_8125504 : Nat := 4983230072969 + 3 ^ 40 * 8125504 * 2
def baseEnd_8125504 : Nat := 1390763037343560720643831

theorem tailTrace_8125504 : CollatzResearch.WordTrace tailWord_8125504 prefixEnd_8125504 1390763037343560720643831 := by
  unfold tailWord_8125504
  simp only [CollatzResearch.WordTrace]
  refine ⟨148180738977347104222915783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197574318636462805630554377 148180738977347104222915783)
  ·
    refine ⟨222271108466020656334373675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148180738977347104222915783 222271108466020656334373675)
    ·
      refine ⟨333406662699030984501560513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222271108466020656334373675 333406662699030984501560513)
      ·
        refine ⟨250054997024273238376170385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333406662699030984501560513 250054997024273238376170385)
        ·
          refine ⟨187541247768204928782127789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250054997024273238376170385 187541247768204928782127789)
          ·
            refine ⟨70327967913076848293297921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187541247768204928782127789 70327967913076848293297921)
            ·
              refine ⟨52745975934807636219973441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70327967913076848293297921 52745975934807636219973441)
              ·
                refine ⟨39559481951105727164980081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52745975934807636219973441 39559481951105727164980081)
                ·
                  refine ⟨29669611463329295373735061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39559481951105727164980081 29669611463329295373735061)
                  ·
                    refine ⟨1390763037343560720643831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29669611463329295373735061 1390763037343560720643831)
                    ·
                      rfl

theorem cell23_8125504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 2, 6].length) (baseStart_8125504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125504 prefixEnd_8125504 := by exact prefixLift 8125504
  have htrace : WordTrace (prefixWord ++ tailWord_8125504) baseStart_8125504 baseEnd_8125504 := by
    simpa [prefixWord, tailWord_8125504, baseEnd_8125504] using wordTrace_append hprefix tailTrace_8125504
  have hstable : (prefixWord ++ tailWord_8125504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125504).length < 2 ^ (prefixWord ++ tailWord_8125504).sum := by decide
  have hdescent : baseEnd_8125504 < baseStart_8125504 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125514 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_8125514 : Nat := 118140960795 + 8125514 * 2 ^ 59
def prefixEnd_8125514 : Nat := 4983230072969 + 3 ^ 40 * 8125514 * 2
def baseEnd_8125514 : Nat := 4172294246837227122806447

theorem tailTrace_8125514 : CollatzResearch.WordTrace tailWord_8125514 prefixEnd_8125514 4172294246837227122806447 := by
  unfold tailWord_8125514
  simp only [CollatzResearch.WordTrace]
  refine ⟨74090460671164495038423899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197574561789771986769130397 74090460671164495038423899)
  ·
    refine ⟨111135691006746742557635849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74090460671164495038423899 111135691006746742557635849)
    ·
      refine ⟨83351768255060056918226887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111135691006746742557635849 83351768255060056918226887)
      ·
        refine ⟨125027652382590085377340331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83351768255060056918226887 125027652382590085377340331)
        ·
          refine ⟨187541478573885128066010497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125027652382590085377340331 187541478573885128066010497)
          ·
            refine ⟨140656108930413846049507873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187541478573885128066010497 140656108930413846049507873)
            ·
              refine ⟨105492081697810384537130905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140656108930413846049507873 105492081697810384537130905)
              ·
                refine ⟨79119061273357788402848179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105492081697810384537130905 79119061273357788402848179)
                ·
                  refine ⟨118678591910036682604272269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79119061273357788402848179 118678591910036682604272269)
                  ·
                    refine ⟨44504471966263755976602101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118678591910036682604272269 44504471966263755976602101)
                    ·
                      refine ⟨4172294246837227122806447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44504471966263755976602101 4172294246837227122806447)
                      ·
                        rfl

theorem cell23_8125514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_8125514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125514 prefixEnd_8125514 := by exact prefixLift 8125514
  have htrace : WordTrace (prefixWord ++ tailWord_8125514) baseStart_8125514 baseEnd_8125514 := by
    simpa [prefixWord, tailWord_8125514, baseEnd_8125514] using wordTrace_append hprefix tailTrace_8125514
  have hstable : (prefixWord ++ tailWord_8125514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125514).length < 2 ^ (prefixWord ++ tailWord_8125514).sum := by decide
  have hdescent : baseEnd_8125514 < baseStart_8125514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125528 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 1, 4, 2]
def baseStart_8125528 : Nat := 118140960795 + 8125528 * 2 ^ 59
def prefixEnd_8125528 : Nat := 4983230072969 + 3 ^ 40 * 8125528 * 2
def baseEnd_8125528 : Nat := 4172301435566390068031383

theorem tailTrace_8125528 : CollatzResearch.WordTrace tailWord_8125528 prefixEnd_8125528 4172301435566390068031383 := by
  unfold tailWord_8125528
  simp only [CollatzResearch.WordTrace]
  refine ⟨148181176653303630272352619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197574902204404840363136825 148181176653303630272352619)
  ·
    refine ⟨222271764979955445408528929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148181176653303630272352619 222271764979955445408528929)
    ·
      refine ⟨166703823734966584056396697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222271764979955445408528929 166703823734966584056396697)
      ·
        refine ⟨125027867801224938042297523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166703823734966584056396697 125027867801224938042297523)
        ·
          refine ⟨187541801701837407063446285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125027867801224938042297523 187541801701837407063446285)
          ·
            refine ⟨70328175638189027648792357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187541801701837407063446285 70328175638189027648792357)
            ·
              refine ⟨13186532932160442684148567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70328175638189027648792357 13186532932160442684148567)
              ·
                refine ⟨19779799398240664026222851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13186532932160442684148567 19779799398240664026222851)
                ·
                  refine ⟨29669699097360996039334277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19779799398240664026222851 29669699097360996039334277)
                  ·
                    refine ⟨5563068580755186757375177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29669699097360996039334277 5563068580755186757375177)
                    ·
                      refine ⟨4172301435566390068031383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5563068580755186757375177 4172301435566390068031383)
                      ·
                        rfl

theorem cell23_8125528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_8125528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125528 prefixEnd_8125528 := by exact prefixLift 8125528
  have htrace : WordTrace (prefixWord ++ tailWord_8125528) baseStart_8125528 baseEnd_8125528 := by
    simpa [prefixWord, tailWord_8125528, baseEnd_8125528] using wordTrace_append hprefix tailTrace_8125528
  have hstable : (prefixWord ++ tailWord_8125528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125528).length < 2 ^ (prefixWord ++ tailWord_8125528).sum := by decide
  have hdescent : baseEnd_8125528 < baseStart_8125528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125598 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_8125598 : Nat := 118140960795 + 8125598 * 2 ^ 59
def prefixEnd_8125598 : Nat := 4983230072969 + 3 ^ 40 * 8125598 * 2
def baseEnd_8125598 : Nat := 1390779126404068264718687

theorem tailTrace_8125598 : CollatzResearch.WordTrace tailWord_8125598 prefixEnd_8125598 1390779126404068264718687 := by
  unfold tailWord_8125598
  simp only [CollatzResearch.WordTrace]
  refine ⟨37045613302044207812469181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197576604277569108333168965 37045613302044207812469181)
  ·
    refine ⟨13892104988266577929675943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37045613302044207812469181 13892104988266577929675943)
    ·
      refine ⟨20838157482399866894513915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13892104988266577929675943 20838157482399866894513915)
      ·
        refine ⟨31257236223599800341770873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20838157482399866894513915 31257236223599800341770873)
        ·
          refine ⟨23442927167699850256328155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31257236223599800341770873 23442927167699850256328155)
          ·
            refine ⟨35164390751549775384492233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23442927167699850256328155 35164390751549775384492233)
            ·
              refine ⟨26373293063662331538369175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35164390751549775384492233 26373293063662331538369175)
              ·
                refine ⟨39559939595493497307553763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26373293063662331538369175 39559939595493497307553763)
                ·
                  refine ⟨59339909393240245961330645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39559939595493497307553763 59339909393240245961330645)
                  ·
                    refine ⟨1390779126404068264718687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59339909393240245961330645 1390779126404068264718687)
                    ·
                      rfl

theorem cell23_8125598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_8125598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125598 prefixEnd_8125598 := by exact prefixLift 8125598
  have htrace : WordTrace (prefixWord ++ tailWord_8125598) baseStart_8125598 baseEnd_8125598 := by
    simpa [prefixWord, tailWord_8125598, baseEnd_8125598] using wordTrace_append hprefix tailTrace_8125598
  have hstable : (prefixWord ++ tailWord_8125598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125598).length < 2 ^ (prefixWord ++ tailWord_8125598).sum := by decide
  have hdescent : baseEnd_8125598 < baseStart_8125598 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125601 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_8125601 : Nat := 118140960795 + 8125601 * 2 ^ 59
def prefixEnd_8125601 : Nat := 4983230072969 + 3 ^ 40 * 8125601 * 2
def baseEnd_8125601 : Nat := 4172338919654168282418547

theorem tailTrace_8125601 : CollatzResearch.WordTrace tailWord_8125601 prefixEnd_8125601 4172338919654168282418547 := by
  unfold tailWord_8125601
  simp only [CollatzResearch.WordTrace]
  refine ⟨296365015835342794012112657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197576677223561862674741771 296365015835342794012112657)
  ·
    refine ⟨222273761876507095509084493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 296365015835342794012112657 222273761876507095509084493)
    ·
      refine ⟨83352660703690160815906685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222273761876507095509084493 83352660703690160815906685)
      ·
        refine ⟨31257247763883810305965007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83352660703690160815906685 31257247763883810305965007)
        ·
          refine ⟨46885871645825715458947511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31257247763883810305965007 46885871645825715458947511)
          ·
            refine ⟨70328807468738573188421267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46885871645825715458947511 70328807468738573188421267)
            ·
              refine ⟨105493211203107859782631901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70328807468738573188421267 105493211203107859782631901)
              ·
                refine ⟨39559954201165447418486963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105493211203107859782631901 39559954201165447418486963)
                ·
                  refine ⟨59339931301748171127730445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39559954201165447418486963 59339931301748171127730445)
                  ·
                    refine ⟨22252474238155564172898917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59339931301748171127730445 22252474238155564172898917)
                    ·
                      refine ⟨4172338919654168282418547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22252474238155564172898917 4172338919654168282418547)
                      ·
                        rfl

theorem cell23_8125601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_8125601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125601 prefixEnd_8125601 := by exact prefixLift 8125601
  have htrace : WordTrace (prefixWord ++ tailWord_8125601) baseStart_8125601 baseEnd_8125601 := by
    simpa [prefixWord, tailWord_8125601, baseEnd_8125601] using wordTrace_append hprefix tailTrace_8125601
  have hstable : (prefixWord ++ tailWord_8125601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125601).length < 2 ^ (prefixWord ++ tailWord_8125601).sum := by decide
  have hdescent : baseEnd_8125601 < baseStart_8125601 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125602 : List Nat := [3, 3, 1, 3, 2, 2, 1, 3, 5]
def baseStart_8125602 : Nat := 118140960795 + 8125602 * 2 ^ 59
def prefixEnd_8125602 : Nat := 4983230072969 + 3 ^ 40 * 8125602 * 2
def baseEnd_8125602 : Nat := 463593270348313642056227

theorem tailTrace_8125602 : CollatzResearch.WordTrace tailWord_8125602 prefixEnd_8125602 463593270348313642056227 := by
  unfold tailWord_8125602
  simp only [CollatzResearch.WordTrace]
  refine ⟨74091263077084792795724765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197576701538892780788599373 74091263077084792795724765)
  ·
    refine ⟨27784223653906797298396787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74091263077084792795724765 27784223653906797298396787)
    ·
      refine ⟨41676335480860195947595181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27784223653906797298396787 41676335480860195947595181)
      ·
        refine ⟨15628625805322573480348193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41676335480860195947595181 15628625805322573480348193)
        ·
          refine ⟨11721469353991930110261145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15628625805322573480348193 11721469353991930110261145)
          ·
            refine ⟨8791102015493947582695859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11721469353991930110261145 8791102015493947582695859)
            ·
              refine ⟨13186653023240921374043789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8791102015493947582695859 13186653023240921374043789)
              ·
                refine ⟨4944994883715345515266421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13186653023240921374043789 4944994883715345515266421)
                ·
                  refine ⟨463593270348313642056227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4944994883715345515266421 463593270348313642056227)
                  ·
                    rfl

theorem cell23_8125602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_8125602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125602 prefixEnd_8125602 := by exact prefixLift 8125602
  have htrace : WordTrace (prefixWord ++ tailWord_8125602) baseStart_8125602 baseEnd_8125602 := by
    simpa [prefixWord, tailWord_8125602, baseEnd_8125602] using wordTrace_append hprefix tailTrace_8125602
  have hstable : (prefixWord ++ tailWord_8125602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125602).length < 2 ^ (prefixWord ++ tailWord_8125602).sum := by decide
  have hdescent : baseEnd_8125602 < baseStart_8125602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125618 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_8125618 : Nat := 118140960795 + 8125618 * 2 ^ 59
def prefixEnd_8125618 : Nat := 4983230072969 + 3 ^ 40 * 8125618 * 2
def baseEnd_8125618 : Nat := 4172347648825294715905969

theorem tailTrace_8125618 : CollatzResearch.WordTrace tailWord_8125618 prefixEnd_8125618 4172347648825294715905969 := by
  unfold tailWord_8125618
  simp only [CollatzResearch.WordTrace]
  refine ⟨74091408969070301478870377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197577090584187470610321005 74091408969070301478870377)
  ·
    refine ⟨55568556726802726109152783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74091408969070301478870377 55568556726802726109152783)
    ·
      refine ⟨83352835090204089163729175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55568556726802726109152783 83352835090204089163729175)
      ·
        refine ⟨125029252635306133745593763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83352835090204089163729175 125029252635306133745593763)
        ·
          refine ⟨187543878952959200618390645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125029252635306133745593763 187543878952959200618390645)
          ·
            refine ⟨17582238651839925057974123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187543878952959200618390645 17582238651839925057974123)
            ·
              refine ⟨26373357977759887586961185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17582238651839925057974123 26373357977759887586961185)
              ·
                refine ⟨19780018483319915690220889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26373357977759887586961185 19780018483319915690220889)
                ·
                  refine ⟨14835013862489936767665667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19780018483319915690220889 14835013862489936767665667)
                  ·
                    refine ⟨22252520793734905151498501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14835013862489936767665667 22252520793734905151498501)
                    ·
                      refine ⟨4172347648825294715905969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22252520793734905151498501 4172347648825294715905969)
                      ·
                        rfl

theorem cell23_8125618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_8125618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125618 prefixEnd_8125618 := by exact prefixLift 8125618
  have htrace : WordTrace (prefixWord ++ tailWord_8125618) baseStart_8125618 baseEnd_8125618 := by
    simpa [prefixWord, tailWord_8125618, baseEnd_8125618] using wordTrace_append hprefix tailTrace_8125618
  have hstable : (prefixWord ++ tailWord_8125618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125618).length < 2 ^ (prefixWord ++ tailWord_8125618).sum := by decide
  have hdescent : baseEnd_8125618 < baseStart_8125618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125652 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_8125652 : Nat := 118140960795 + 8125652 * 2 ^ 59
def prefixEnd_8125652 : Nat := 4983230072969 + 3 ^ 40 * 8125652 * 2
def baseEnd_8125652 : Nat := 4172365107167547582880813

theorem tailTrace_8125652 : CollatzResearch.WordTrace tailWord_8125652 prefixEnd_8125652 4172365107167547582880813 := by
  unfold tailWord_8125652
  simp only [CollatzResearch.WordTrace]
  refine ⟨148183437979079014861109605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197577917305438686481479473 148183437979079014861109605)
  ·
    refine ⟨27784394621077315286458051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148183437979079014861109605 27784394621077315286458051)
    ·
      refine ⟨41676591931615972929687077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27784394621077315286458051 41676591931615972929687077)
      ·
        refine ⟨7814360987177994924316327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41676591931615972929687077 7814360987177994924316327)
        ·
          refine ⟨11721541480766992386474491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7814360987177994924316327 11721541480766992386474491)
          ·
            refine ⟨17582312221150488579711737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11721541480766992386474491 17582312221150488579711737)
            ·
              refine ⟨13186734165862866434783803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17582312221150488579711737 13186734165862866434783803)
              ·
                refine ⟨19780101248794299652175705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13186734165862866434783803 19780101248794299652175705)
                ·
                  refine ⟨14835075936595724739131779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19780101248794299652175705 14835075936595724739131779)
                  ·
                    refine ⟨22252613904893587108697669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14835075936595724739131779 22252613904893587108697669)
                    ·
                      refine ⟨4172365107167547582880813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22252613904893587108697669 4172365107167547582880813)
                      ·
                        rfl

theorem cell23_8125652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_8125652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125652 prefixEnd_8125652 := by exact prefixLift 8125652
  have htrace : WordTrace (prefixWord ++ tailWord_8125652) baseStart_8125652 baseEnd_8125652 := by
    simpa [prefixWord, tailWord_8125652, baseEnd_8125652] using wordTrace_append hprefix tailTrace_8125652
  have hstable : (prefixWord ++ tailWord_8125652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125652).length < 2 ^ (prefixWord ++ tailWord_8125652).sum := by decide
  have hdescent : baseEnd_8125652 < baseStart_8125652 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125679 : List Nat := [1, 1, 2, 1, 7, 2, 2, 2, 1, 4]
def baseStart_8125679 : Nat := 118140960795 + 8125679 * 2 ^ 59
def prefixEnd_8125679 : Nat := 4983230072969 + 3 ^ 40 * 8125679 * 2
def baseEnd_8125679 : Nat := 1390792990381739659081063

theorem tailTrace_8125679 : CollatzResearch.WordTrace tailWord_8125679 prefixEnd_8125679 1390792990381739659081063 := by
  unfold tailWord_8125679
  simp only [CollatzResearch.WordTrace]
  refine ⟨296367860729060213333452091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197578573819373475555634727 296367860729060213333452091)
  ·
    refine ⟨444551791093590320000178137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296367860729060213333452091 444551791093590320000178137)
    ·
      refine ⟨333413843320192740000133603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444551791093590320000178137 333413843320192740000133603)
      ·
        refine ⟨500120764980289110000200405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333413843320192740000133603 500120764980289110000200405)
        ·
          refine ⟨11721580429225526015629697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 500120764980289110000200405 11721580429225526015629697)
          ·
            refine ⟨8791185321919144511722273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11721580429225526015629697 8791185321919144511722273)
            ·
              refine ⟨6593388991439358383791705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8791185321919144511722273 6593388991439358383791705)
              ·
                refine ⟨4945041743579518787843779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6593388991439358383791705 4945041743579518787843779)
                ·
                  refine ⟨7417562615369278181765669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4945041743579518787843779 7417562615369278181765669)
                  ·
                    refine ⟨1390792990381739659081063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7417562615369278181765669 1390792990381739659081063)
                    ·
                      rfl

theorem cell23_8125679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 1, 4].length) (baseStart_8125679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125679 prefixEnd_8125679 := by exact prefixLift 8125679
  have htrace : WordTrace (prefixWord ++ tailWord_8125679) baseStart_8125679 baseEnd_8125679 := by
    simpa [prefixWord, tailWord_8125679, baseEnd_8125679] using wordTrace_append hprefix tailTrace_8125679
  have hstable : (prefixWord ++ tailWord_8125679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125679).length < 2 ^ (prefixWord ++ tailWord_8125679).sum := by decide
  have hdescent : baseEnd_8125679 < baseStart_8125679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125708 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 3, 1, 4]
def baseStart_8125708 : Nat := 118140960795 + 8125708 * 2 ^ 59
def prefixEnd_8125708 : Nat := 4983230072969 + 3 ^ 40 * 8125708 * 2
def baseEnd_8125708 : Nat := 4172393862084199363780555

theorem tailTrace_8125708 : CollatzResearch.WordTrace tailWord_8125708 prefixEnd_8125708 4172393862084199363780555 := by
  unfold tailWord_8125708
  simp only [CollatzResearch.WordTrace]
  refine ⟨148184459222977575643128889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197579278963970100857505185 148184459222977575643128889)
  ·
    refine ⟨111138344417233181732346667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148184459222977575643128889 111138344417233181732346667)
    ·
      refine ⟨166707516625849772598520001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111138344417233181732346667 166707516625849772598520001)
      ·
        refine ⟨125030637469387329448890001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166707516625849772598520001 125030637469387329448890001)
        ·
          refine ⟨93772978102040497086667501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125030637469387329448890001 93772978102040497086667501)
          ·
            refine ⟨35164866788265186407500313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93772978102040497086667501 35164866788265186407500313)
            ·
              refine ⟨26373650091198889805625235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35164866788265186407500313 26373650091198889805625235)
              ·
                refine ⟨39560475136798334708437853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26373650091198889805625235 39560475136798334708437853)
                ·
                  refine ⟨14835178176299375515664195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39560475136798334708437853 14835178176299375515664195)
                  ·
                    refine ⟨22252767264449063273496293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14835178176299375515664195 22252767264449063273496293)
                    ·
                      refine ⟨4172393862084199363780555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22252767264449063273496293 4172393862084199363780555)
                      ·
                        rfl

theorem cell23_8125708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_8125708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125708 prefixEnd_8125708 := by exact prefixLift 8125708
  have htrace : WordTrace (prefixWord ++ tailWord_8125708) baseStart_8125708 baseEnd_8125708 := by
    simpa [prefixWord, tailWord_8125708, baseEnd_8125708] using wordTrace_append hprefix tailTrace_8125708
  have hstable : (prefixWord ++ tailWord_8125708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125708).length < 2 ^ (prefixWord ++ tailWord_8125708).sum := by decide
  have hdescent : baseEnd_8125708 < baseStart_8125708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125722 : List Nat := [3, 1, 1, 3, 3, 3, 2, 1, 1, 5]
def baseStart_8125722 : Nat := 118140960795 + 8125722 * 2 ^ 59
def prefixEnd_8125722 : Nat := 4983230072969 + 3 ^ 40 * 8125722 * 2
def baseEnd_8125722 : Nat := 1390800350271120769668497

theorem tailTrace_8125722 : CollatzResearch.WordTrace tailWord_8125722 prefixEnd_8125722 1390800350271120769668497 := by
  unfold tailWord_8125722
  simp only [CollatzResearch.WordTrace]
  refine ⟨74092357266976107919316855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197579619378602954451511613 74092357266976107919316855)
  ·
    refine ⟨111138535900464161878975283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74092357266976107919316855 111138535900464161878975283)
    ·
      refine ⟨166707803850696242818462925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111138535900464161878975283 166707803850696242818462925)
      ·
        refine ⟨62515426444011091056923597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166707803850696242818462925 62515426444011091056923597)
        ·
          refine ⟨23443284916504159146346349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62515426444011091056923597 23443284916504159146346349)
          ·
            refine ⟨8791231843689059679879881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23443284916504159146346349 8791231843689059679879881)
            ·
              refine ⟨6593423882766794759909911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8791231843689059679879881 6593423882766794759909911)
              ·
                refine ⟨9890135824150192139864867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593423882766794759909911 9890135824150192139864867)
                ·
                  refine ⟨14835203736225288209797301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9890135824150192139864867 14835203736225288209797301)
                  ·
                    refine ⟨1390800350271120769668497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14835203736225288209797301 1390800350271120769668497)
                    ·
                      rfl

theorem cell23_8125722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_8125722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125722 prefixEnd_8125722 := by exact prefixLift 8125722
  have htrace : WordTrace (prefixWord ++ tailWord_8125722) baseStart_8125722 baseEnd_8125722 := by
    simpa [prefixWord, tailWord_8125722, baseEnd_8125722] using wordTrace_append hprefix tailTrace_8125722
  have hstable : (prefixWord ++ tailWord_8125722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125722).length < 2 ^ (prefixWord ++ tailWord_8125722).sum := by decide
  have hdescent : baseEnd_8125722 < baseStart_8125722 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125731 : List Nat := [1, 1, 1, 4, 2, 4, 10]
def baseStart_8125731 : Nat := 118140960795 + 8125731 * 2 ^ 59
def prefixEnd_8125731 : Nat := 4983230072969 + 3 ^ 40 * 8125731 * 2
def baseEnd_8125731 : Nat := 51511181137521639182629

theorem tailTrace_8125731 : CollatzResearch.WordTrace tailWord_8125731 prefixEnd_8125731 51511181137521639182629 := by
  unfold tailWord_8125731
  simp only [CollatzResearch.WordTrace]
  refine ⟨296369757324871826214345047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197579838216581217476230031 296369757324871826214345047)
  ·
    refine ⟨444554635987307739321517571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296369757324871826214345047 444554635987307739321517571)
    ·
      refine ⟨666831953980961608982276357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444554635987307739321517571 666831953980961608982276357)
      ·
        refine ⟨125030991371430301684176817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 666831953980961608982276357 125030991371430301684176817)
        ·
          refine ⟨93773243528572726263132613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125030991371430301684176817 93773243528572726263132613)
          ·
            refine ⟨17582483161607386174337365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93773243528572726263132613 17582483161607386174337365)
            ·
              refine ⟨51511181137521639182629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17582483161607386174337365 51511181137521639182629)
              ·
                rfl

theorem cell23_8125731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 10].length) (baseStart_8125731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125731 prefixEnd_8125731 := by exact prefixLift 8125731
  have htrace : WordTrace (prefixWord ++ tailWord_8125731) baseStart_8125731 baseEnd_8125731 := by
    simpa [prefixWord, tailWord_8125731, baseEnd_8125731] using wordTrace_append hprefix tailTrace_8125731
  have hstable : (prefixWord ++ tailWord_8125731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125731).length < 2 ^ (prefixWord ++ tailWord_8125731).sum := by decide
  have hdescent : baseEnd_8125731 < baseStart_8125731 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8125748 : List Nat := [2, 5, 1, 1, 1, 1, 2, 10]
def baseStart_8125748 : Nat := 118140960795 + 8125748 * 2 ^ 59
def prefixEnd_8125748 : Nat := 4983230072969 + 3 ^ 40 * 8125748 * 2
def baseEnd_8125748 : Nat := 154533866715199229899273

theorem tailTrace_8125748 : CollatzResearch.WordTrace tailWord_8125748 prefixEnd_8125748 154533866715199229899273 := by
  unfold tailWord_8125748
  simp only [CollatzResearch.WordTrace]
  refine ⟨148185188682905119058856949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197580251577206825411809265 148185188682905119058856949)
  ·
    refine ⟨13892361439022354911767839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148185188682905119058856949 13892361439022354911767839)
    ·
      refine ⟨20838542158533532367651759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13892361439022354911767839 20838542158533532367651759)
      ·
        refine ⟨31257813237800298551477639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20838542158533532367651759 31257813237800298551477639)
        ·
          refine ⟨46886719856700447827216459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31257813237800298551477639 46886719856700447827216459)
          ·
            refine ⟨70330079785050671740824689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46886719856700447827216459 70330079785050671740824689)
            ·
              refine ⟨52747559838788003805618517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70330079785050671740824689 52747559838788003805618517)
              ·
                refine ⟨154533866715199229899273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52747559838788003805618517 154533866715199229899273)
                ·
                  rfl

theorem cell23_8125748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 10].length) (baseStart_8125748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8125748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8125748 prefixEnd_8125748 := by exact prefixLift 8125748
  have htrace : WordTrace (prefixWord ++ tailWord_8125748) baseStart_8125748 baseEnd_8125748 := by
    simpa [prefixWord, tailWord_8125748, baseEnd_8125748] using wordTrace_append hprefix tailTrace_8125748
  have hstable : (prefixWord ++ tailWord_8125748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8125748).length < 2 ^ (prefixWord ++ tailWord_8125748).sum := by decide
  have hdescent : baseEnd_8125748 < baseStart_8125748 := by decide
  rcases family_descends (prefixWord ++ tailWord_8125748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
