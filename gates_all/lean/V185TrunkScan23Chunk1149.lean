import V185TrunkScan23Chunk1148

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6805433 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 3, 7]
def baseStart_6805433 : Nat := 118140960795 + 6805433 * 2 ^ 59
def prefixEnd_6805433 : Nat := 4983230072969 + 3 ^ 40 * 6805433 * 2
def baseEnd_6805433 : Nat := 1164819396989792481929963

theorem tailTrace_6805433 : CollatzResearch.WordTrace tailWord_6805433 prefixEnd_6805433 1164819396989792481929963 := by
  unfold tailWord_6805433
  simp only [CollatzResearch.WordTrace]
  refine ⟨248214533154085991268036953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165476355436057327512024635 248214533154085991268036953)
  ·
    refine ⟨186160899865564493451027715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248214533154085991268036953 186160899865564493451027715)
    ·
      refine ⟨279241349798346740176541573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186160899865564493451027715 279241349798346740176541573)
      ·
        refine ⟨52357753087190013783101545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279241349798346740176541573 52357753087190013783101545)
        ·
          refine ⟨39268314815392510337326159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52357753087190013783101545 39268314815392510337326159)
          ·
            refine ⟨58902472223088765505989239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39268314815392510337326159 58902472223088765505989239)
            ·
              refine ⟨88353708334633148258983859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58902472223088765505989239 88353708334633148258983859)
              ·
                refine ⟨132530562501949722388475789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88353708334633148258983859 132530562501949722388475789)
                ·
                  refine ⟨49698960938231145895678421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132530562501949722388475789 49698960938231145895678421)
                  ·
                    refine ⟨1164819396989792481929963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49698960938231145895678421 1164819396989792481929963)
                    ·
                      rfl

theorem cell23_6805433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 7].length) (baseStart_6805433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805433 prefixEnd_6805433 := by exact prefixLift 6805433
  have htrace : WordTrace (prefixWord ++ tailWord_6805433) baseStart_6805433 baseEnd_6805433 := by
    simpa [prefixWord, tailWord_6805433, baseEnd_6805433] using wordTrace_append hprefix tailTrace_6805433
  have hstable : (prefixWord ++ tailWord_6805433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805433).length < 2 ^ (prefixWord ++ tailWord_6805433).sum := by decide
  have hdescent : baseEnd_6805433 < baseStart_6805433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805460 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_6805460 : Nat := 118140960795 + 6805460 * 2 ^ 59
def prefixEnd_6805460 : Nat := 4983230072969 + 3 ^ 40 * 6805460 * 2
def baseEnd_6805460 : Nat := 3494472054947048840152265

theorem tailTrace_6805460 : CollatzResearch.WordTrace tailWord_6805460 prefixEnd_6805460 3494472054947048840152265 := by
  unfold tailWord_6805460
  simp only [CollatzResearch.WordTrace]
  refine ⟨124107758962494087439634917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165477011949992116586179889 124107758962494087439634917)
  ·
    refine ⟨23270204805467641394931547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124107758962494087439634917 23270204805467641394931547)
    ·
      refine ⟨34905307208201462092397321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23270204805467641394931547 34905307208201462092397321)
      ·
        refine ⟨26178980406151096569297991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34905307208201462092397321 26178980406151096569297991)
        ·
          refine ⟨39268470609226644853946987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26178980406151096569297991 39268470609226644853946987)
          ·
            refine ⟨58902705913839967280920481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39268470609226644853946987 58902705913839967280920481)
            ·
              refine ⟨44177029435379975460690361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58902705913839967280920481 44177029435379975460690361)
              ·
                refine ⟨33132772076534981595517771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44177029435379975460690361 33132772076534981595517771)
                ·
                  refine ⟨49699158114802472393276657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33132772076534981595517771 49699158114802472393276657)
                  ·
                    refine ⟨37274368586101854294957493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49699158114802472393276657 37274368586101854294957493)
                    ·
                      refine ⟨3494472054947048840152265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37274368586101854294957493 3494472054947048840152265)
                      ·
                        rfl

theorem cell23_6805460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_6805460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805460 prefixEnd_6805460 := by exact prefixLift 6805460
  have htrace : WordTrace (prefixWord ++ tailWord_6805460) baseStart_6805460 baseEnd_6805460 := by
    simpa [prefixWord, tailWord_6805460, baseEnd_6805460] using wordTrace_append hprefix tailTrace_6805460
  have hstable : (prefixWord ++ tailWord_6805460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805460).length < 2 ^ (prefixWord ++ tailWord_6805460).sum := by decide
  have hdescent : baseEnd_6805460 < baseStart_6805460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805483 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 6]
def baseStart_6805483 : Nat := 118140960795 + 6805483 * 2 ^ 59
def prefixEnd_6805483 : Nat := 4983230072969 + 3 ^ 40 * 6805483 * 2
def baseEnd_6805483 : Nat := 3494483865002102250164659

theorem tailTrace_6805483 : CollatzResearch.WordTrace tailWord_6805483 prefixEnd_6805483 3494483865002102250164659 := by
  unfold tailWord_6805483
  simp only [CollatzResearch.WordTrace]
  refine ⟨248216356803904849807357103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165477571202603233204904735 248216356803904849807357103)
  ·
    refine ⟨372324535205857274711035655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248216356803904849807357103 372324535205857274711035655)
    ·
      refine ⟨558486802808785912066553483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372324535205857274711035655 558486802808785912066553483)
      ·
        refine ⟨837730204213178868099830225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558486802808785912066553483 837730204213178868099830225)
        ·
          refine ⟨628297653159884151074872669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 837730204213178868099830225 628297653159884151074872669)
          ·
            refine ⟨235611619934956556653077251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 628297653159884151074872669 235611619934956556653077251)
            ·
              refine ⟨353417429902434834979615877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235611619934956556653077251 353417429902434834979615877)
              ·
                refine ⟨66265768106706531558677977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 353417429902434834979615877 66265768106706531558677977)
                ·
                  refine ⟨49699326080029898669008483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66265768106706531558677977 49699326080029898669008483)
                  ·
                    refine ⟨74548989120044848003512725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49699326080029898669008483 74548989120044848003512725)
                    ·
                      refine ⟨3494483865002102250164659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74548989120044848003512725 3494483865002102250164659)
                      ·
                        rfl

theorem cell23_6805483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 6].length) (baseStart_6805483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805483 prefixEnd_6805483 := by exact prefixLift 6805483
  have htrace : WordTrace (prefixWord ++ tailWord_6805483) baseStart_6805483 baseEnd_6805483 := by
    simpa [prefixWord, tailWord_6805483, baseEnd_6805483] using wordTrace_append hprefix tailTrace_6805483
  have hstable : (prefixWord ++ tailWord_6805483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805483).length < 2 ^ (prefixWord ++ tailWord_6805483).sum := by decide
  have hdescent : baseEnd_6805483 < baseStart_6805483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805513 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 8]
def baseStart_6805513 : Nat := 118140960795 + 6805513 * 2 ^ 59
def prefixEnd_6805513 : Nat := 4983230072969 + 3 ^ 40 * 6805513 * 2
def baseEnd_6805513 : Nat := 3494499269421737132789521

theorem tailTrace_6805513 : CollatzResearch.WordTrace tailWord_6805513 prefixEnd_6805513 3494499269421737132789521 := by
  unfold tailWord_6805513
  simp only [CollatzResearch.WordTrace]
  refine ⟨248217450993796164930949193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165478300662530776620632795 248217450993796164930949193)
  ·
    refine ⟨186163088245347123698211895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248217450993796164930949193 186163088245347123698211895)
    ·
      refine ⟨279244632368020685547317843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186163088245347123698211895 279244632368020685547317843)
      ·
        refine ⟨418866948552031028320976765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279244632368020685547317843 418866948552031028320976765)
        ·
          refine ⟨157075105707011635620366287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418866948552031028320976765 157075105707011635620366287)
          ·
            refine ⟨235612658560517453430549431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157075105707011635620366287 235612658560517453430549431)
            ·
              refine ⟨353418987840776180145824147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235612658560517453430549431 353418987840776180145824147)
              ·
                refine ⟨530128481761164270218736221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353418987840776180145824147 530128481761164270218736221)
                ·
                  refine ⟨198798180660436601332026083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 530128481761164270218736221 198798180660436601332026083)
                  ·
                    refine ⟨298197270990654901998039125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198798180660436601332026083 298197270990654901998039125)
                    ·
                      refine ⟨3494499269421737132789521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 298197270990654901998039125 3494499269421737132789521)
                      ·
                        rfl

theorem cell23_6805513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_6805513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805513 prefixEnd_6805513 := by exact prefixLift 6805513
  have htrace : WordTrace (prefixWord ++ tailWord_6805513) baseStart_6805513 baseEnd_6805513 := by
    simpa [prefixWord, tailWord_6805513, baseEnd_6805513] using wordTrace_append hprefix tailTrace_6805513
  have hstable : (prefixWord ++ tailWord_6805513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805513).length < 2 ^ (prefixWord ++ tailWord_6805513).sum := by decide
  have hdescent : baseEnd_6805513 < baseStart_6805513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805554 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3]
def baseStart_6805554 : Nat := 118140960795 + 6805554 * 2 ^ 59
def prefixEnd_6805554 : Nat := 4983230072969 + 3 ^ 40 * 6805554 * 2
def baseEnd_6805554 : Nat := 3494520322128571472376833

theorem tailTrace_6805554 : CollatzResearch.WordTrace tailWord_6805554 prefixEnd_6805554 3494520322128571472376833 := by
  unfold tailWord_6805554
  simp only [CollatzResearch.WordTrace]
  refine ⟨62054736596661907233297929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165479297591098419288794477 62054736596661907233297929)
  ·
    refine ⟨46541052447496430424973447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62054736596661907233297929 46541052447496430424973447)
    ·
      refine ⟨69811578671244645637460171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46541052447496430424973447 69811578671244645637460171)
      ·
        refine ⟨104717368006866968456190257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69811578671244645637460171 104717368006866968456190257)
        ·
          refine ⟨78538026005150226342142693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104717368006866968456190257 78538026005150226342142693)
          ·
            refine ⟨14725879875965667439151755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78538026005150226342142693 14725879875965667439151755)
            ·
              refine ⟨22088819813948501158727633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14725879875965667439151755 22088819813948501158727633)
              ·
                refine ⟨16566614860461375869045725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22088819813948501158727633 16566614860461375869045725)
                ·
                  refine ⟨6212480572673015950892147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16566614860461375869045725 6212480572673015950892147)
                  ·
                    refine ⟨9318720859009523926338221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6212480572673015950892147 9318720859009523926338221)
                    ·
                      refine ⟨3494520322128571472376833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9318720859009523926338221 3494520322128571472376833)
                      ·
                        rfl

theorem cell23_6805554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_6805554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805554 prefixEnd_6805554 := by exact prefixLift 6805554
  have htrace : WordTrace (prefixWord ++ tailWord_6805554) baseStart_6805554 baseEnd_6805554 := by
    simpa [prefixWord, tailWord_6805554, baseEnd_6805554] using wordTrace_append hprefix tailTrace_6805554
  have hstable : (prefixWord ++ tailWord_6805554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805554).length < 2 ^ (prefixWord ++ tailWord_6805554).sum := by decide
  have hdescent : baseEnd_6805554 < baseStart_6805554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805577 : List Nat := [1, 2, 1, 1, 2, 2, 5, 3, 1, 1, 4]
def baseStart_6805577 : Nat := 118140960795 + 6805577 * 2 ^ 59
def prefixEnd_6805577 : Nat := 4983230072969 + 3 ^ 40 * 6805577 * 2
def baseEnd_6805577 : Nat := 3494532132183624882389227

theorem tailTrace_6805577 : CollatzResearch.WordTrace tailWord_6805577 prefixEnd_6805577 3494532132183624882389227 := by
  unfold tailWord_6805577
  simp only [CollatzResearch.WordTrace]
  refine ⟨248219785265564303861278985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165479856843709535907519323 248219785265564303861278985)
  ·
    refine ⟨186164838949173227895959239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248219785265564303861278985 186164838949173227895959239)
    ·
      refine ⟨279247258423759841843938859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186164838949173227895959239 279247258423759841843938859)
      ·
        refine ⟨418870887635639762765908289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279247258423759841843938859 418870887635639762765908289)
        ·
          refine ⟨314153165726729822074431217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418870887635639762765908289 314153165726729822074431217)
          ·
            refine ⟨235614874295047366555823413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314153165726729822074431217 235614874295047366555823413)
            ·
              refine ⟨22088894465160690614608445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235614874295047366555823413 22088894465160690614608445)
              ·
                refine ⟨8283335424435258980478167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22088894465160690614608445 8283335424435258980478167)
                ·
                  refine ⟨12425003136652888470717251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8283335424435258980478167 12425003136652888470717251)
                  ·
                    refine ⟨18637504704979332706075877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12425003136652888470717251 18637504704979332706075877)
                    ·
                      refine ⟨3494532132183624882389227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18637504704979332706075877 3494532132183624882389227)
                      ·
                        rfl

theorem cell23_6805577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 1, 4].length) (baseStart_6805577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805577 prefixEnd_6805577 := by exact prefixLift 6805577
  have htrace : WordTrace (prefixWord ++ tailWord_6805577) baseStart_6805577 baseEnd_6805577 := by
    simpa [prefixWord, tailWord_6805577, baseEnd_6805577] using wordTrace_append hprefix tailTrace_6805577
  have hstable : (prefixWord ++ tailWord_6805577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805577).length < 2 ^ (prefixWord ++ tailWord_6805577).sum := by decide
  have hdescent : baseEnd_6805577 < baseStart_6805577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805628 : List Nat := [2, 2, 2, 1, 1, 4, 3, 3, 1, 2, 2]
def baseStart_6805628 : Nat := 118140960795 + 6805628 * 2 ^ 59
def prefixEnd_6805628 : Nat := 4983230072969 + 3 ^ 40 * 6805628 * 2
def baseEnd_6805628 : Nat := 3494558319697004182851493

theorem tailTrace_6805628 : CollatzResearch.WordTrace tailWord_6805628 prefixEnd_6805628 3494558319697004182851493 := by
  unfold tailWord_6805628
  simp only [CollatzResearch.WordTrace]
  refine ⟨124110822694189769785692769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165481096925586359714257025 124110822694189769785692769)
  ·
    refine ⟨93083117020642327339269577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124110822694189769785692769 93083117020642327339269577)
    ·
      refine ⟨69812337765481745504452183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93083117020642327339269577 69812337765481745504452183)
      ·
        refine ⟨104718506648222618256678275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69812337765481745504452183 104718506648222618256678275)
        ·
          refine ⟨157077759972333927385017413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104718506648222618256678275 157077759972333927385017413)
          ·
            refine ⟨29452079994812611384690765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157077759972333927385017413 29452079994812611384690765)
            ·
              refine ⟨11044529998054729269259037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29452079994812611384690765 11044529998054729269259037)
              ·
                refine ⟨4141698749270523475972139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11044529998054729269259037 4141698749270523475972139)
                ·
                  refine ⟨6212548123905785213958209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4141698749270523475972139 6212548123905785213958209)
                  ·
                    refine ⟨4659411092929338910468657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6212548123905785213958209 4659411092929338910468657)
                    ·
                      refine ⟨3494558319697004182851493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4659411092929338910468657 3494558319697004182851493)
                      ·
                        rfl

theorem cell23_6805628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_6805628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805628 prefixEnd_6805628 := by exact prefixLift 6805628
  have htrace : WordTrace (prefixWord ++ tailWord_6805628) baseStart_6805628 baseEnd_6805628 := by
    simpa [prefixWord, tailWord_6805628, baseEnd_6805628] using wordTrace_append hprefix tailTrace_6805628
  have hstable : (prefixWord ++ tailWord_6805628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805628).length < 2 ^ (prefixWord ++ tailWord_6805628).sum := by decide
  have hdescent : baseEnd_6805628 < baseStart_6805628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805661 : List Nat := [1, 4, 2, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_6805661 : Nat := 118140960795 + 6805661 * 2 ^ 59
def prefixEnd_6805661 : Nat := 4983230072969 + 3 ^ 40 * 6805661 * 2
def baseEnd_6805661 : Nat := 3494575264558602553738841

theorem tailTrace_6805661 : CollatzResearch.WordTrace tailWord_6805661 prefixEnd_6805661 3494575264558602553738841 := by
  unfold tailWord_6805661
  simp only [CollatzResearch.WordTrace]
  refine ⟨248222848997259986207336837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165481899331506657471557891 248222848997259986207336837)
  ·
    refine ⟨46541784186986247413875657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248222848997259986207336837 46541784186986247413875657)
    ·
      refine ⟨34906338140239685560406743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46541784186986247413875657 34906338140239685560406743)
      ·
        refine ⟨52359507210359528340610115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34906338140239685560406743 52359507210359528340610115)
        ·
          refine ⟨78539260815539292510915173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52359507210359528340610115 78539260815539292510915173)
          ·
            refine ⟨14726111402913617345796595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78539260815539292510915173 14726111402913617345796595)
            ·
              refine ⟨22089167104370426018694893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14726111402913617345796595 22089167104370426018694893)
              ·
                refine ⟨8283437664138909757010585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22089167104370426018694893 8283437664138909757010585)
                ·
                  refine ⟨6212578248104182317757939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8283437664138909757010585 6212578248104182317757939)
                  ·
                    refine ⟨9318867372156273476636909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6212578248104182317757939 9318867372156273476636909)
                    ·
                      refine ⟨3494575264558602553738841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9318867372156273476636909 3494575264558602553738841)
                      ·
                        rfl

theorem cell23_6805661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_6805661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805661 prefixEnd_6805661 := by exact prefixLift 6805661
  have htrace : WordTrace (prefixWord ++ tailWord_6805661) baseStart_6805661 baseEnd_6805661 := by
    simpa [prefixWord, tailWord_6805661, baseEnd_6805661] using wordTrace_append hprefix tailTrace_6805661
  have hstable : (prefixWord ++ tailWord_6805661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805661).length < 2 ^ (prefixWord ++ tailWord_6805661).sum := by decide
  have hdescent : baseEnd_6805661 < baseStart_6805661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805678 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_6805678 : Nat := 118140960795 + 6805678 * 2 ^ 59
def prefixEnd_6805678 : Nat := 4983230072969 + 3 ^ 40 * 6805678 * 2
def baseEnd_6805678 : Nat := 3494583993729728987226263

theorem tailTrace_6805678 : CollatzResearch.WordTrace tailWord_6805678 prefixEnd_6805678 3494583993729728987226263 := by
  unfold tailWord_6805678
  simp only [CollatzResearch.WordTrace]
  refine ⟨31027933629774799763838211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165482312692132265407137125 31027933629774799763838211)
  ·
    refine ⟨46541900444662199645757317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31027933629774799763838211 46541900444662199645757317)
    ·
      refine ⟨8726606333374162433579497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46541900444662199645757317 8726606333374162433579497)
      ·
        refine ⟨6544954750030621825184623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8726606333374162433579497 6544954750030621825184623)
        ·
          refine ⟨9817432125045932737776935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6544954750030621825184623 9817432125045932737776935)
          ·
            refine ⟨14726148187568899106665403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9817432125045932737776935 14726148187568899106665403)
            ·
              refine ⟨22089222281353348659998105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14726148187568899106665403 22089222281353348659998105)
              ·
                refine ⟨16566916711015011494998579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22089222281353348659998105 16566916711015011494998579)
                ·
                  refine ⟨24850375066522517242497869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16566916711015011494998579 24850375066522517242497869)
                  ·
                    refine ⟨9318890649945943965936701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24850375066522517242497869 9318890649945943965936701)
                    ·
                      refine ⟨3494583993729728987226263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9318890649945943965936701 3494583993729728987226263)
                      ·
                        rfl

theorem cell23_6805678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_6805678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805678 prefixEnd_6805678 := by exact prefixLift 6805678
  have htrace : WordTrace (prefixWord ++ tailWord_6805678) baseStart_6805678 baseEnd_6805678 := by
    simpa [prefixWord, tailWord_6805678, baseEnd_6805678] using wordTrace_append hprefix tailTrace_6805678
  have hstable : (prefixWord ++ tailWord_6805678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805678).length < 2 ^ (prefixWord ++ tailWord_6805678).sum := by decide
  have hdescent : baseEnd_6805678 < baseStart_6805678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805687 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 5]
def baseStart_6805687 : Nat := 118140960795 + 6805687 * 2 ^ 59
def prefixEnd_6805687 : Nat := 4983230072969 + 3 ^ 40 * 6805687 * 2
def baseEnd_6805687 : Nat := 3494588615055619452013721

theorem tailTrace_6805687 : CollatzResearch.WordTrace tailWord_6805687 prefixEnd_6805687 3494588615055619452013721 := by
  unfold tailWord_6805687
  simp only [CollatzResearch.WordTrace]
  refine ⟨248223797295165792647783315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165482531530110528431855543 248223797295165792647783315)
  ·
    refine ⟨372335695942748688971674973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248223797295165792647783315 372335695942748688971674973)
    ·
      refine ⟨139625885978530758364378115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372335695942748688971674973 139625885978530758364378115)
      ·
        refine ⟨209438828967796137546567173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139625885978530758364378115 209438828967796137546567173)
        ·
          refine ⟨39269780431461775789981345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209438828967796137546567173 39269780431461775789981345)
          ·
            refine ⟨29452335323596331842486009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39269780431461775789981345 29452335323596331842486009)
            ·
              refine ⟨22089251492697248881864507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29452335323596331842486009 22089251492697248881864507)
              ·
                refine ⟨33133877239045873322796761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22089251492697248881864507 33133877239045873322796761)
                ·
                  refine ⟨24850407929284404992097571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33133877239045873322796761 24850407929284404992097571)
                  ·
                    refine ⟨37275611893926607488146357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24850407929284404992097571 37275611893926607488146357)
                    ·
                      refine ⟨3494588615055619452013721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37275611893926607488146357 3494588615055619452013721)
                      ·
                        rfl

theorem cell23_6805687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_6805687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805687 prefixEnd_6805687 := by exact prefixLift 6805687
  have htrace : WordTrace (prefixWord ++ tailWord_6805687) baseStart_6805687 baseEnd_6805687 := by
    simpa [prefixWord, tailWord_6805687, baseEnd_6805687] using wordTrace_append hprefix tailTrace_6805687
  have hstable : (prefixWord ++ tailWord_6805687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805687).length < 2 ^ (prefixWord ++ tailWord_6805687).sum := by decide
  have hdescent : baseEnd_6805687 < baseStart_6805687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805701 : List Nat := [1, 3, 1, 1, 1, 1, 5, 4, 2, 2, 2]
def baseStart_6805701 : Nat := 118140960795 + 6805701 * 2 ^ 59
def prefixEnd_6805701 : Nat := 4983230072969 + 3 ^ 40 * 6805701 * 2
def baseEnd_6805701 : Nat := 3494595803784782397238657

theorem tailTrace_6805701 : CollatzResearch.WordTrace tailWord_6805701 prefixEnd_6805701 3494595803784782397238657 := by
  unfold tailWord_6805701
  simp only [CollatzResearch.WordTrace]
  refine ⟨248224307917115073038792957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165482871944743382025861971 248224307917115073038792957)
  ·
    refine ⟨93084115468918152389547359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248224307917115073038792957 93084115468918152389547359)
    ·
      refine ⟨139626173203377228584321039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93084115468918152389547359 139626173203377228584321039)
      ·
        refine ⟨209439259805065842876481559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139626173203377228584321039 209439259805065842876481559)
        ·
          refine ⟨314158889707598764314722339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209439259805065842876481559 314158889707598764314722339)
          ·
            refine ⟨471238334561398146472083509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314158889707598764314722339 471238334561398146472083509)
            ·
              refine ⟨44178593865131076231757829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 471238334561398146472083509 44178593865131076231757829)
              ·
                refine ⟨8283486349712076793454593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44178593865131076231757829 8283486349712076793454593)
                ·
                  refine ⟨6212614762284057595090945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8283486349712076793454593 6212614762284057595090945)
                  ·
                    refine ⟨4659461071713043196318209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6212614762284057595090945 4659461071713043196318209)
                    ·
                      refine ⟨3494595803784782397238657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4659461071713043196318209 3494595803784782397238657)
                      ·
                        rfl

theorem cell23_6805701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 2, 2].length) (baseStart_6805701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805701 prefixEnd_6805701 := by exact prefixLift 6805701
  have htrace : WordTrace (prefixWord ++ tailWord_6805701) baseStart_6805701 baseEnd_6805701 := by
    simpa [prefixWord, tailWord_6805701, baseEnd_6805701] using wordTrace_append hprefix tailTrace_6805701
  have hstable : (prefixWord ++ tailWord_6805701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805701).length < 2 ^ (prefixWord ++ tailWord_6805701).sum := by decide
  have hdescent : baseEnd_6805701 < baseStart_6805701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805714 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_6805714 : Nat := 118140960795 + 6805714 * 2 ^ 59
def prefixEnd_6805714 : Nat := 4983230072969 + 3 ^ 40 * 6805714 * 2
def baseEnd_6805714 : Nat := 3494602479033290846376097

theorem tailTrace_6805714 : CollatzResearch.WordTrace tailWord_6805714 prefixEnd_6805714 3494602479033290846376097 := by
  unfold tailWord_6805714
  simp only [CollatzResearch.WordTrace]
  refine ⟨62056195516516994064754049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165483188044045317506010797 62056195516516994064754049)
  ·
    refine ⟨46542146637387745548565537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62056195516516994064754049 46542146637387745548565537)
    ·
      refine ⟨34906609978040809161424153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46542146637387745548565537 34906609978040809161424153)
      ·
        refine ⟨26179957483530606871068115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34906609978040809161424153 26179957483530606871068115)
        ·
          refine ⟨39269936225295910306602173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26179957483530606871068115 39269936225295910306602173)
          ·
            refine ⟨14726226084485966364975815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39269936225295910306602173 14726226084485966364975815)
            ·
              refine ⟨22089339126728949547463723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14726226084485966364975815 22089339126728949547463723)
              ·
                refine ⟨33134008690093424321195585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22089339126728949547463723 33134008690093424321195585)
                ·
                  refine ⟨24850506517570068240896689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33134008690093424321195585 24850506517570068240896689)
                  ·
                    refine ⟨18637879888177551180672517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24850506517570068240896689 18637879888177551180672517)
                    ·
                      refine ⟨3494602479033290846376097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18637879888177551180672517 3494602479033290846376097)
                      ·
                        rfl

theorem cell23_6805714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_6805714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805714 prefixEnd_6805714 := by exact prefixLift 6805714
  have htrace : WordTrace (prefixWord ++ tailWord_6805714) baseStart_6805714 baseEnd_6805714 := by
    simpa [prefixWord, tailWord_6805714, baseEnd_6805714] using wordTrace_append hprefix tailTrace_6805714
  have hstable : (prefixWord ++ tailWord_6805714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805714).length < 2 ^ (prefixWord ++ tailWord_6805714).sum := by decide
  have hdescent : baseEnd_6805714 < baseStart_6805714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805718 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_6805718 : Nat := 118140960795 + 6805718 * 2 ^ 59
def prefixEnd_6805718 : Nat := 4983230072969 + 3 ^ 40 * 6805718 * 2
def baseEnd_6805718 : Nat := 3494604532955908830726079

theorem tailTrace_6805718 : CollatzResearch.WordTrace tailWord_6805718 prefixEnd_6805718 3494604532955908830726079 := by
  unfold tailWord_6805718
  simp only [CollatzResearch.WordTrace]
  refine ⟨15514057997378342808885113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165483285305368989961441205 15514057997378342808885113)
  ·
    refine ⟨11635543498033757106663835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15514057997378342808885113 11635543498033757106663835)
    ·
      refine ⟨17453315247050635659995753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11635543498033757106663835 17453315247050635659995753)
      ·
        refine ⟨13089986435287976744996815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17453315247050635659995753 13089986435287976744996815)
        ·
          refine ⟨19634979652931965117495223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13089986435287976744996815 19634979652931965117495223)
          ·
            refine ⟨29452469479397947676242835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19634979652931965117495223 29452469479397947676242835)
            ·
              refine ⟨44178704219096921514364253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29452469479397947676242835 44178704219096921514364253)
              ·
                refine ⟨16567014082161345567886595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44178704219096921514364253 16567014082161345567886595)
                ·
                  refine ⟨24850521123242018351829893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16567014082161345567886595 24850521123242018351829893)
                  ·
                    refine ⟨4659472710607878440968105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24850521123242018351829893 4659472710607878440968105)
                    ·
                      refine ⟨3494604532955908830726079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4659472710607878440968105 3494604532955908830726079)
                      ·
                        rfl

theorem cell23_6805718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_6805718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805718 prefixEnd_6805718 := by exact prefixLift 6805718
  have htrace : WordTrace (prefixWord ++ tailWord_6805718) baseStart_6805718 baseEnd_6805718 := by
    simpa [prefixWord, tailWord_6805718, baseEnd_6805718] using wordTrace_append hprefix tailTrace_6805718
  have hstable : (prefixWord ++ tailWord_6805718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805718).length < 2 ^ (prefixWord ++ tailWord_6805718).sum := by decide
  have hdescent : baseEnd_6805718 < baseStart_6805718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805784 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 3, 4]
def baseStart_6805784 : Nat := 118140960795 + 6805784 * 2 ^ 59
def prefixEnd_6805784 : Nat := 4983230072969 + 3 ^ 40 * 6805784 * 2
def baseEnd_6805784 : Nat := 1164879474226368524166925

theorem tailTrace_6805784 : CollatzResearch.WordTrace tailWord_6805784 prefixEnd_6805784 1164879474226368524166925 := by
  unfold tailWord_6805784
  simp only [CollatzResearch.WordTrace]
  refine ⟨124113667587907189107032203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165484890117209585476042937 124113667587907189107032203)
  ·
    refine ⟨186170501381860783660548305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124113667587907189107032203 186170501381860783660548305)
    ·
      refine ⟨139627876036395587745411229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186170501381860783660548305 139627876036395587745411229)
      ·
        refine ⟨52360453513648345404529211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139627876036395587745411229 52360453513648345404529211)
        ·
          refine ⟨78540680270472518106793817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52360453513648345404529211 78540680270472518106793817)
          ·
            refine ⟨58905510202854388580095363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78540680270472518106793817 58905510202854388580095363)
            ·
              refine ⟨88358265304281582870143045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58905510202854388580095363 88358265304281582870143045)
              ·
                refine ⟨16567174744552796788151821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88358265304281582870143045 16567174744552796788151821)
                ·
                  refine ⟨6212690529207298795556933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16567174744552796788151821 6212690529207298795556933)
                  ·
                    refine ⟨1164879474226368524166925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6212690529207298795556933 1164879474226368524166925)
                    ·
                      rfl

theorem cell23_6805784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_6805784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805784 prefixEnd_6805784 := by exact prefixLift 6805784
  have htrace : WordTrace (prefixWord ++ tailWord_6805784) baseStart_6805784 baseEnd_6805784 := by
    simpa [prefixWord, tailWord_6805784, baseEnd_6805784] using wordTrace_append hprefix tailTrace_6805784
  have hstable : (prefixWord ++ tailWord_6805784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805784).length < 2 ^ (prefixWord ++ tailWord_6805784).sum := by decide
  have hdescent : baseEnd_6805784 < baseStart_6805784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805891 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 1, 6]
def baseStart_6805891 : Nat := 118140960795 + 6805891 * 2 ^ 59
def prefixEnd_6805891 : Nat := 4983230072969 + 3 ^ 40 * 6805891 * 2
def baseEnd_6805891 : Nat := 1164897788369712217954261

theorem tailTrace_6805891 : CollatzResearch.WordTrace tailWord_6805891 prefixEnd_6805891 1164897788369712217954261 := by
  unfold tailWord_6805891
  simp only [CollatzResearch.WordTrace]
  refine ⟨248231237786426735488209527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165487491857617823658806351 248231237786426735488209527)
  ·
    refine ⟨372346856679640103232314291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248231237786426735488209527 372346856679640103232314291)
    ·
      refine ⟨558520285019460154848471437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372346856679640103232314291 558520285019460154848471437)
      ·
        refine ⟨209445106882297558068176789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 558520285019460154848471437 209445106882297558068176789)
        ·
          refine ⟨9817739385107698034445787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 209445106882297558068176789 9817739385107698034445787)
          ·
            refine ⟨14726609077661547051668681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9817739385107698034445787 14726609077661547051668681)
            ·
              refine ⟨11044956808246160288751511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14726609077661547051668681 11044956808246160288751511)
              ·
                refine ⟨16567435212369240433127267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11044956808246160288751511 16567435212369240433127267)
                ·
                  refine ⟨24851152818553860649690901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16567435212369240433127267 24851152818553860649690901)
                  ·
                    refine ⟨1164897788369712217954261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24851152818553860649690901 1164897788369712217954261)
                    ·
                      rfl

theorem cell23_6805891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 6].length) (baseStart_6805891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805891 prefixEnd_6805891 := by exact prefixLift 6805891
  have htrace : WordTrace (prefixWord ++ tailWord_6805891) baseStart_6805891 baseEnd_6805891 := by
    simpa [prefixWord, tailWord_6805891, baseEnd_6805891] using wordTrace_append hprefix tailTrace_6805891
  have hstable : (prefixWord ++ tailWord_6805891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805891).length < 2 ^ (prefixWord ++ tailWord_6805891).sum := by decide
  have hdescent : baseEnd_6805891 < baseStart_6805891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805921 : List Nat := [1, 2, 3, 5, 1, 1, 10]
def baseStart_6805921 : Nat := 118140960795 + 6805921 * 2 ^ 59
def prefixEnd_6805921 : Nat := 4983230072969 + 3 ^ 40 * 6805921 * 2
def baseEnd_6805921 : Nat := 43144552710231747364045

theorem tailTrace_6805921 : CollatzResearch.WordTrace tailWord_6805921 prefixEnd_6805921 43144552710231747364045 := by
  unfold tailWord_6805921
  simp only [CollatzResearch.WordTrace]
  refine ⟨248232331976318050611801617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165488221317545367074534411 248232331976318050611801617)
  ·
    refine ⟨186174248982238537958851213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248232331976318050611801617 186174248982238537958851213)
    ·
      refine ⟨69815343368339451734569205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186174248982238537958851213 69815343368339451734569205)
      ·
        refine ⟨6545188440781823600115863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69815343368339451734569205 6545188440781823600115863)
        ·
          refine ⟨9817782661172735400173795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6545188440781823600115863 9817782661172735400173795)
          ·
            refine ⟨14726673991759103100260693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9817782661172735400173795 14726673991759103100260693)
            ·
              refine ⟨43144552710231747364045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14726673991759103100260693 43144552710231747364045)
              ·
                rfl

theorem cell23_6805921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 10].length) (baseStart_6805921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805921 prefixEnd_6805921 := by exact prefixLift 6805921
  have htrace : WordTrace (prefixWord ++ tailWord_6805921) baseStart_6805921 baseEnd_6805921 := by
    simpa [prefixWord, tailWord_6805921, baseEnd_6805921] using wordTrace_append hprefix tailTrace_6805921
  have hstable : (prefixWord ++ tailWord_6805921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805921).length < 2 ^ (prefixWord ++ tailWord_6805921).sum := by decide
  have hdescent : baseEnd_6805921 < baseStart_6805921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805948 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 1, 3, 3]
def baseStart_6805948 : Nat := 118140960795 + 6805948 * 2 ^ 59
def prefixEnd_6805948 : Nat := 4983230072969 + 3 ^ 40 * 6805948 * 2
def baseEnd_6805948 : Nat := 3494722633506442930850021

theorem tailTrace_6805948 : CollatzResearch.WordTrace tailWord_6805948 prefixEnd_6805948 3494722633506442930850021 := by
  unfold tailWord_6805948
  simp only [CollatzResearch.WordTrace]
  refine ⟨124116658373610117111517249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165488877831480156148689665 124116658373610117111517249)
  ·
    refine ⟨93087493780207587833637937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124116658373610117111517249 93087493780207587833637937)
    ·
      refine ⟨69815620335155690875228453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93087493780207587833637937 69815620335155690875228453)
      ·
        refine ⟨13090428812841692039105335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69815620335155690875228453 13090428812841692039105335)
        ·
          refine ⟨19635643219262538058658003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13090428812841692039105335 19635643219262538058658003)
          ·
            refine ⟨29453464828893807087987005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19635643219262538058658003 29453464828893807087987005)
            ·
              refine ⟨11045049310835177657995127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29453464828893807087987005 11045049310835177657995127)
              ·
                refine ⟨16567573966252766486992691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11045049310835177657995127 16567573966252766486992691)
                ·
                  refine ⟨24851360949379149730489037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16567573966252766486992691 24851360949379149730489037)
                  ·
                    refine ⟨9319260356017181148933389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24851360949379149730489037 9319260356017181148933389)
                    ·
                      refine ⟨3494722633506442930850021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9319260356017181148933389 3494722633506442930850021)
                      ·
                        rfl

theorem cell23_6805948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_6805948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805948 prefixEnd_6805948 := by exact prefixLift 6805948
  have htrace : WordTrace (prefixWord ++ tailWord_6805948) baseStart_6805948 baseEnd_6805948 := by
    simpa [prefixWord, tailWord_6805948, baseEnd_6805948] using wordTrace_append hprefix tailTrace_6805948
  have hstable : (prefixWord ++ tailWord_6805948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805948).length < 2 ^ (prefixWord ++ tailWord_6805948).sum := by decide
  have hdescent : baseEnd_6805948 < baseStart_6805948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6805991 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_6805991 : Nat := 118140960795 + 6805991 * 2 ^ 59
def prefixEnd_6805991 : Nat := 4983230072969 + 3 ^ 40 * 6805991 * 2
def baseEnd_6805991 : Nat := 3494744713174586262612323

theorem tailTrace_6805991 : CollatzResearch.WordTrace tailWord_6805991 prefixEnd_6805991 3494744713174586262612323 := by
  unfold tailWord_6805991
  simp only [CollatzResearch.WordTrace]
  refine ⟨248234885086064452566849827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165489923390709635044566551 248234885086064452566849827)
  ·
    refine ⟨372352327629096678850274741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248234885086064452566849827 372352327629096678850274741)
    ·
      refine ⟨34908030715227813642213257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 372352327629096678850274741 34908030715227813642213257)
      ·
        refine ⟨26181023036420860231659943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34908030715227813642213257 26181023036420860231659943)
        ·
          refine ⟨39271534554631290347489915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26181023036420860231659943 39271534554631290347489915)
          ·
            refine ⟨58907301831946935521234873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39271534554631290347489915 58907301831946935521234873)
            ·
              refine ⟨44180476373960201640926155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58907301831946935521234873 44180476373960201640926155)
              ·
                refine ⟨66270714560940302461389233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44180476373960201640926155 66270714560940302461389233)
                ·
                  refine ⟨49703035920705226846041925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66270714560940302461389233 49703035920705226846041925)
                  ·
                    refine ⟨9319319235132230033632861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49703035920705226846041925 9319319235132230033632861)
                    ·
                      refine ⟨3494744713174586262612323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9319319235132230033632861 3494744713174586262612323)
                      ·
                        rfl

theorem cell23_6805991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_6805991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6805991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6805991 prefixEnd_6805991 := by exact prefixLift 6805991
  have htrace : WordTrace (prefixWord ++ tailWord_6805991) baseStart_6805991 baseEnd_6805991 := by
    simpa [prefixWord, tailWord_6805991, baseEnd_6805991] using wordTrace_append hprefix tailTrace_6805991
  have hstable : (prefixWord ++ tailWord_6805991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6805991).length < 2 ^ (prefixWord ++ tailWord_6805991).sum := by decide
  have hdescent : baseEnd_6805991 < baseStart_6805991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6805991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806031 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 1, 7, 2]
def baseStart_6806031 : Nat := 118140960795 + 6806031 * 2 ^ 59
def prefixEnd_6806031 : Nat := 4983230072969 + 3 ^ 40 * 6806031 * 2
def baseEnd_6806031 : Nat := 3494765252400766106112139

theorem tailTrace_6806031 : CollatzResearch.WordTrace tailWord_6806031 prefixEnd_6806031 3494765252400766106112139 := by
  unfold tailWord_6806031
  simp only [CollatzResearch.WordTrace]
  refine ⟨248236344005919539398305947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165490896003946359598870631 248236344005919539398305947)
  ·
    refine ⟨372354516008879309097458921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248236344005919539398305947 372354516008879309097458921)
    ·
      refine ⟨279265887006659481823094191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372354516008879309097458921 279265887006659481823094191)
      ·
        refine ⟨418898830509989222734641287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279265887006659481823094191 418898830509989222734641287)
        ·
          refine ⟨628348245764983834101961931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418898830509989222734641287 628348245764983834101961931)
          ·
            refine ⟨942522368647475751152942897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628348245764983834101961931 942522368647475751152942897)
            ·
              refine ⟨706891776485606813364707173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 942522368647475751152942897 706891776485606813364707173)
              ·
                refine ⟨132542208091051277505882595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 706891776485606813364707173 132542208091051277505882595)
                ·
                  refine ⟨198813312136576916258823893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132542208091051277505882595 198813312136576916258823893)
                  ·
                    refine ⟨4659687003201021474816185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 198813312136576916258823893 4659687003201021474816185)
                    ·
                      refine ⟨3494765252400766106112139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4659687003201021474816185 3494765252400766106112139)
                      ·
                        rfl

theorem cell23_6806031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 7, 2].length) (baseStart_6806031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806031 prefixEnd_6806031 := by exact prefixLift 6806031
  have htrace : WordTrace (prefixWord ++ tailWord_6806031) baseStart_6806031 baseEnd_6806031 := by
    simpa [prefixWord, tailWord_6806031, baseEnd_6806031] using wordTrace_append hprefix tailTrace_6806031
  have hstable : (prefixWord ++ tailWord_6806031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806031).length < 2 ^ (prefixWord ++ tailWord_6806031).sum := by decide
  have hdescent : baseEnd_6806031 < baseStart_6806031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806039 : List Nat := [1, 1, 3, 6, 1, 1, 2, 2, 2, 2, 2]
def baseStart_6806039 : Nat := 118140960795 + 6806039 * 2 ^ 59
def prefixEnd_6806039 : Nat := 4983230072969 + 3 ^ 40 * 6806039 * 2
def baseEnd_6806039 : Nat := 3494769360246002074812103

theorem tailTrace_6806039 : CollatzResearch.WordTrace tailWord_6806039 prefixEnd_6806039 3494769360246002074812103 := by
  unfold tailWord_6806039
  simp only [CollatzResearch.WordTrace]
  refine ⟨248236635789890556764597171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165491090526593704509731447 248236635789890556764597171)
  ·
    refine ⟨372354953684835835146895757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248236635789890556764597171 372354953684835835146895757)
    ·
      refine ⟨139633107631813438180085909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372354953684835835146895757 139633107631813438180085909)
      ·
        refine ⟨6545301920241254914691527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139633107631813438180085909 6545301920241254914691527)
        ·
          refine ⟨9817952880361882372037291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6545301920241254914691527 9817952880361882372037291)
          ·
            refine ⟨14726929320542823558055937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9817952880361882372037291 14726929320542823558055937)
            ·
              refine ⟨11045196990407117668541953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14726929320542823558055937 11045196990407117668541953)
              ·
                refine ⟨8283897742805338251406465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11045196990407117668541953 8283897742805338251406465)
                ·
                  refine ⟨6212923307104003688554849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8283897742805338251406465 6212923307104003688554849)
                  ·
                    refine ⟨4659692480328002766416137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6212923307104003688554849 4659692480328002766416137)
                    ·
                      refine ⟨3494769360246002074812103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4659692480328002766416137 3494769360246002074812103)
                      ·
                        rfl

theorem cell23_6806039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_6806039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806039 prefixEnd_6806039 := by exact prefixLift 6806039
  have htrace : WordTrace (prefixWord ++ tailWord_6806039) baseStart_6806039 baseEnd_6806039 := by
    simpa [prefixWord, tailWord_6806039, baseEnd_6806039] using wordTrace_append hprefix tailTrace_6806039
  have hstable : (prefixWord ++ tailWord_6806039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806039).length < 2 ^ (prefixWord ++ tailWord_6806039).sum := by decide
  have hdescent : baseEnd_6806039 < baseStart_6806039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806045 : List Nat := [1, 4, 2, 2, 1, 2, 4, 2, 5]
def baseStart_6806045 : Nat := 118140960795 + 6806045 * 2 ^ 59
def prefixEnd_6806045 : Nat := 4983230072969 + 3 ^ 40 * 6806045 * 2
def baseEnd_6806045 : Nat := 388308049014436561259675

theorem tailTrace_6806045 : CollatzResearch.WordTrace tailWord_6806045 prefixEnd_6806045 388308049014436561259675 := by
  unfold tailWord_6806045
  simp only [CollatzResearch.WordTrace]
  refine ⟨248236854627868819789315589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165491236418579213192877059 248236854627868819789315589)
  ·
    refine ⟨46544410242725403710496673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248236854627868819789315589 46544410242725403710496673)
    ·
      refine ⟨34908307682044052782872505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46544410242725403710496673 34908307682044052782872505)
      ·
        refine ⟨26181230761533039587154379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34908307682044052782872505 26181230761533039587154379)
        ·
          refine ⟨39271846142299559380731569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26181230761533039587154379 39271846142299559380731569)
          ·
            refine ⟨29453884606724669535548677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39271846142299559380731569 29453884606724669535548677)
            ·
              refine ⟨5522603363760875537915377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29453884606724669535548677 5522603363760875537915377)
              ·
                refine ⟨4141952522820656653436533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5522603363760875537915377 4141952522820656653436533)
                ·
                  refine ⟨388308049014436561259675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4141952522820656653436533 388308049014436561259675)
                  ·
                    rfl

theorem cell23_6806045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_6806045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806045 prefixEnd_6806045 := by exact prefixLift 6806045
  have htrace : WordTrace (prefixWord ++ tailWord_6806045) baseStart_6806045 baseEnd_6806045 := by
    simpa [prefixWord, tailWord_6806045, baseEnd_6806045] using wordTrace_append hprefix tailTrace_6806045
  have hstable : (prefixWord ++ tailWord_6806045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806045).length < 2 ^ (prefixWord ++ tailWord_6806045).sum := by decide
  have hdescent : baseEnd_6806045 < baseStart_6806045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806051 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 5]
def baseStart_6806051 : Nat := 118140960795 + 6806051 * 2 ^ 59
def prefixEnd_6806051 : Nat := 4983230072969 + 3 ^ 40 * 6806051 * 2
def baseEnd_6806051 : Nat := 3494775522013856027862047

theorem tailTrace_6806051 : CollatzResearch.WordTrace tailWord_6806051 prefixEnd_6806051 3494775522013856027862047 := by
  unfold tailWord_6806051
  simp only [CollatzResearch.WordTrace]
  refine ⟨248237073465847082814034007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165491382310564721876022671 248237073465847082814034007)
  ·
    refine ⟨372355610198770624221051011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248237073465847082814034007 372355610198770624221051011)
    ·
      refine ⟨558533415298155936331576517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372355610198770624221051011 558533415298155936331576517)
      ·
        refine ⟨104725015368404238062170597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 558533415298155936331576517 104725015368404238062170597)
        ·
          refine ⟨19635940381575794636656987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104725015368404238062170597 19635940381575794636656987)
          ·
            refine ⟨29453910572363691954985481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19635940381575794636656987 29453910572363691954985481)
            ·
              refine ⟨22090432929272768966239111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29453910572363691954985481 22090432929272768966239111)
              ·
                refine ⟨33135649393909153449358667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22090432929272768966239111 33135649393909153449358667)
                ·
                  refine ⟨49703474090863730174038001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33135649393909153449358667 49703474090863730174038001)
                  ·
                    refine ⟨37277605568147797630528501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49703474090863730174038001 37277605568147797630528501)
                    ·
                      refine ⟨3494775522013856027862047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37277605568147797630528501 3494775522013856027862047)
                      ·
                        rfl

theorem cell23_6806051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_6806051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806051 prefixEnd_6806051 := by exact prefixLift 6806051
  have htrace : WordTrace (prefixWord ++ tailWord_6806051) baseStart_6806051 baseEnd_6806051 := by
    simpa [prefixWord, tailWord_6806051, baseEnd_6806051] using wordTrace_append hprefix tailTrace_6806051
  have hstable : (prefixWord ++ tailWord_6806051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806051).length < 2 ^ (prefixWord ++ tailWord_6806051).sum := by decide
  have hdescent : baseEnd_6806051 < baseStart_6806051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806098 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_6806098 : Nat := 118140960795 + 6806098 * 2 ^ 59
def prefixEnd_6806098 : Nat := 4983230072969 + 3 ^ 40 * 6806098 * 2
def baseEnd_6806098 : Nat := 3494799655604617343974331

theorem tailTrace_6806098 : CollatzResearch.WordTrace tailWord_6806098 prefixEnd_6806098 3494799655604617343974331 := by
  unfold tailWord_6806098
  simp only [CollatzResearch.WordTrace]
  refine ⟨62059696924169202460248737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165492525131117873227329965 62059696924169202460248737)
  ·
    refine ⟨46544772693126901845186553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62059696924169202460248737 46544772693126901845186553)
    ·
      refine ⟨34908579519845176383889915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46544772693126901845186553 34908579519845176383889915)
      ·
        refine ⟨52362869279767764575834873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34908579519845176383889915 52362869279767764575834873)
        ·
          refine ⟨39272151959825823431876155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52362869279767764575834873 39272151959825823431876155)
          ·
            refine ⟨58908227939738735147814233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39272151959825823431876155 58908227939738735147814233)
            ·
              refine ⟨44181170954804051360860675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58908227939738735147814233 44181170954804051360860675)
              ·
                refine ⟨66271756432206077041291013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44181170954804051360860675 66271756432206077041291013)
                ·
                  refine ⟨12425954331038639445242065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66271756432206077041291013 12425954331038639445242065)
                  ·
                    refine ⟨9319465748278979583931549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12425954331038639445242065 9319465748278979583931549)
                    ·
                      refine ⟨3494799655604617343974331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9319465748278979583931549 3494799655604617343974331)
                      ·
                        rfl

theorem cell23_6806098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_6806098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806098 prefixEnd_6806098 := by exact prefixLift 6806098
  have htrace : WordTrace (prefixWord ++ tailWord_6806098) baseStart_6806098 baseEnd_6806098 := by
    simpa [prefixWord, tailWord_6806098, baseEnd_6806098] using wordTrace_append hprefix tailTrace_6806098
  have hstable : (prefixWord ++ tailWord_6806098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806098).length < 2 ^ (prefixWord ++ tailWord_6806098).sum := by decide
  have hdescent : baseEnd_6806098 < baseStart_6806098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806162 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_6806162 : Nat := 118140960795 + 6806162 * 2 ^ 59
def prefixEnd_6806162 : Nat := 4983230072969 + 3 ^ 40 * 6806162 * 2
def baseEnd_6806162 : Nat := 3494832518366505093574037

theorem tailTrace_6806162 : CollatzResearch.WordTrace tailWord_6806162 prefixEnd_6806162 3494832518366505093574037 := by
  unfold tailWord_6806162
  simp only [CollatzResearch.WordTrace]
  refine ⟨62060280492111237192831185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165494081312296632514216493 62060280492111237192831185)
  ·
    refine ⟨46545210369083427894623389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62060280492111237192831185 46545210369083427894623389)
    ·
      refine ⟨17454453888406285460483771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46545210369083427894623389 17454453888406285460483771)
      ·
        refine ⟨26181680832609428190725657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17454453888406285460483771 26181680832609428190725657)
        ·
          refine ⟨19636260624457071143044243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26181680832609428190725657 19636260624457071143044243)
          ·
            refine ⟨29454390936685606714566365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19636260624457071143044243 29454390936685606714566365)
            ·
              refine ⟨11045396601257102517962387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29454390936685606714566365 11045396601257102517962387)
              ·
                refine ⟨16568094901885653776943581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11045396601257102517962387 16568094901885653776943581)
                ·
                  refine ⟨6213035588207120166353843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16568094901885653776943581 6213035588207120166353843)
                  ·
                    refine ⟨9319553382310680249530765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6213035588207120166353843 9319553382310680249530765)
                    ·
                      refine ⟨3494832518366505093574037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9319553382310680249530765 3494832518366505093574037)
                      ·
                        rfl

theorem cell23_6806162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_6806162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806162 prefixEnd_6806162 := by exact prefixLift 6806162
  have htrace : WordTrace (prefixWord ++ tailWord_6806162) baseStart_6806162 baseEnd_6806162 := by
    simpa [prefixWord, tailWord_6806162, baseEnd_6806162] using wordTrace_append hprefix tailTrace_6806162
  have hstable : (prefixWord ++ tailWord_6806162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806162).length < 2 ^ (prefixWord ++ tailWord_6806162).sum := by decide
  have hdescent : baseEnd_6806162 < baseStart_6806162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806168 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 3, 1, 4]
def baseStart_6806168 : Nat := 118140960795 + 6806168 * 2 ^ 59
def prefixEnd_6806168 : Nat := 4983230072969 + 3 ^ 40 * 6806168 * 2
def baseEnd_6806168 : Nat := 3494835599250432070099009

theorem tailTrace_6806168 : CollatzResearch.WordTrace tailWord_6806168 prefixEnd_6806168 3494835599250432070099009 := by
  unfold tailWord_6806168
  simp only [CollatzResearch.WordTrace]
  refine ⟨124120670403211605898021579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165494227204282141197362105 124120670403211605898021579)
  ·
    refine ⟨186181005604817408847032369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124120670403211605898021579 186181005604817408847032369)
    ·
      refine ⟨139635754203613056635274277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186181005604817408847032369 139635754203613056635274277)
      ·
        refine ⟨26181703913177448119113927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139635754203613056635274277 26181703913177448119113927)
        ·
          refine ⟨39272555869766172178670891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26181703913177448119113927 39272555869766172178670891)
          ·
            refine ⟨58908833804649258268006337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39272555869766172178670891 58908833804649258268006337)
            ·
              refine ⟨44181625353486943701004753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58908833804649258268006337 44181625353486943701004753)
              ·
                refine ⟨33136219015115207775753565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44181625353486943701004753 33136219015115207775753565)
                ·
                  refine ⟨12426082130668202915907587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33136219015115207775753565 12426082130668202915907587)
                  ·
                    refine ⟨18639123196002304373861381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12426082130668202915907587 18639123196002304373861381)
                    ·
                      refine ⟨3494835599250432070099009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18639123196002304373861381 3494835599250432070099009)
                      ·
                        rfl

theorem cell23_6806168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_6806168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806168 prefixEnd_6806168 := by exact prefixLift 6806168
  have htrace : WordTrace (prefixWord ++ tailWord_6806168) baseStart_6806168 baseEnd_6806168 := by
    simpa [prefixWord, tailWord_6806168, baseEnd_6806168] using wordTrace_append hprefix tailTrace_6806168
  have hstable : (prefixWord ++ tailWord_6806168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806168).length < 2 ^ (prefixWord ++ tailWord_6806168).sum := by decide
  have hdescent : baseEnd_6806168 < baseStart_6806168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806191 : List Nat := [1, 1, 2, 1, 2, 5, 2, 9]
def baseStart_6806191 : Nat := 118140960795 + 6806191 * 2 ^ 59
def prefixEnd_6806191 : Nat := 4983230072969 + 3 ^ 40 * 6806191 * 2
def baseEnd_6806191 : Nat := 129438792937240202967089

theorem tailTrace_6806191 : CollatzResearch.WordTrace tailWord_6806191 prefixEnd_6806191 129438792937240202967089 := by
  unfold tailWord_6806191
  simp only [CollatzResearch.WordTrace]
  refine ⟨248242179685339886724130427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165494786456893257816086951 248242179685339886724130427)
  ·
    refine ⟨372363269528009830086195641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248242179685339886724130427 372363269528009830086195641)
    ·
      refine ⟨279272452146007372564646731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372363269528009830086195641 279272452146007372564646731)
      ·
        refine ⟨418908678219011058846970097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279272452146007372564646731 418908678219011058846970097)
        ·
          refine ⟨314181508664258294135227573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418908678219011058846970097 314181508664258294135227573)
          ·
            refine ⟨29454516437274215075177585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 314181508664258294135227573 29454516437274215075177585)
            ·
              refine ⟨22090887327955661306383189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29454516437274215075177585 22090887327955661306383189)
              ·
                refine ⟨129438792937240202967089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22090887327955661306383189 129438792937240202967089)
                ·
                  rfl

theorem cell23_6806191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 9].length) (baseStart_6806191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806191 prefixEnd_6806191 := by exact prefixLift 6806191
  have htrace : WordTrace (prefixWord ++ tailWord_6806191) baseStart_6806191 baseEnd_6806191 := by
    simpa [prefixWord, tailWord_6806191, baseEnd_6806191] using wordTrace_append hprefix tailTrace_6806191
  have hstable : (prefixWord ++ tailWord_6806191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806191).length < 2 ^ (prefixWord ++ tailWord_6806191).sum := by decide
  have hdescent : baseEnd_6806191 < baseStart_6806191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806205 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 1, 1, 5]
def baseStart_6806205 : Nat := 118140960795 + 6806205 * 2 ^ 59
def prefixEnd_6806205 : Nat := 4983230072969 + 3 ^ 40 * 6806205 * 2
def baseEnd_6806205 : Nat := 3494854598034648425336339

theorem tailTrace_6806205 : CollatzResearch.WordTrace tailWord_6806205 prefixEnd_6806205 3494854598034648425336339 := by
  unfold tailWord_6806205
  simp only [CollatzResearch.WordTrace]
  refine ⟨248242690307289167115140069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165495126871526111410093379 248242690307289167115140069)
  ·
    refine ⟨46545504432616718834088763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248242690307289167115140069 46545504432616718834088763)
    ·
      refine ⟨69818256648925078251133145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46545504432616718834088763 69818256648925078251133145)
      ·
        refine ⟨52363692486693808688349859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69818256648925078251133145 52363692486693808688349859)
        ·
          refine ⟨78545538730040713032524789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52363692486693808688349859 78545538730040713032524789)
          ·
            refine ⟨7363644255941316846799199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78545538730040713032524789 7363644255941316846799199)
            ·
              refine ⟨11045466383911975270198799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7363644255941316846799199 11045466383911975270198799)
              ·
                refine ⟨16568199575867962905298199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11045466383911975270198799 16568199575867962905298199)
                ·
                  refine ⟨24852299363801944357947299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16568199575867962905298199 24852299363801944357947299)
                  ·
                    refine ⟨37278449045702916536920949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24852299363801944357947299 37278449045702916536920949)
                    ·
                      refine ⟨3494854598034648425336339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37278449045702916536920949 3494854598034648425336339)
                      ·
                        rfl

theorem cell23_6806205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_6806205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806205 prefixEnd_6806205 := by exact prefixLift 6806205
  have htrace : WordTrace (prefixWord ++ tailWord_6806205) baseStart_6806205 baseEnd_6806205 := by
    simpa [prefixWord, tailWord_6806205, baseEnd_6806205] using wordTrace_append hprefix tailTrace_6806205
  have hstable : (prefixWord ++ tailWord_6806205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806205).length < 2 ^ (prefixWord ++ tailWord_6806205).sum := by decide
  have hdescent : baseEnd_6806205 < baseStart_6806205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806212 : List Nat := [2, 3, 3, 1, 1, 3, 2, 2, 2, 4]
def baseStart_6806212 : Nat := 118140960795 + 6806212 * 2 ^ 59
def prefixEnd_6806212 : Nat := 4983230072969 + 3 ^ 40 * 6806212 * 2
def baseEnd_6806212 : Nat := 1164952730799743299316269

theorem tailTrace_6806212 : CollatzResearch.WordTrace tailWord_6806212 prefixEnd_6806212 1164952730799743299316269 := by
  unfold tailWord_6806212
  simp only [CollatzResearch.WordTrace]
  refine ⟨124121472809131903655322445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165495297078842538207096593 124121472809131903655322445)
  ·
    refine ⟨46545552303424463870745917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124121472809131903655322445 46545552303424463870745917)
    ·
      refine ⟨17454582113784173951529719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46545552303424463870745917 17454582113784173951529719)
      ·
        refine ⟨26181873170676260927294579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17454582113784173951529719 26181873170676260927294579)
        ·
          refine ⟨39272809756014391390941869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26181873170676260927294579 39272809756014391390941869)
          ·
            refine ⟨14727303658505396771603201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39272809756014391390941869 14727303658505396771603201)
            ·
              refine ⟨11045477743879047578702401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14727303658505396771603201 11045477743879047578702401)
              ·
                refine ⟨8284108307909285684026801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11045477743879047578702401 8284108307909285684026801)
                ·
                  refine ⟨6213081230931964263020101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8284108307909285684026801 6213081230931964263020101)
                  ·
                    refine ⟨1164952730799743299316269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6213081230931964263020101 1164952730799743299316269)
                    ·
                      rfl

theorem cell23_6806212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_6806212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806212 prefixEnd_6806212 := by exact prefixLift 6806212
  have htrace : WordTrace (prefixWord ++ tailWord_6806212) baseStart_6806212 baseEnd_6806212 := by
    simpa [prefixWord, tailWord_6806212, baseEnd_6806212] using wordTrace_append hprefix tailTrace_6806212
  have hstable : (prefixWord ++ tailWord_6806212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806212).length < 2 ^ (prefixWord ++ tailWord_6806212).sum := by decide
  have hdescent : baseEnd_6806212 < baseStart_6806212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806251 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 3, 8]
def baseStart_6806251 : Nat := 118140960795 + 6806251 * 2 ^ 59
def prefixEnd_6806251 : Nat := 4983230072969 + 3 ^ 40 * 6806251 * 2
def baseEnd_6806251 : Nat := 1164959406048251748453709

theorem tailTrace_6806251 : CollatzResearch.WordTrace tailWord_6806251 prefixEnd_6806251 1164959406048251748453709 := by
  unfold tailWord_6806251
  simp only [CollatzResearch.WordTrace]
  refine ⟨248244368065122516971314607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165496245376748344647543071 248244368065122516971314607)
  ·
    refine ⟨372366552097683775456971911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248244368065122516971314607 372366552097683775456971911)
    ·
      refine ⟨558549828146525663185457867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372366552097683775456971911 558549828146525663185457867)
      ·
        refine ⟨837824742219788494778186801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558549828146525663185457867 837824742219788494778186801)
        ·
          refine ⟨628368556664841371083640101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 837824742219788494778186801 628368556664841371083640101)
          ·
            refine ⟨117819104374657757078182519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 628368556664841371083640101 117819104374657757078182519)
            ·
              refine ⟨176728656561986635617273779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117819104374657757078182519 176728656561986635617273779)
              ·
                refine ⟨265092984842979953425910669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176728656561986635617273779 265092984842979953425910669)
                ·
                  refine ⟨99409869316117482534716501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265092984842979953425910669 99409869316117482534716501)
                  ·
                    refine ⟨1164959406048251748453709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99409869316117482534716501 1164959406048251748453709)
                    ·
                      rfl

theorem cell23_6806251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 8].length) (baseStart_6806251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806251 prefixEnd_6806251 := by exact prefixLift 6806251
  have htrace : WordTrace (prefixWord ++ tailWord_6806251) baseStart_6806251 baseEnd_6806251 := by
    simpa [prefixWord, tailWord_6806251, baseEnd_6806251] using wordTrace_append hprefix tailTrace_6806251
  have hstable : (prefixWord ++ tailWord_6806251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806251).length < 2 ^ (prefixWord ++ tailWord_6806251).sum := by decide
  have hdescent : baseEnd_6806251 < baseStart_6806251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806268 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 2, 6]
def baseStart_6806268 : Nat := 118140960795 + 6806268 * 2 ^ 59
def prefixEnd_6806268 : Nat := 4983230072969 + 3 ^ 40 * 6806268 * 2
def baseEnd_6806268 : Nat := 1164962315771960559616183

theorem tailTrace_6806268 : CollatzResearch.WordTrace tailWord_6806268 prefixEnd_6806268 1164962315771960559616183 := by
  unfold tailWord_6806268
  simp only [CollatzResearch.WordTrace]
  refine ⟨124122494053030464437341729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165496658737373952583122305 124122494053030464437341729)
  ·
    refine ⟨93091870539772848328006297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124122494053030464437341729 93091870539772848328006297)
    ·
      refine ⟨69818902904829636246004723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93091870539772848328006297 69818902904829636246004723)
      ·
        refine ⟨104728354357244454369007085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69818902904829636246004723 104728354357244454369007085)
        ·
          refine ⟨39273132883966670388377657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104728354357244454369007085 39273132883966670388377657)
          ·
            refine ⟨29454849662975002791283243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39273132883966670388377657 29454849662975002791283243)
            ·
              refine ⟨44182274494462504186924865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29454849662975002791283243 44182274494462504186924865)
              ·
                refine ⟨33136705870846878140193649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44182274494462504186924865 33136705870846878140193649)
                ·
                  refine ⟨24852529403135158605145237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33136705870846878140193649 24852529403135158605145237)
                  ·
                    refine ⟨1164962315771960559616183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24852529403135158605145237 1164962315771960559616183)
                    ·
                      rfl

theorem cell23_6806268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_6806268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806268 prefixEnd_6806268 := by exact prefixLift 6806268
  have htrace : WordTrace (prefixWord ++ tailWord_6806268) baseStart_6806268 baseEnd_6806268 := by
    simpa [prefixWord, tailWord_6806268, baseEnd_6806268] using wordTrace_append hprefix tailTrace_6806268
  have hstable : (prefixWord ++ tailWord_6806268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806268).length < 2 ^ (prefixWord ++ tailWord_6806268).sum := by decide
  have hdescent : baseEnd_6806268 < baseStart_6806268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806298 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 7]
def baseStart_6806298 : Nat := 118140960795 + 6806298 * 2 ^ 59
def prefixEnd_6806298 : Nat := 4983230072969 + 3 ^ 40 * 6806298 * 2
def baseEnd_6806298 : Nat := 388322483526168506830379

theorem tailTrace_6806298 : CollatzResearch.WordTrace tailWord_6806298 prefixEnd_6806298 388322483526168506830379 := by
  unfold tailWord_6806298
  simp only [CollatzResearch.WordTrace]
  refine ⟨62061520573988060999568887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165497388197301495998850365 62061520573988060999568887)
  ·
    refine ⟨93092280860982091499353331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62061520573988060999568887 93092280860982091499353331)
    ·
      refine ⟨139638421291473137249029997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93092280860982091499353331 139638421291473137249029997)
      ·
        refine ⟨52364407984302426468386249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139638421291473137249029997 52364407984302426468386249)
        ·
          refine ⟨39273305988226819851289687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52364407984302426468386249 39273305988226819851289687)
          ·
            refine ⟨58909958982340229776934531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39273305988226819851289687 58909958982340229776934531)
            ·
              refine ⟨88364938473510344665401797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58909958982340229776934531 88364938473510344665401797)
              ·
                refine ⟨16568425963783189624762837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88364938473510344665401797 16568425963783189624762837)
                ·
                  refine ⟨388322483526168506830379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16568425963783189624762837 388322483526168506830379)
                  ·
                    rfl

theorem cell23_6806298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 7].length) (baseStart_6806298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806298 prefixEnd_6806298 := by exact prefixLift 6806298
  have htrace : WordTrace (prefixWord ++ tailWord_6806298) baseStart_6806298 baseEnd_6806298 := by
    simpa [prefixWord, tailWord_6806298, baseEnd_6806298] using wordTrace_append hprefix tailTrace_6806298
  have hstable : (prefixWord ++ tailWord_6806298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806298).length < 2 ^ (prefixWord ++ tailWord_6806298).sum := by decide
  have hdescent : baseEnd_6806298 < baseStart_6806298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806405 : List Nat := [1, 3, 1, 1, 3, 3, 2, 3, 6]
def baseStart_6806405 : Nat := 118140960795 + 6806405 * 2 ^ 59
def prefixEnd_6806405 : Nat := 4983230072969 + 3 ^ 40 * 6806405 * 2
def baseEnd_6806405 : Nat := 388328588240616404759491

theorem tailTrace_6806405 : CollatzResearch.WordTrace tailWord_6806405 prefixEnd_6806405 388328588240616404759491 := by
  unfold tailWord_6806405
  simp only [CollatzResearch.WordTrace]
  refine ⟨248249984906564601272420669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165499989937709734181613779 248249984906564601272420669)
  ·
    refine ⟨93093744339961725477157751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248249984906564601272420669 93093744339961725477157751)
    ·
      refine ⟨139640616509942588215736627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93093744339961725477157751 139640616509942588215736627)
      ·
        refine ⟨209460924764913882323604941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139640616509942588215736627 209460924764913882323604941)
        ·
          refine ⟨78547846786842705871351853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209460924764913882323604941 78547846786842705871351853)
          ·
            refine ⟨29455442545066014701756945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78547846786842705871351853 29455442545066014701756945)
            ·
              refine ⟨22091581908799511026317709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29455442545066014701756945 22091581908799511026317709)
              ·
                refine ⟨8284343215799816634869141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22091581908799511026317709 8284343215799816634869141)
                ·
                  refine ⟨388328588240616404759491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8284343215799816634869141 388328588240616404759491)
                  ·
                    rfl

theorem cell23_6806405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 6].length) (baseStart_6806405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806405 prefixEnd_6806405 := by exact prefixLift 6806405
  have htrace : WordTrace (prefixWord ++ tailWord_6806405) baseStart_6806405 baseEnd_6806405 := by
    simpa [prefixWord, tailWord_6806405, baseEnd_6806405] using wordTrace_append hprefix tailTrace_6806405
  have hstable : (prefixWord ++ tailWord_6806405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806405).length < 2 ^ (prefixWord ++ tailWord_6806405).sum := by decide
  have hdescent : baseEnd_6806405 < baseStart_6806405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806426 : List Nat := [3, 1, 1, 4, 3, 1, 2, 3, 1, 4]
def baseStart_6806426 : Nat := 118140960795 + 6806426 * 2 ^ 59
def prefixEnd_6806426 : Nat := 4983230072969 + 3 ^ 40 * 6806426 * 2
def baseEnd_6806426 : Nat := 1164989359086430686890941

theorem tailTrace_6806426 : CollatzResearch.WordTrace tailWord_6806426 prefixEnd_6806426 1164989359086430686890941 := by
  unfold tailWord_6806426
  simp only [CollatzResearch.WordTrace]
  refine ⟨62062687709872130464733783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165500500559659014572623421 62062687709872130464733783)
  ·
    refine ⟨93094031564808195697100675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62062687709872130464733783 93094031564808195697100675)
    ·
      refine ⟨139641047347212293545651013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93094031564808195697100675 139641047347212293545651013)
      ·
        refine ⟨26182696377602305039809565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139641047347212293545651013 26182696377602305039809565)
        ·
          refine ⟨9818511141600864389928587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26182696377602305039809565 9818511141600864389928587)
          ·
            refine ⟨14727766712401296584892881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9818511141600864389928587 14727766712401296584892881)
            ·
              refine ⟨11045825034300972438669661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14727766712401296584892881 11045825034300972438669661)
              ·
                refine ⟨4142184387862864664501123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11045825034300972438669661 4142184387862864664501123)
                ·
                  refine ⟨6213276581794296996751685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142184387862864664501123 6213276581794296996751685)
                  ·
                    refine ⟨1164989359086430686890941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6213276581794296996751685 1164989359086430686890941)
                    ·
                      rfl

theorem cell23_6806426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 1, 4].length) (baseStart_6806426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806426 prefixEnd_6806426 := by exact prefixLift 6806426
  have htrace : WordTrace (prefixWord ++ tailWord_6806426) baseStart_6806426 baseEnd_6806426 := by
    simpa [prefixWord, tailWord_6806426, baseEnd_6806426] using wordTrace_append hprefix tailTrace_6806426
  have hstable : (prefixWord ++ tailWord_6806426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806426).length < 2 ^ (prefixWord ++ tailWord_6806426).sum := by decide
  have hdescent : baseEnd_6806426 < baseStart_6806426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806439 : List Nat := [1, 1, 6, 1, 3, 2, 1, 2, 6]
def baseStart_6806439 : Nat := 118140960795 + 6806439 * 2 ^ 59
def prefixEnd_6806439 : Nat := 4983230072969 + 3 ^ 40 * 6806439 * 2
def baseEnd_6806439 : Nat := 388330528056422278867807

theorem tailTrace_6806439 : CollatzResearch.WordTrace tailWord_6806439 prefixEnd_6806439 388330528056422278867807 := by
  unfold tailWord_6806439
  simp only [CollatzResearch.WordTrace]
  refine ⟨248251224988441425079158371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165500816658960950052772247 248251224988441425079158371)
  ·
    refine ⟨372376837482662137618737557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248251224988441425079158371 372376837482662137618737557)
    ·
      refine ⟨17455164256999787700878323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 372376837482662137618737557 17455164256999787700878323)
      ·
        refine ⟨26182746385499681551317485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17455164256999787700878323 26182746385499681551317485)
        ·
          refine ⟨9818529894562380581744057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26182746385499681551317485 9818529894562380581744057)
          ·
            refine ⟨7363897420921785436308043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9818529894562380581744057 7363897420921785436308043)
            ·
              refine ⟨11045846131382678154462065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7363897420921785436308043 11045846131382678154462065)
              ·
                refine ⟨8284384598537008615846549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11045846131382678154462065 8284384598537008615846549)
                ·
                  refine ⟨388330528056422278867807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8284384598537008615846549 388330528056422278867807)
                  ·
                    rfl

theorem cell23_6806439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 6].length) (baseStart_6806439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806439 prefixEnd_6806439 := by exact prefixLift 6806439
  have htrace : WordTrace (prefixWord ++ tailWord_6806439) baseStart_6806439 baseEnd_6806439 := by
    simpa [prefixWord, tailWord_6806439, baseEnd_6806439] using wordTrace_append hprefix tailTrace_6806439
  have hstable : (prefixWord ++ tailWord_6806439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806439).length < 2 ^ (prefixWord ++ tailWord_6806439).sum := by decide
  have hdescent : baseEnd_6806439 < baseStart_6806439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806448 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 1, 12]
def baseStart_6806448 : Nat := 118140960795 + 6806448 * 2 ^ 59
def prefixEnd_6806448 : Nat := 4983230072969 + 3 ^ 40 * 6806448 * 2
def baseEnd_6806448 : Nat := 1164993124611230324865907

theorem tailTrace_6806448 : CollatzResearch.WordTrace tailWord_6806448 prefixEnd_6806448 1164993124611230324865907 := by
  unfold tailWord_6806448
  simp only [CollatzResearch.WordTrace]
  refine ⟨124125776622704409808117999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165501035496939213077490665 124125776622704409808117999)
  ·
    refine ⟨186188664934056614712176999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124125776622704409808117999 186188664934056614712176999)
    ·
      refine ⟨279282997401084922068265499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186188664934056614712176999 279282997401084922068265499)
      ·
        refine ⟨418924496101627383102398249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279282997401084922068265499 418924496101627383102398249)
        ·
          refine ⟨314193372076220537326798687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418924496101627383102398249 314193372076220537326798687)
          ·
            refine ⟨471290058114330805990198031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314193372076220537326798687 471290058114330805990198031)
            ·
              refine ⟨706935087171496208985297047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471290058114330805990198031 706935087171496208985297047)
              ·
                refine ⟨1060402630757244313477945571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706935087171496208985297047 1060402630757244313477945571)
                ·
                  refine ⟨1590603946135866470216918357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060402630757244313477945571 1590603946135866470216918357)
                  ·
                    refine ⟨1164993124611230324865907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1590603946135866470216918357 1164993124611230324865907)
                    ·
                      rfl

theorem cell23_6806448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 12].length) (baseStart_6806448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806448 prefixEnd_6806448 := by exact prefixLift 6806448
  have htrace : WordTrace (prefixWord ++ tailWord_6806448) baseStart_6806448 baseEnd_6806448 := by
    simpa [prefixWord, tailWord_6806448, baseEnd_6806448] using wordTrace_append hprefix tailTrace_6806448
  have hstable : (prefixWord ++ tailWord_6806448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806448).length < 2 ^ (prefixWord ++ tailWord_6806448).sum := by decide
  have hdescent : baseEnd_6806448 < baseStart_6806448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806455 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 4]
def baseStart_6806455 : Nat := 118140960795 + 6806455 * 2 ^ 59
def prefixEnd_6806455 : Nat := 4983230072969 + 3 ^ 40 * 6806455 * 2
def baseEnd_6806455 : Nat := 3494982968198272447210189

theorem tailTrace_6806455 : CollatzResearch.WordTrace tailWord_6806455 prefixEnd_6806455 3494982968198272447210189 := by
  unfold tailWord_6806455
  simp only [CollatzResearch.WordTrace]
  refine ⟨248251808556383459811740819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165501205704255639874493879 248251808556383459811740819)
  ·
    refine ⟨372377712834575189717611229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248251808556383459811740819 372377712834575189717611229)
    ·
      refine ⟨139641642312965696144104211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372377712834575189717611229 139641642312965696144104211)
      ·
        refine ⟨209462463469448544216156317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139641642312965696144104211 209462463469448544216156317)
        ·
          refine ⟨78548423801043204081058619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209462463469448544216156317 78548423801043204081058619)
          ·
            refine ⟨117822635701564806121587929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78548423801043204081058619 117822635701564806121587929)
            ·
              refine ⟨88366976776173604591190947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117822635701564806121587929 88366976776173604591190947)
              ·
                refine ⟨132550465164260406886786421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88366976776173604591190947 132550465164260406886786421)
                ·
                  refine ⟨12426606109149413145636227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132550465164260406886786421 12426606109149413145636227)
                  ·
                    refine ⟨18639909163724119718454341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12426606109149413145636227 18639909163724119718454341)
                    ·
                      refine ⟨3494982968198272447210189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18639909163724119718454341 3494982968198272447210189)
                      ·
                        rfl

theorem cell23_6806455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_6806455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806455 prefixEnd_6806455 := by exact prefixLift 6806455
  have htrace : WordTrace (prefixWord ++ tailWord_6806455) baseStart_6806455 baseEnd_6806455 := by
    simpa [prefixWord, tailWord_6806455, baseEnd_6806455] using wordTrace_append hprefix tailTrace_6806455
  have hstable : (prefixWord ++ tailWord_6806455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806455).length < 2 ^ (prefixWord ++ tailWord_6806455).sum := by decide
  have hdescent : baseEnd_6806455 < baseStart_6806455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806477 : List Nat := [1, 6, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_6806477 : Nat := 118140960795 + 6806477 * 2 ^ 59
def prefixEnd_6806477 : Nat := 4983230072969 + 3 ^ 40 * 6806477 * 2
def baseEnd_6806477 : Nat := 1164998088257557120378363

theorem tailTrace_6806477 : CollatzResearch.WordTrace tailWord_6806477 prefixEnd_6806477 1164998088257557120378363 := by
  unfold tailWord_6806477
  simp only [CollatzResearch.WordTrace]
  refine ⟨248252610962303757569041685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165501740641535838379361123 248252610962303757569041685)
  ·
    refine ⟨11636841138857988636048829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 248252610962303757569041685 11636841138857988636048829)
    ·
      refine ⟨4363815427071745738518311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11636841138857988636048829 4363815427071745738518311)
      ·
        refine ⟨6545723140607618607777467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4363815427071745738518311 6545723140607618607777467)
        ·
          refine ⟨9818584710911427911666201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6545723140607618607777467 9818584710911427911666201)
          ·
            refine ⟨7363938533183570933749651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9818584710911427911666201 7363938533183570933749651)
            ·
              refine ⟨11045907799775356400624477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7363938533183570933749651 11045907799775356400624477)
              ·
                refine ⟨4142215424915758650234179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11045907799775356400624477 4142215424915758650234179)
                ·
                  refine ⟨6213323137373637975351269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142215424915758650234179 6213323137373637975351269)
                  ·
                    refine ⟨1164998088257557120378363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6213323137373637975351269 1164998088257557120378363)
                    ·
                      rfl

theorem cell23_6806477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_6806477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806477 prefixEnd_6806477 := by exact prefixLift 6806477
  have htrace : WordTrace (prefixWord ++ tailWord_6806477) baseStart_6806477 baseEnd_6806477 := by
    simpa [prefixWord, tailWord_6806477, baseEnd_6806477] using wordTrace_append hprefix tailTrace_6806477
  have hstable : (prefixWord ++ tailWord_6806477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806477).length < 2 ^ (prefixWord ++ tailWord_6806477).sum := by decide
  have hdescent : baseEnd_6806477 < baseStart_6806477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806506 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 3, 2, 2]
def baseStart_6806506 : Nat := 118140960795 + 6806506 * 2 ^ 59
def prefixEnd_6806506 : Nat := 4983230072969 + 3 ^ 40 * 6806506 * 2
def baseEnd_6806506 : Nat := 3495009155711651747672455

theorem tailTrace_6806506 : CollatzResearch.WordTrace tailWord_6806506 prefixEnd_6806506 3495009155711651747672455 := by
  unfold tailWord_6806506
  simp only [CollatzResearch.WordTrace]
  refine ⟨62063417169799673880461843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165502445786132463681231581 62063417169799673880461843)
  ·
    refine ⟨93095125754699510820692765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62063417169799673880461843 93095125754699510820692765)
    ·
      refine ⟨34910672158012316557759787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93095125754699510820692765 34910672158012316557759787)
      ·
        refine ⟨52366008237018474836639681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34910672158012316557759787 52366008237018474836639681)
        ·
          refine ⟨39274506177763856127479761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52366008237018474836639681 39274506177763856127479761)
          ·
            refine ⟨29455879633322892095609821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39274506177763856127479761 29455879633322892095609821)
            ·
              refine ⟨11045954862496084535853683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29455879633322892095609821 11045954862496084535853683)
              ·
                refine ⟨16568932293744126803780525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11045954862496084535853683 16568932293744126803780525)
                ·
                  refine ⟨6213349610154047551417697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16568932293744126803780525 6213349610154047551417697)
                  ·
                    refine ⟨4660012207615535663563273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6213349610154047551417697 4660012207615535663563273)
                    ·
                      refine ⟨3495009155711651747672455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660012207615535663563273 3495009155711651747672455)
                      ·
                        rfl

theorem cell23_6806506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_6806506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806506 prefixEnd_6806506 := by exact prefixLift 6806506
  have htrace : WordTrace (prefixWord ++ tailWord_6806506) baseStart_6806506 baseEnd_6806506 := by
    simpa [prefixWord, tailWord_6806506, baseEnd_6806506] using wordTrace_append hprefix tailTrace_6806506
  have hstable : (prefixWord ++ tailWord_6806506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806506).length < 2 ^ (prefixWord ++ tailWord_6806506).sum := by decide
  have hdescent : baseEnd_6806506 < baseStart_6806506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806526 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_6806526 : Nat := 118140960795 + 6806526 * 2 ^ 59
def prefixEnd_6806526 : Nat := 4983230072969 + 3 ^ 40 * 6806526 * 2
def baseEnd_6806526 : Nat := 3495019425324741669422363

theorem tailTrace_6806526 : CollatzResearch.WordTrace tailWord_6806526 prefixEnd_6806526 3495019425324741669422363 := by
  unfold tailWord_6806526
  simp only [CollatzResearch.WordTrace]
  refine ⟨31031799767390779867196929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165502932092750825958383621 31031799767390779867196929)
  ·
    refine ⟨23273849825543084900397697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31031799767390779867196929 23273849825543084900397697)
    ·
      refine ⟨17455387369157313675298273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23273849825543084900397697 17455387369157313675298273)
      ·
        refine ⟨13091540526867985256473705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17455387369157313675298273 13091540526867985256473705)
        ·
          refine ⟨9818655395150988942355279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13091540526867985256473705 9818655395150988942355279)
          ·
            refine ⟨14727983092726483413532919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9818655395150988942355279 14727983092726483413532919)
            ·
              refine ⟨22091974639089725120299379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14727983092726483413532919 22091974639089725120299379)
              ·
                refine ⟨33137961958634587680449069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22091974639089725120299379 33137961958634587680449069)
                ·
                  refine ⟨12426735734487970380168401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33137961958634587680449069 12426735734487970380168401)
                  ·
                    refine ⟨9320051800865977785126301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12426735734487970380168401 9320051800865977785126301)
                    ·
                      refine ⟨3495019425324741669422363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9320051800865977785126301 3495019425324741669422363)
                      ·
                        rfl

theorem cell23_6806526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_6806526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806526 prefixEnd_6806526 := by exact prefixLift 6806526
  have htrace : WordTrace (prefixWord ++ tailWord_6806526) baseStart_6806526 baseEnd_6806526 := by
    simpa [prefixWord, tailWord_6806526, baseEnd_6806526] using wordTrace_append hprefix tailTrace_6806526
  have hstable : (prefixWord ++ tailWord_6806526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806526).length < 2 ^ (prefixWord ++ tailWord_6806526).sum := by decide
  have hdescent : baseEnd_6806526 < baseStart_6806526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806545 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 4]
def baseStart_6806545 : Nat := 118140960795 + 6806545 * 2 ^ 59
def prefixEnd_6806545 : Nat := 4983230072969 + 3 ^ 40 * 6806545 * 2
def baseEnd_6806545 : Nat := 3495029181457177095084775

theorem tailTrace_6806545 : CollatzResearch.WordTrace tailWord_6806545 prefixEnd_6806545 3495029181457177095084775 := by
  unfold tailWord_6806545
  simp only [CollatzResearch.WordTrace]
  refine ⟨248255091126057405182517089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165503394084038270121678059 248255091126057405182517089)
  ·
    refine ⟨186191318344543053886887817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248255091126057405182517089 186191318344543053886887817)
    ·
      refine ⟨139643488758407290415165863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186191318344543053886887817 139643488758407290415165863)
      ·
        refine ⟨209465233137610935622748795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139643488758407290415165863 209465233137610935622748795)
        ·
          refine ⟨314197849706416403434123193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209465233137610935622748795 314197849706416403434123193)
          ·
            refine ⟨235648387279812302575592395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314197849706416403434123193 235648387279812302575592395)
            ·
              refine ⟨353472580919718453863388593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235648387279812302575592395 353472580919718453863388593)
              ·
                refine ⟨265104435689788840397541445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353472580919718453863388593 265104435689788840397541445)
                ·
                  refine ⟨49707081691835407574539021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 265104435689788840397541445 49707081691835407574539021)
                  ·
                    refine ⟨18640155634438277840452133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49707081691835407574539021 18640155634438277840452133)
                    ·
                      refine ⟨3495029181457177095084775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18640155634438277840452133 3495029181457177095084775)
                      ·
                        rfl

theorem cell23_6806545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_6806545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806545 prefixEnd_6806545 := by exact prefixLift 6806545
  have htrace : WordTrace (prefixWord ++ tailWord_6806545) baseStart_6806545 baseEnd_6806545 := by
    simpa [prefixWord, tailWord_6806545, baseEnd_6806545] using wordTrace_append hprefix tailTrace_6806545
  have hstable : (prefixWord ++ tailWord_6806545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806545).length < 2 ^ (prefixWord ++ tailWord_6806545).sum := by decide
  have hdescent : baseEnd_6806545 < baseStart_6806545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806546 : List Nat := [3, 2, 5, 1, 2, 10]
def baseStart_6806546 : Nat := 118140960795 + 6806546 * 2 ^ 59
def prefixEnd_6806546 : Nat := 4983230072969 + 3 ^ 40 * 6806546 * 2
def baseEnd_6806546 : Nat := 14382838250772969510997

theorem tailTrace_6806546 : CollatzResearch.WordTrace tailWord_6806546 prefixEnd_6806546 14382838250772969510997 := by
  unfold tailWord_6806546
  simp only [CollatzResearch.WordTrace]
  refine ⟨62063781899763445588325873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165503418399369188235535661 62063781899763445588325873)
  ·
    refine ⟨46547836424822584191244405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62063781899763445588325873 46547836424822584191244405)
    ·
      refine ⟨4363859664827117267929163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46547836424822584191244405 4363859664827117267929163)
      ·
        refine ⟨6545789497240675901893745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4363859664827117267929163 6545789497240675901893745)
        ·
          refine ⟨4909342122930506926420309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6545789497240675901893745 4909342122930506926420309)
          ·
            refine ⟨14382838250772969510997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4909342122930506926420309 14382838250772969510997)
            ·
              rfl

theorem cell23_6806546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 10].length) (baseStart_6806546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806546 prefixEnd_6806546 := by exact prefixLift 6806546
  have htrace : WordTrace (prefixWord ++ tailWord_6806546) baseStart_6806546 baseEnd_6806546 := by
    simpa [prefixWord, tailWord_6806546, baseEnd_6806546] using wordTrace_append hprefix tailTrace_6806546
  have hstable : (prefixWord ++ tailWord_6806546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806546).length < 2 ^ (prefixWord ++ tailWord_6806546).sum := by decide
  have hdescent : baseEnd_6806546 < baseStart_6806546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806557 : List Nat := [1, 4, 2, 2, 3, 2, 2, 2, 1, 2, 2]
def baseStart_6806557 : Nat := 118140960795 + 6806557 * 2 ^ 59
def prefixEnd_6806557 : Nat := 4983230072969 + 3 ^ 40 * 6806557 * 2
def baseEnd_6806557 : Nat := 3495035343225031048134721

theorem tailTrace_6806557 : CollatzResearch.WordTrace tailWord_6806557 prefixEnd_6806557 3495035343225031048134721 := by
  unfold tailWord_6806557
  simp only [CollatzResearch.WordTrace]
  refine ⟨248255528802013931231953925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165503685868009287487969283 248255528802013931231953925)
  ·
    refine ⟨46547911650377612105991361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248255528802013931231953925 46547911650377612105991361)
    ·
      refine ⟨34910933737783209079493521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46547911650377612105991361 34910933737783209079493521)
      ·
        refine ⟨26183200303337406809620141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34910933737783209079493521 26183200303337406809620141)
        ·
          refine ⟨9818700113751527553607553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26183200303337406809620141 9818700113751527553607553)
          ·
            refine ⟨7364025085313645665205665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9818700113751527553607553 7364025085313645665205665)
            ·
              refine ⟨5523018813985234248904249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7364025085313645665205665 5523018813985234248904249)
              ·
                refine ⟨4142264110488925686678187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5523018813985234248904249 4142264110488925686678187)
                ·
                  refine ⟨6213396165733388530017281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142264110488925686678187 6213396165733388530017281)
                  ·
                    refine ⟨4660047124300041397512961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6213396165733388530017281 4660047124300041397512961)
                    ·
                      refine ⟨3495035343225031048134721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660047124300041397512961 3495035343225031048134721)
                      ·
                        rfl

theorem cell23_6806557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_6806557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806557 prefixEnd_6806557 := by exact prefixLift 6806557
  have htrace : WordTrace (prefixWord ++ tailWord_6806557) baseStart_6806557 baseEnd_6806557 := by
    simpa [prefixWord, tailWord_6806557, baseEnd_6806557] using wordTrace_append hprefix tailTrace_6806557
  have hstable : (prefixWord ++ tailWord_6806557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806557).length < 2 ^ (prefixWord ++ tailWord_6806557).sum := by decide
  have hdescent : baseEnd_6806557 < baseStart_6806557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806562 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_6806562 : Nat := 118140960795 + 6806562 * 2 ^ 59
def prefixEnd_6806562 : Nat := 4983230072969 + 3 ^ 40 * 6806562 * 2
def baseEnd_6806562 : Nat := 3495037910628303528572197

theorem tailTrace_6806562 : CollatzResearch.WordTrace tailWord_6806562 prefixEnd_6806562 3495037910628303528572197 := by
  unfold tailWord_6806562
  simp only [CollatzResearch.WordTrace]
  refine ⟨62063927791748954271471485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165503807444663878057257293 62063927791748954271471485)
  ·
    refine ⟨23273972921905857851801807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62063927791748954271471485 23273972921905857851801807)
    ·
      refine ⟨34910959382858786777702711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23273972921905857851801807 34910959382858786777702711)
      ·
        refine ⟨52366439074288180166554067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34910959382858786777702711 52366439074288180166554067)
        ·
          refine ⟨78549658611432270249831101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52366439074288180166554067 78549658611432270249831101)
          ·
            refine ⟨29456121979287101343686663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78549658611432270249831101 29456121979287101343686663)
            ·
              refine ⟨44184182968930652015529995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29456121979287101343686663 44184182968930652015529995)
              ·
                refine ⟨66276274453395978023294993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44184182968930652015529995 66276274453395978023294993)
                ·
                  refine ⟨49707205840046983517471245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66276274453395978023294993 49707205840046983517471245)
                  ·
                    refine ⟨18640202190017618819051717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49707205840046983517471245 18640202190017618819051717)
                    ·
                      refine ⟨3495037910628303528572197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18640202190017618819051717 3495037910628303528572197)
                      ·
                        rfl

theorem cell23_6806562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_6806562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806562 prefixEnd_6806562 := by exact prefixLift 6806562
  have htrace : WordTrace (prefixWord ++ tailWord_6806562) baseStart_6806562 baseEnd_6806562 := by
    simpa [prefixWord, tailWord_6806562, baseEnd_6806562] using wordTrace_append hprefix tailTrace_6806562
  have hstable : (prefixWord ++ tailWord_6806562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806562).length < 2 ^ (prefixWord ++ tailWord_6806562).sum := by decide
  have hdescent : baseEnd_6806562 < baseStart_6806562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806579 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 6, 2, 2]
def baseStart_6806579 : Nat := 118140960795 + 6806579 * 2 ^ 59
def prefixEnd_6806579 : Nat := 4983230072969 + 3 ^ 40 * 6806579 * 2
def baseEnd_6806579 : Nat := 3495046639799429962059619

theorem tailTrace_6806579 : CollatzResearch.WordTrace tailWord_6806579 prefixEnd_6806579 3495046639799429962059619 := by
  unfold tailWord_6806579
  simp only [CollatzResearch.WordTrace]
  refine ⟨248256331207934228989254791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165504220805289485992836527 248256331207934228989254791)
  ·
    refine ⟨372384496811901343483882187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248256331207934228989254791 372384496811901343483882187)
    ·
      refine ⟨558576745217852015225823281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372384496811901343483882187 558576745217852015225823281)
      ·
        refine ⟨418932558913389011419367461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558576745217852015225823281 418932558913389011419367461)
        ·
          refine ⟨78549854796260439641131399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 418932558913389011419367461 78549854796260439641131399)
          ·
            refine ⟨117824782194390659461697099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78549854796260439641131399 117824782194390659461697099)
            ·
              refine ⟨176737173291585989192545649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117824782194390659461697099 176737173291585989192545649)
              ·
                refine ⟨132552879968689491894409237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176737173291585989192545649 132552879968689491894409237)
                ·
                  refine ⟨6213416248532319932550433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132552879968689491894409237 6213416248532319932550433)
                  ·
                    refine ⟨4660062186399239949412825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6213416248532319932550433 4660062186399239949412825)
                    ·
                      refine ⟨3495046639799429962059619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660062186399239949412825 3495046639799429962059619)
                      ·
                        rfl

theorem cell23_6806579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 2, 2].length) (baseStart_6806579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806579 prefixEnd_6806579 := by exact prefixLift 6806579
  have htrace : WordTrace (prefixWord ++ tailWord_6806579) baseStart_6806579 baseEnd_6806579 := by
    simpa [prefixWord, tailWord_6806579, baseEnd_6806579] using wordTrace_append hprefix tailTrace_6806579
  have hstable : (prefixWord ++ tailWord_6806579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806579).length < 2 ^ (prefixWord ++ tailWord_6806579).sum := by decide
  have hdescent : baseEnd_6806579 < baseStart_6806579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806652 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_6806652 : Nat := 118140960795 + 6806652 * 2 ^ 59
def prefixEnd_6806652 : Nat := 4983230072969 + 3 ^ 40 * 6806652 * 2
def baseEnd_6806652 : Nat := 3495084123887208176446783

theorem tailTrace_6806652 : CollatzResearch.WordTrace tailWord_6806652 prefixEnd_6806652 3495084123887208176446783 := by
  unfold tailWord_6806652
  simp only [CollatzResearch.WordTrace]
  refine ⟨124129496868334881228331105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165505995824446508304441473 124129496868334881228331105)
  ·
    refine ⟨93097122651251160921248329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124129496868334881228331105 93097122651251160921248329)
    ·
      refine ⟨69822841988438370690936247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93097122651251160921248329 69822841988438370690936247)
      ·
        refine ⟨104734262982657556036404371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69822841988438370690936247 104734262982657556036404371)
        ·
          refine ⟨157101394473986334054606557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104734262982657556036404371 157101394473986334054606557)
          ·
            refine ⟨58913022927744875270477459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157101394473986334054606557 58913022927744875270477459)
            ·
              refine ⟨88369534391617312905716189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58913022927744875270477459 88369534391617312905716189)
              ·
                refine ⟨33138575396856492339643571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88369534391617312905716189 33138575396856492339643571)
                ·
                  refine ⟨49707863095284738509465357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33138575396856492339643571 49707863095284738509465357)
                  ·
                    refine ⟨18640448660731776941049509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49707863095284738509465357 18640448660731776941049509)
                    ·
                      refine ⟨3495084123887208176446783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18640448660731776941049509 3495084123887208176446783)
                      ·
                        rfl

theorem cell23_6806652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_6806652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806652 prefixEnd_6806652 := by exact prefixLift 6806652
  have htrace : WordTrace (prefixWord ++ tailWord_6806652) baseStart_6806652 baseEnd_6806652 := by
    simpa [prefixWord, tailWord_6806652, baseEnd_6806652] using wordTrace_append hprefix tailTrace_6806652
  have hstable : (prefixWord ++ tailWord_6806652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806652).length < 2 ^ (prefixWord ++ tailWord_6806652).sum := by decide
  have hdescent : baseEnd_6806652 < baseStart_6806652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806672 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 3]
def baseStart_6806672 : Nat := 118140960795 + 6806672 * 2 ^ 59
def prefixEnd_6806672 : Nat := 4983230072969 + 3 ^ 40 * 6806672 * 2
def baseEnd_6806672 : Nat := 3495094393500298098196691

theorem tailTrace_6806672 : CollatzResearch.WordTrace tailWord_6806672 prefixEnd_6806672 3495094393500298098196691 := by
  unfold tailWord_6806672
  simp only [CollatzResearch.WordTrace]
  refine ⟨124129861598298652936195135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165506482131064870581593513 124129861598298652936195135)
  ·
    refine ⟨186194792397447979404292703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124129861598298652936195135 186194792397447979404292703)
    ·
      refine ⟨279292188596171969106439055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186194792397447979404292703 279292188596171969106439055)
      ·
        refine ⟨418938282894257953659658583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279292188596171969106439055 418938282894257953659658583)
        ·
          refine ⟨628407424341386930489487875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418938282894257953659658583 628407424341386930489487875)
          ·
            refine ⟨942611136512080395734231813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628407424341386930489487875 942611136512080395734231813)
            ·
              refine ⟨176739588096015074200168465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 942611136512080395734231813 176739588096015074200168465)
              ·
                refine ⟨132554691072011305650126349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176739588096015074200168465 132554691072011305650126349)
                ·
                  refine ⟨49708009152004239618797381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132554691072011305650126349 49708009152004239618797381)
                  ·
                    refine ⟨9320251716000794928524509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49708009152004239618797381 9320251716000794928524509)
                    ·
                      refine ⟨3495094393500298098196691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9320251716000794928524509 3495094393500298098196691)
                      ·
                        rfl

theorem cell23_6806672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 3].length) (baseStart_6806672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806672 prefixEnd_6806672 := by exact prefixLift 6806672
  have htrace : WordTrace (prefixWord ++ tailWord_6806672) baseStart_6806672 baseEnd_6806672 := by
    simpa [prefixWord, tailWord_6806672, baseEnd_6806672] using wordTrace_append hprefix tailTrace_6806672
  have hstable : (prefixWord ++ tailWord_6806672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806672).length < 2 ^ (prefixWord ++ tailWord_6806672).sum := by decide
  have hdescent : baseEnd_6806672 < baseStart_6806672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806689 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 4, 2, 3]
def baseStart_6806689 : Nat := 118140960795 + 6806689 * 2 ^ 59
def prefixEnd_6806689 : Nat := 4983230072969 + 3 ^ 40 * 6806689 * 2
def baseEnd_6806689 : Nat := 3495103122671424531684113

theorem tailTrace_6806689 : CollatzResearch.WordTrace tailWord_6806689 prefixEnd_6806689 3495103122671424531684113 := by
  unfold tailWord_6806689
  simp only [CollatzResearch.WordTrace]
  refine ⟨248260343237535717775759121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165506895491690478517172747 248260343237535717775759121)
  ·
    refine ⟨186195257428151788331819341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248260343237535717775759121 186195257428151788331819341)
    ·
      refine ⟨69823221535556920624432253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186195257428151788331819341 69823221535556920624432253)
      ·
        refine ⟨26183708075833845234162095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69823221535556920624432253 26183708075833845234162095)
        ·
          refine ⟨39275562113750767851243143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26183708075833845234162095 39275562113750767851243143)
          ·
            refine ⟨58913343170626151776864715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39275562113750767851243143 58913343170626151776864715)
            ·
              refine ⟨88370014755939227665297073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58913343170626151776864715 88370014755939227665297073)
              ·
                refine ⟨66277511066954420748972805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88370014755939227665297073 66277511066954420748972805)
                ·
                  refine ⟨12427033325053953890432401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66277511066954420748972805 12427033325053953890432401)
                  ·
                    refine ⟨9320274993790465417824301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12427033325053953890432401 9320274993790465417824301)
                    ·
                      refine ⟨3495103122671424531684113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9320274993790465417824301 3495103122671424531684113)
                      ·
                        rfl

theorem cell23_6806689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_6806689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806689 prefixEnd_6806689 := by exact prefixLift 6806689
  have htrace : WordTrace (prefixWord ++ tailWord_6806689) baseStart_6806689 baseEnd_6806689 := by
    simpa [prefixWord, tailWord_6806689, baseEnd_6806689] using wordTrace_append hprefix tailTrace_6806689
  have hstable : (prefixWord ++ tailWord_6806689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806689).length < 2 ^ (prefixWord ++ tailWord_6806689).sum := by decide
  have hdescent : baseEnd_6806689 < baseStart_6806689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806706 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3]
def baseStart_6806706 : Nat := 118140960795 + 6806706 * 2 ^ 59
def prefixEnd_6806706 : Nat := 4983230072969 + 3 ^ 40 * 6806706 * 2
def baseEnd_6806706 : Nat := 3495111851842550965171535

theorem tailTrace_6806706 : CollatzResearch.WordTrace tailWord_6806706 prefixEnd_6806706 3495111851842550965171535 := by
  unfold tailWord_6806706
  simp only [CollatzResearch.WordTrace]
  refine ⟨62065240819618532419781993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165507308852316086452751981 62065240819618532419781993)
  ·
    refine ⟨46548930614713899314836495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62065240819618532419781993 46548930614713899314836495)
    ·
      refine ⟨69823395922070848972254743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46548930614713899314836495 69823395922070848972254743)
      ·
        refine ⟨104735093883106273458382115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69823395922070848972254743 104735093883106273458382115)
        ·
          refine ⟨157102640824659410187573173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104735093883106273458382115 157102640824659410187573173)
          ·
            refine ⟨14728372577311819705084985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157102640824659410187573173 14728372577311819705084985)
            ·
              refine ⟨11046279432983864778813739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14728372577311819705084985 11046279432983864778813739)
              ·
                refine ⟨16569419149475797168220609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11046279432983864778813739 16569419149475797168220609)
                ·
                  refine ⟨12427064362106847876165457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16569419149475797168220609 12427064362106847876165457)
                  ·
                    refine ⟨9320298271580135907124093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12427064362106847876165457 9320298271580135907124093)
                    ·
                      refine ⟨3495111851842550965171535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9320298271580135907124093 3495111851842550965171535)
                      ·
                        rfl

theorem cell23_6806706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_6806706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806706 prefixEnd_6806706 := by exact prefixLift 6806706
  have htrace : WordTrace (prefixWord ++ tailWord_6806706) baseStart_6806706 baseEnd_6806706 := by
    simpa [prefixWord, tailWord_6806706, baseEnd_6806706] using wordTrace_append hprefix tailTrace_6806706
  have hstable : (prefixWord ++ tailWord_6806706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806706).length < 2 ^ (prefixWord ++ tailWord_6806706).sum := by decide
  have hdescent : baseEnd_6806706 < baseStart_6806706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806730 : List Nat := [3, 1, 2, 1, 3, 4, 2, 2, 1, 4]
def baseStart_6806730 : Nat := 118140960795 + 6806730 * 2 ^ 59
def prefixEnd_6806730 : Nat := 4983230072969 + 3 ^ 40 * 6806730 * 2
def baseEnd_6806730 : Nat := 1165041391792752957090475

theorem tailTrace_6806730 : CollatzResearch.WordTrace tailWord_6806730 prefixEnd_6806730 1165041391792752957090475 := by
  unfold tailWord_6806730
  simp only [CollatzResearch.WordTrace]
  refine ⟨62065459657596795444500411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165507892420258121185334429 62065459657596795444500411)
  ·
    refine ⟨93098189486395193166750617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62065459657596795444500411 93098189486395193166750617)
    ·
      refine ⟨69823642114796394875062963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93098189486395193166750617 69823642114796394875062963)
      ·
        refine ⟨104735463172194592312594445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69823642114796394875062963 104735463172194592312594445)
        ·
          refine ⟨39275798689572972117222917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104735463172194592312594445 39275798689572972117222917)
          ·
            refine ⟨7364212254294932271979297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39275798689572972117222917 7364212254294932271979297)
            ·
              refine ⟨5523159190721199203984473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7364212254294932271979297 5523159190721199203984473)
              ·
                refine ⟨4142369393040899402988355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5523159190721199203984473 4142369393040899402988355)
                ·
                  refine ⟨6213554089561349104482533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142369393040899402988355 6213554089561349104482533)
                  ·
                    refine ⟨1165041391792752957090475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6213554089561349104482533 1165041391792752957090475)
                    ·
                      rfl

theorem cell23_6806730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_6806730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806730 prefixEnd_6806730 := by exact prefixLift 6806730
  have htrace : WordTrace (prefixWord ++ tailWord_6806730) baseStart_6806730 baseEnd_6806730 := by
    simpa [prefixWord, tailWord_6806730, baseEnd_6806730] using wordTrace_append hprefix tailTrace_6806730
  have hstable : (prefixWord ++ tailWord_6806730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806730).length < 2 ^ (prefixWord ++ tailWord_6806730).sum := by decide
  have hdescent : baseEnd_6806730 < baseStart_6806730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806763 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 2, 3, 2]
def baseStart_6806763 : Nat := 118140960795 + 6806763 * 2 ^ 59
def prefixEnd_6806763 : Nat := 4983230072969 + 3 ^ 40 * 6806763 * 2
def baseEnd_6806763 : Nat := 3495141120239857242158773

theorem tailTrace_6806763 : CollatzResearch.WordTrace tailWord_6806763 prefixEnd_6806763 3495141120239857242158773 := by
  unfold tailWord_6806763
  simp only [CollatzResearch.WordTrace]
  refine ⟨248263042239267628413952943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165508694826178418942635295 248263042239267628413952943)
  ·
    refine ⟨372394563358901442620929415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248263042239267628413952943 372394563358901442620929415)
    ·
      refine ⟨558591845038352163931394123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372394563358901442620929415 558591845038352163931394123)
      ·
        refine ⟨837887767557528245897091185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558591845038352163931394123 837887767557528245897091185)
        ·
          refine ⟨628415825668146184422818389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 837887767557528245897091185 628415825668146184422818389)
          ·
            refine ⟨7364247957048588098704903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 628415825668146184422818389 7364247957048588098704903)
            ·
              refine ⟨11046371935572882148057355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7364247957048588098704903 11046371935572882148057355)
              ·
                refine ⟨16569557903359323222086033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11046371935572882148057355 16569557903359323222086033)
                ·
                  refine ⟨12427168427519492416564525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16569557903359323222086033 12427168427519492416564525)
                  ·
                    refine ⟨4660188160319809656211697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12427168427519492416564525 4660188160319809656211697)
                    ·
                      refine ⟨3495141120239857242158773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660188160319809656211697 3495141120239857242158773)
                      ·
                        rfl

theorem cell23_6806763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 3, 2].length) (baseStart_6806763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806763 prefixEnd_6806763 := by exact prefixLift 6806763
  have htrace : WordTrace (prefixWord ++ tailWord_6806763) baseStart_6806763 baseEnd_6806763 := by
    simpa [prefixWord, tailWord_6806763, baseEnd_6806763] using wordTrace_append hprefix tailTrace_6806763
  have hstable : (prefixWord ++ tailWord_6806763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806763).length < 2 ^ (prefixWord ++ tailWord_6806763).sum := by decide
  have hdescent : baseEnd_6806763 < baseStart_6806763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806769 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 4, 4]
def baseStart_6806769 : Nat := 118140960795 + 6806769 * 2 ^ 59
def prefixEnd_6806769 : Nat := 4983230072969 + 3 ^ 40 * 6806769 * 2
def baseEnd_6806769 : Nat := 1165048067041261406227915

theorem tailTrace_6806769 : CollatzResearch.WordTrace tailWord_6806769 prefixEnd_6806769 1165048067041261406227915 := by
  unfold tailWord_6806769
  simp only [CollatzResearch.WordTrace]
  refine ⟨248263261077245891438671361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165508840718163927625780907 248263261077245891438671361)
  ·
    refine ⟨186197445807934418579003521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248263261077245891438671361 186197445807934418579003521)
    ·
      refine ⟨139648084355950813934252641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186197445807934418579003521 139648084355950813934252641)
      ·
        refine ⟨104736063266963110450689481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139648084355950813934252641 104736063266963110450689481)
        ·
          refine ⟨78552047450222332838017111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104736063266963110450689481 78552047450222332838017111)
          ·
            refine ⟨117828071175333499257025667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78552047450222332838017111 117828071175333499257025667)
            ·
              refine ⟨176742106763000248885538501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117828071175333499257025667 176742106763000248885538501)
              ·
                refine ⟨33139145018062546666038469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176742106763000248885538501 33139145018062546666038469)
                ·
                  refine ⟨6213589690886727499882213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33139145018062546666038469 6213589690886727499882213)
                  ·
                    refine ⟨1165048067041261406227915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6213589690886727499882213 1165048067041261406227915)
                    ·
                      rfl

theorem cell23_6806769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_6806769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806769 prefixEnd_6806769 := by exact prefixLift 6806769
  have htrace : WordTrace (prefixWord ++ tailWord_6806769) baseStart_6806769 baseEnd_6806769 := by
    simpa [prefixWord, tailWord_6806769, baseEnd_6806769] using wordTrace_append hprefix tailTrace_6806769
  have hstable : (prefixWord ++ tailWord_6806769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806769).length < 2 ^ (prefixWord ++ tailWord_6806769).sum := by decide
  have hdescent : baseEnd_6806769 < baseStart_6806769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806793 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 3, 2, 2]
def baseStart_6806793 : Nat := 118140960795 + 6806793 * 2 ^ 59
def prefixEnd_6806793 : Nat := 4983230072969 + 3 ^ 40 * 6806793 * 2
def baseEnd_6806793 : Nat := 3495156524659492124783635

theorem tailTrace_6806793 : CollatzResearch.WordTrace tailWord_6806793 prefixEnd_6806793 3495156524659492124783635 := by
  unfold tailWord_6806793
  simp only [CollatzResearch.WordTrace]
  refine ⟨248264136429158943537545033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165509424286105962358363355 248264136429158943537545033)
  ·
    refine ⟨186198102321869207653158775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248264136429158943537545033 186198102321869207653158775)
    ·
      refine ⟨279297153482803811479738163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186198102321869207653158775 279297153482803811479738163)
      ·
        refine ⟨418945730224205717219607245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279297153482803811479738163 418945730224205717219607245)
        ·
          refine ⟨157104648834077143957352717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418945730224205717219607245 157104648834077143957352717)
          ·
            refine ⟨58914243312778928984007269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157104648834077143957352717 58914243312778928984007269)
            ·
              refine ⟨11046420621146049184501363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58914243312778928984007269 11046420621146049184501363)
              ·
                refine ⟨16569630931719073776752045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11046420621146049184501363 16569630931719073776752045)
                ·
                  refine ⟨6213611599394652666282017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16569630931719073776752045 6213611599394652666282017)
                  ·
                    refine ⟨4660208699545989499711513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6213611599394652666282017 4660208699545989499711513)
                    ·
                      refine ⟨3495156524659492124783635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660208699545989499711513 3495156524659492124783635)
                      ·
                        rfl

theorem cell23_6806793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 2, 2].length) (baseStart_6806793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806793 prefixEnd_6806793 := by exact prefixLift 6806793
  have htrace : WordTrace (prefixWord ++ tailWord_6806793) baseStart_6806793 baseEnd_6806793 := by
    simpa [prefixWord, tailWord_6806793, baseEnd_6806793] using wordTrace_append hprefix tailTrace_6806793
  have hstable : (prefixWord ++ tailWord_6806793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806793).length < 2 ^ (prefixWord ++ tailWord_6806793).sum := by decide
  have hdescent : baseEnd_6806793 < baseStart_6806793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806813 : List Nat := [1, 4, 2, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_6806813 : Nat := 118140960795 + 6806813 * 2 ^ 59
def prefixEnd_6806813 : Nat := 4983230072969 + 3 ^ 40 * 6806813 * 2
def baseEnd_6806813 : Nat := 3495166794272582046533543

theorem tailTrace_6806813 : CollatzResearch.WordTrace tailWord_6806813 prefixEnd_6806813 3495166794272582046533543 := by
  unfold tailWord_6806813
  simp only [CollatzResearch.WordTrace]
  refine ⟨248264865889086486953273093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165509910592724324635515395 248264865889086486953273093)
  ·
    refine ⟨46549662354203716303738705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248264865889086486953273093 46549662354203716303738705)
    ·
      refine ⟨34912246765652787227804029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46549662354203716303738705 34912246765652787227804029)
      ·
        refine ⟨13092092537119795210426511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34912246765652787227804029 13092092537119795210426511)
        ·
          refine ⟨19638138805679692815639767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13092092537119795210426511 19638138805679692815639767)
          ·
            refine ⟨29457208208519539223459651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19638138805679692815639767 29457208208519539223459651)
            ·
              refine ⟨44185812312779308835189477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29457208208519539223459651 44185812312779308835189477)
              ·
                refine ⟨8284839808646120406598027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44185812312779308835189477 8284839808646120406598027)
                ·
                  refine ⟨12427259712969180609897041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8284839808646120406598027 12427259712969180609897041)
                  ·
                    refine ⟨9320444784726885457422781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12427259712969180609897041 9320444784726885457422781)
                    ·
                      refine ⟨3495166794272582046533543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9320444784726885457422781 3495166794272582046533543)
                      ·
                        rfl

theorem cell23_6806813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_6806813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806813 prefixEnd_6806813 := by exact prefixLift 6806813
  have htrace : WordTrace (prefixWord ++ tailWord_6806813) baseStart_6806813 baseEnd_6806813 := by
    simpa [prefixWord, tailWord_6806813, baseEnd_6806813] using wordTrace_append hprefix tailTrace_6806813
  have hstable : (prefixWord ++ tailWord_6806813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806813).length < 2 ^ (prefixWord ++ tailWord_6806813).sum := by decide
  have hdescent : baseEnd_6806813 < baseStart_6806813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806860 : List Nat := [2, 2, 1, 3, 2, 2, 4, 1, 2, 1, 3]
def baseStart_6806860 : Nat := 118140960795 + 6806860 * 2 ^ 59
def prefixEnd_6806860 : Nat := 4983230072969 + 3 ^ 40 * 6806860 * 2
def baseEnd_6806860 : Nat := 3495190927863343362645827

theorem tailTrace_6806860 : CollatzResearch.WordTrace tailWord_6806860 prefixEnd_6806860 3495190927863343362645827 := by
  unfold tailWord_6806860
  simp only [CollatzResearch.WordTrace]
  refine ⟨124133290059958106990117017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165511053413277475986822689 124133290059958106990117017)
  ·
    refine ⟨93099967544968580242587763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124133290059958106990117017 93099967544968580242587763)
    ·
      refine ⟨139649951317452870363881645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93099967544968580242587763 139649951317452870363881645)
      ·
        refine ⟨52368731744044826386455617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139649951317452870363881645 52368731744044826386455617)
        ·
          refine ⟨39276548808033619789841713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52368731744044826386455617 39276548808033619789841713)
          ·
            refine ⟨29457411606025214842381285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39276548808033619789841713 29457411606025214842381285)
            ·
              refine ⟨5523264676129727782946491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29457411606025214842381285 5523264676129727782946491)
              ·
                refine ⟨8284897014194591674419737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523264676129727782946491 8284897014194591674419737)
                ·
                  refine ⟨6213672760645943755814803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8284897014194591674419737 6213672760645943755814803)
                  ·
                    refine ⟨9320509140968915633722205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6213672760645943755814803 9320509140968915633722205)
                    ·
                      refine ⟨3495190927863343362645827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9320509140968915633722205 3495190927863343362645827)
                      ·
                        rfl

theorem cell23_6806860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_6806860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806860 prefixEnd_6806860 := by exact prefixLift 6806860
  have htrace : WordTrace (prefixWord ++ tailWord_6806860) baseStart_6806860 baseEnd_6806860 := by
    simpa [prefixWord, tailWord_6806860, baseEnd_6806860] using wordTrace_append hprefix tailTrace_6806860
  have hstable : (prefixWord ++ tailWord_6806860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806860).length < 2 ^ (prefixWord ++ tailWord_6806860).sum := by decide
  have hdescent : baseEnd_6806860 < baseStart_6806860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806877 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_6806877 : Nat := 118140960795 + 6806877 * 2 ^ 59
def prefixEnd_6806877 : Nat := 4983230072969 + 3 ^ 40 * 6806877 * 2
def baseEnd_6806877 : Nat := 3495199657034469796133249

theorem tailTrace_6806877 : CollatzResearch.WordTrace tailWord_6806877 prefixEnd_6806877 3495199657034469796133249 := by
  unfold tailWord_6806877
  simp only [CollatzResearch.WordTrace]
  refine ⟨248267200160854625883602885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165511466773903083922401923 248267200160854625883602885)
  ·
    refine ⟨46550100030160242353175541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248267200160854625883602885 46550100030160242353175541)
    ·
      refine ⟨4364071877827522720610207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46550100030160242353175541 4364071877827522720610207)
      ·
        refine ⟨6546107816741284080915311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4364071877827522720610207 6546107816741284080915311)
        ·
          refine ⟨9819161725111926121372967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6546107816741284080915311 9819161725111926121372967)
          ·
            refine ⟨14728742587667889182059451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9819161725111926121372967 14728742587667889182059451)
            ·
              refine ⟨22093113881501833773089177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14728742587667889182059451 22093113881501833773089177)
              ·
                refine ⟨16569835411126375329816883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22093113881501833773089177 16569835411126375329816883)
                ·
                  refine ⟨24854753116689562994725325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16569835411126375329816883 24854753116689562994725325)
                  ·
                    refine ⟨9320532418758586123021997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24854753116689562994725325 9320532418758586123021997)
                    ·
                      refine ⟨3495199657034469796133249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9320532418758586123021997 3495199657034469796133249)
                      ·
                        rfl

theorem cell23_6806877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_6806877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806877 prefixEnd_6806877 := by exact prefixLift 6806877
  have htrace : WordTrace (prefixWord ++ tailWord_6806877) baseStart_6806877 baseEnd_6806877 := by
    simpa [prefixWord, tailWord_6806877, baseEnd_6806877] using wordTrace_append hprefix tailTrace_6806877
  have hstable : (prefixWord ++ tailWord_6806877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806877).length < 2 ^ (prefixWord ++ tailWord_6806877).sum := by decide
  have hdescent : baseEnd_6806877 < baseStart_6806877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806879 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 4]
def baseStart_6806879 : Nat := 118140960795 + 6806879 * 2 ^ 59
def prefixEnd_6806879 : Nat := 4983230072969 + 3 ^ 40 * 6806879 * 2
def baseEnd_6806879 : Nat := 3495200683995778788308239

theorem tailTrace_6806879 : CollatzResearch.WordTrace tailWord_6806879 prefixEnd_6806879 3495200683995778788308239 := by
  unfold tailWord_6806879
  simp only [CollatzResearch.WordTrace]
  refine ⟨248267273106847380225175691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165511515404564920150117127 248267273106847380225175691)
  ·
    refine ⟨372400909660271070337763537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248267273106847380225175691 372400909660271070337763537)
    ·
      refine ⟨279300682245203302753322653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372400909660271070337763537 279300682245203302753322653)
      ·
        refine ⟨104737755841951238532495995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279300682245203302753322653 104737755841951238532495995)
        ·
          refine ⟨157106633762926857798743993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104737755841951238532495995 157106633762926857798743993)
          ·
            refine ⟨117829975322195143349057995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157106633762926857798743993 117829975322195143349057995)
            ·
              refine ⟨176744962983292715023586993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117829975322195143349057995 176744962983292715023586993)
              ·
                refine ⟨132558722237469536267690245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176744962983292715023586993 132558722237469536267690245)
                ·
                  refine ⟨24854760419525538050191921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132558722237469536267690245 24854760419525538050191921)
                  ·
                    refine ⟨18641070314644153537643941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24854760419525538050191921 18641070314644153537643941)
                    ·
                      refine ⟨3495200683995778788308239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18641070314644153537643941 3495200683995778788308239)
                      ·
                        rfl

theorem cell23_6806879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_6806879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806879 prefixEnd_6806879 := by exact prefixLift 6806879
  have htrace : WordTrace (prefixWord ++ tailWord_6806879) baseStart_6806879 baseEnd_6806879 := by
    simpa [prefixWord, tailWord_6806879, baseEnd_6806879] using wordTrace_append hprefix tailTrace_6806879
  have hstable : (prefixWord ++ tailWord_6806879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806879).length < 2 ^ (prefixWord ++ tailWord_6806879).sum := by decide
  have hdescent : baseEnd_6806879 < baseStart_6806879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806883 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 1, 4, 2]
def baseStart_6806883 : Nat := 118140960795 + 6806883 * 2 ^ 59
def prefixEnd_6806883 : Nat := 4983230072969 + 3 ^ 40 * 6806883 * 2
def baseEnd_6806883 : Nat := 3495202737918396772658221

theorem tailTrace_6806883 : CollatzResearch.WordTrace tailWord_6806883 prefixEnd_6806883 3495202737918396772658221 := by
  unfold tailWord_6806883
  simp only [CollatzResearch.WordTrace]
  refine ⟨248267418998832888908321303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165511612665888592605547535 248267418998832888908321303)
  ·
    refine ⟨372401128498249333362481955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248267418998832888908321303 372401128498249333362481955)
    ·
      refine ⟨558601692747374000043722933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372401128498249333362481955 558601692747374000043722933)
      ·
        refine ⟨52368908695066312504099025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 558601692747374000043722933 52368908695066312504099025)
        ·
          refine ⟨39276681521299734378074269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52368908695066312504099025 39276681521299734378074269)
          ·
            refine ⟨14728755570487400391777851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39276681521299734378074269 14728755570487400391777851)
            ·
              refine ⟨22093133355731100587666777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14728755570487400391777851 22093133355731100587666777)
              ·
                refine ⟨16569850016798325440750083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22093133355731100587666777 16569850016798325440750083)
                ·
                  refine ⟨24854775025197488161125125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16569850016798325440750083 24854775025197488161125125)
                  ·
                    refine ⟨4660270317224529030210961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24854775025197488161125125 4660270317224529030210961)
                    ·
                      refine ⟨3495202737918396772658221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660270317224529030210961 3495202737918396772658221)
                      ·
                        rfl

theorem cell23_6806883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_6806883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806883 prefixEnd_6806883 := by exact prefixLift 6806883
  have htrace : WordTrace (prefixWord ++ tailWord_6806883) baseStart_6806883 baseEnd_6806883 := by
    simpa [prefixWord, tailWord_6806883, baseEnd_6806883] using wordTrace_append hprefix tailTrace_6806883
  have hstable : (prefixWord ++ tailWord_6806883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806883).length < 2 ^ (prefixWord ++ tailWord_6806883).sum := by decide
  have hdescent : baseEnd_6806883 < baseStart_6806883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806887 : List Nat := [1, 1, 5, 1, 4, 1, 3, 1, 1, 3, 2]
def baseStart_6806887 : Nat := 118140960795 + 6806887 * 2 ^ 59
def prefixEnd_6806887 : Nat := 4983230072969 + 3 ^ 40 * 6806887 * 2
def baseEnd_6806887 : Nat := 3495204791841014757008203

theorem tailTrace_6806887 : CollatzResearch.WordTrace tailWord_6806887 prefixEnd_6806887 3495204791841014757008203 := by
  unfold tailWord_6806887
  simp only [CollatzResearch.WordTrace]
  refine ⟨248267564890818397591466915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165511709927212265060977943 248267564890818397591466915)
  ·
    refine ⟨372401347336227596387200373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248267564890818397591466915 372401347336227596387200373)
    ·
      refine ⟨34912626312771337161300035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 372401347336227596387200373 34912626312771337161300035)
      ·
        refine ⟨52368939469157005741950053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34912626312771337161300035 52368939469157005741950053)
        ·
          refine ⟨9819176150466938576615635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52368939469157005741950053 9819176150466938576615635)
          ·
            refine ⟨14728764225700407864923453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9819176150466938576615635 14728764225700407864923453)
            ·
              refine ⟨5523286584637652949346295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14728764225700407864923453 5523286584637652949346295)
              ·
                refine ⟨8284929876956479424019443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523286584637652949346295 8284929876956479424019443)
                ·
                  refine ⟨12427394815434719136029165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8284929876956479424019443 12427394815434719136029165)
                  ·
                    refine ⟨4660273055788019676010937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12427394815434719136029165 4660273055788019676010937)
                    ·
                      refine ⟨3495204791841014757008203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660273055788019676010937 3495204791841014757008203)
                      ·
                        rfl

theorem cell23_6806887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_6806887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806887 prefixEnd_6806887 := by exact prefixLift 6806887
  have htrace : WordTrace (prefixWord ++ tailWord_6806887) baseStart_6806887 baseEnd_6806887 := by
    simpa [prefixWord, tailWord_6806887, baseEnd_6806887] using wordTrace_append hprefix tailTrace_6806887
  have hstable : (prefixWord ++ tailWord_6806887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806887).length < 2 ^ (prefixWord ++ tailWord_6806887).sum := by decide
  have hdescent : baseEnd_6806887 < baseStart_6806887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806906 : List Nat := [3, 1, 1, 1, 1, 1, 2, 8, 5]
def baseStart_6806906 : Nat := 118140960795 + 6806906 * 2 ^ 59
def prefixEnd_6806906 : Nat := 4983230072969 + 3 ^ 40 * 6806906 * 2
def baseEnd_6806906 : Nat := 388357171997050020296735

theorem tailTrace_6806906 : CollatzResearch.WordTrace tailWord_6806906 prefixEnd_6806906 388357171997050020296735 := by
  unfold tailWord_6806906
  simp only [CollatzResearch.WordTrace]
  refine ⟨62067064469437390959102143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165512171918499709224272381 62067064469437390959102143)
  ·
    refine ⟨93100596704156086438653215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62067064469437390959102143 93100596704156086438653215)
    ·
      refine ⟨139650895056234129657979823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93100596704156086438653215 139650895056234129657979823)
      ·
        refine ⟨209476342584351194486969735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139650895056234129657979823 209476342584351194486969735)
        ·
          refine ⟨314214513876526791730454603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209476342584351194486969735 314214513876526791730454603)
          ·
            refine ⟨471321770814790187595681905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314214513876526791730454603 471321770814790187595681905)
            ·
              refine ⟨353491328111092640696761429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471321770814790187595681905 353491328111092640696761429)
              ·
                refine ⟨4142476501301866883165173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 353491328111092640696761429 4142476501301866883165173)
                ·
                  refine ⟨388357171997050020296735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4142476501301866883165173 388357171997050020296735)
                  ·
                    rfl

theorem cell23_6806906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 5].length) (baseStart_6806906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806906 prefixEnd_6806906 := by exact prefixLift 6806906
  have htrace : WordTrace (prefixWord ++ tailWord_6806906) baseStart_6806906 baseEnd_6806906 := by
    simpa [prefixWord, tailWord_6806906, baseEnd_6806906] using wordTrace_append hprefix tailTrace_6806906
  have hstable : (prefixWord ++ tailWord_6806906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806906).length < 2 ^ (prefixWord ++ tailWord_6806906).sum := by decide
  have hdescent : baseEnd_6806906 < baseStart_6806906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806910 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_6806910 : Nat := 118140960795 + 6806910 * 2 ^ 59
def prefixEnd_6806910 : Nat := 4983230072969 + 3 ^ 40 * 6806910 * 2
def baseEnd_6806910 : Nat := 1165072200632022722340199

theorem tailTrace_6806910 : CollatzResearch.WordTrace tailWord_6806910 prefixEnd_6806910 1165072200632022722340199 := by
  unfold tailWord_6806910
  simp only [CollatzResearch.WordTrace]
  refine ⟨31033550471216884064944273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165512269179823381679702789 31033550471216884064944273)
  ·
    refine ⟨23275162853412663048708205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31033550471216884064944273 23275162853412663048708205)
    ·
      refine ⟨8728186070029748643265577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23275162853412663048708205 8728186070029748643265577)
      ·
        refine ⟨6546139552522311482449183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8728186070029748643265577 6546139552522311482449183)
        ·
          refine ⟨9819209328783467223673775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6546139552522311482449183 9819209328783467223673775)
          ·
            refine ⟨14728813993175200835510663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9819209328783467223673775 14728813993175200835510663)
            ·
              refine ⟨22093220989762801253265995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14728813993175200835510663 22093220989762801253265995)
              ·
                refine ⟨33139831484644201879898993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22093220989762801253265995 33139831484644201879898993)
                ·
                  refine ⟨24854873613483151409924245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33139831484644201879898993 24854873613483151409924245)
                  ·
                    refine ⟨1165072200632022722340199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24854873613483151409924245 1165072200632022722340199)
                    ·
                      rfl

theorem cell23_6806910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_6806910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806910 prefixEnd_6806910 := by exact prefixLift 6806910
  have htrace : WordTrace (prefixWord ++ tailWord_6806910) baseStart_6806910 baseEnd_6806910 := by
    simpa [prefixWord, tailWord_6806910, baseEnd_6806910] using wordTrace_append hprefix tailTrace_6806910
  have hstable : (prefixWord ++ tailWord_6806910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806910).length < 2 ^ (prefixWord ++ tailWord_6806910).sum := by decide
  have hdescent : baseEnd_6806910 < baseStart_6806910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806913 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_6806913 : Nat := 118140960795 + 6806913 * 2 ^ 59
def prefixEnd_6806913 : Nat := 4983230072969 + 3 ^ 40 * 6806913 * 2
def baseEnd_6806913 : Nat := 3495218142338031655283083

theorem tailTrace_6806913 : CollatzResearch.WordTrace tailWord_6806913 prefixEnd_6806913 3495218142338031655283083 := by
  unfold tailWord_6806913
  simp only [CollatzResearch.WordTrace]
  refine ⟨248268513188724204031913393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165512342125816136021275595 248268513188724204031913393)
  ·
    refine ⟨186201384891543153023935045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248268513188724204031913393 186201384891543153023935045)
    ·
      refine ⟨34912759667164341191987821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186201384891543153023935045 34912759667164341191987821)
      ·
        refine ⟨13092284875186627946995433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34912759667164341191987821 13092284875186627946995433)
        ·
          refine ⟨9819213656389970960246575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13092284875186627946995433 9819213656389970960246575)
          ·
            refine ⟨14728820484584956440369863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9819213656389970960246575 14728820484584956440369863)
            ·
              refine ⟨22093230726877434660554795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14728820484584956440369863 22093230726877434660554795)
              ·
                refine ⟨33139846090316151990832193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22093230726877434660554795 33139846090316151990832193)
                ·
                  refine ⟨24854884567737113993124145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33139846090316151990832193 24854884567737113993124145)
                  ·
                    refine ⟨18641163425802835494843109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24854884567737113993124145 18641163425802835494843109)
                    ·
                      refine ⟨3495218142338031655283083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18641163425802835494843109 3495218142338031655283083)
                      ·
                        rfl

theorem cell23_6806913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_6806913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806913 prefixEnd_6806913 := by exact prefixLift 6806913
  have htrace : WordTrace (prefixWord ++ tailWord_6806913) baseStart_6806913 baseEnd_6806913 := by
    simpa [prefixWord, tailWord_6806913, baseEnd_6806913] using wordTrace_append hprefix tailTrace_6806913
  have hstable : (prefixWord ++ tailWord_6806913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806913).length < 2 ^ (prefixWord ++ tailWord_6806913).sum := by decide
  have hdescent : baseEnd_6806913 < baseStart_6806913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806916 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_6806916 : Nat := 118140960795 + 6806916 * 2 ^ 59
def prefixEnd_6806916 : Nat := 4983230072969 + 3 ^ 40 * 6806916 * 2
def baseEnd_6806916 : Nat := 3495219682779995143545569

theorem tailTrace_6806916 : CollatzResearch.WordTrace tailWord_6806916 prefixEnd_6806916 3495219682779995143545569 := by
  unfold tailWord_6806916
  simp only [CollatzResearch.WordTrace]
  refine ⟨124134311303856667772136301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165512415071808890362848401 124134311303856667772136301)
  ·
    refine ⟨46550366738946250414551113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124134311303856667772136301 46550366738946250414551113)
    ·
      refine ⟨34912775054209687810913335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46550366738946250414551113 34912775054209687810913335)
      ·
        refine ⟨52369162581314531716370003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34912775054209687810913335 52369162581314531716370003)
        ·
          refine ⟨78553743871971797574555005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52369162581314531716370003 78553743871971797574555005)
          ·
            refine ⟨29457653951989424090458127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78553743871971797574555005 29457653951989424090458127)
            ·
              refine ⟨44186480927984136135687191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29457653951989424090458127 44186480927984136135687191)
              ·
                refine ⟨66279721391976204203530787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44186480927984136135687191 66279721391976204203530787)
                ·
                  refine ⟨99419582087964306305296181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66279721391976204203530787 99419582087964306305296181)
                  ·
                    refine ⟨9320585820746653716121517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99419582087964306305296181 9320585820746653716121517)
                    ·
                      refine ⟨3495219682779995143545569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9320585820746653716121517 3495219682779995143545569)
                      ·
                        rfl

theorem cell23_6806916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_6806916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806916 prefixEnd_6806916 := by exact prefixLift 6806916
  have htrace : WordTrace (prefixWord ++ tailWord_6806916) baseStart_6806916 baseEnd_6806916 := by
    simpa [prefixWord, tailWord_6806916, baseEnd_6806916] using wordTrace_append hprefix tailTrace_6806916
  have hstable : (prefixWord ++ tailWord_6806916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806916).length < 2 ^ (prefixWord ++ tailWord_6806916).sum := by decide
  have hdescent : baseEnd_6806916 < baseStart_6806916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806939 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 4]
def baseStart_6806939 : Nat := 118140960795 + 6806939 * 2 ^ 59
def prefixEnd_6806939 : Nat := 4983230072969 + 3 ^ 40 * 6806939 * 2
def baseEnd_6806939 : Nat := 3495231492835048553557963

theorem tailTrace_6806939 : CollatzResearch.WordTrace tailWord_6806939 prefixEnd_6806939 3495231492835048553557963 := by
  unfold tailWord_6806939
  simp only [CollatzResearch.WordTrace]
  refine ⟨248269461486630010472359871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165512974324420006981573247 248269461486630010472359871)
  ·
    refine ⟨372404192229945015708539807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248269461486630010472359871 372404192229945015708539807)
    ·
      refine ⟨558606288344917523562809711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372404192229945015708539807 558606288344917523562809711)
      ·
        refine ⟨837909432517376285344214567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558606288344917523562809711 837909432517376285344214567)
        ·
          refine ⟨1256864148776064428016321851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837909432517376285344214567 1256864148776064428016321851)
          ·
            refine ⟨1885296223164096642024482777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256864148776064428016321851 1885296223164096642024482777)
            ·
              refine ⟨1413972167373072481518362083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1885296223164096642024482777 1413972167373072481518362083)
              ·
                refine ⟨2120958251059608722277543125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1413972167373072481518362083 2120958251059608722277543125)
                ·
                  refine ⟨49709959009209579428379917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2120958251059608722277543125 49709959009209579428379917)
                  ·
                    refine ⟨18641234628453592285642469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49709959009209579428379917 18641234628453592285642469)
                    ·
                      refine ⟨3495231492835048553557963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18641234628453592285642469 3495231492835048553557963)
                      ·
                        rfl

theorem cell23_6806939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 4].length) (baseStart_6806939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806939 prefixEnd_6806939 := by exact prefixLift 6806939
  have htrace : WordTrace (prefixWord ++ tailWord_6806939) baseStart_6806939 baseEnd_6806939 := by
    simpa [prefixWord, tailWord_6806939, baseEnd_6806939] using wordTrace_append hprefix tailTrace_6806939
  have hstable : (prefixWord ++ tailWord_6806939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806939).length < 2 ^ (prefixWord ++ tailWord_6806939).sum := by decide
  have hdescent : baseEnd_6806939 < baseStart_6806939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806956 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 4]
def baseStart_6806956 : Nat := 118140960795 + 6806956 * 2 ^ 59
def prefixEnd_6806956 : Nat := 4983230072969 + 3 ^ 40 * 6806956 * 2
def baseEnd_6806956 : Nat := 3495240222006174987045385

theorem tailTrace_6806956 : CollatzResearch.WordTrace tailWord_6806956 prefixEnd_6806956 3495240222006174987045385 := by
  unfold tailWord_6806956
  simp only [CollatzResearch.WordTrace]
  refine ⟨124135040763784211187864361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165513387685045614917152481 124135040763784211187864361)
  ·
    refine ⟨93101280572838158390898271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124135040763784211187864361 93101280572838158390898271)
    ·
      refine ⟨139651920859257237586347407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93101280572838158390898271 139651920859257237586347407)
      ·
        refine ⟨209477881288885856379521111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139651920859257237586347407 209477881288885856379521111)
        ·
          refine ⟨314216821933328784569281667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209477881288885856379521111 314216821933328784569281667)
          ·
            refine ⟨471325232899993176853922501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314216821933328784569281667 471325232899993176853922501)
            ·
              refine ⟨88373481168748720660110469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 471325232899993176853922501 88373481168748720660110469)
              ·
                refine ⟨16570027719140385123770713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88373481168748720660110469 16570027719140385123770713)
                ·
                  refine ⟨12427520789355288842828035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16570027719140385123770713 12427520789355288842828035)
                  ·
                    refine ⟨18641281184032933264242053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12427520789355288842828035 18641281184032933264242053)
                    ·
                      refine ⟨3495240222006174987045385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18641281184032933264242053 3495240222006174987045385)
                      ·
                        rfl

theorem cell23_6806956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_6806956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806956 prefixEnd_6806956 := by exact prefixLift 6806956
  have htrace : WordTrace (prefixWord ++ tailWord_6806956) baseStart_6806956 baseEnd_6806956 := by
    simpa [prefixWord, tailWord_6806956, baseEnd_6806956] using wordTrace_append hprefix tailTrace_6806956
  have hstable : (prefixWord ++ tailWord_6806956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806956).length < 2 ^ (prefixWord ++ tailWord_6806956).sum := by decide
  have hdescent : baseEnd_6806956 < baseStart_6806956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806959 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 5]
def baseStart_6806959 : Nat := 118140960795 + 6806959 * 2 ^ 59
def prefixEnd_6806959 : Nat := 4983230072969 + 3 ^ 40 * 6806959 * 2
def baseEnd_6806959 : Nat := 3495241762448138475307871

theorem tailTrace_6806959 : CollatzResearch.WordTrace tailWord_6806959 prefixEnd_6806959 3495241762448138475307871 := by
  unfold tailWord_6806959
  simp only [CollatzResearch.WordTrace]
  refine ⟨248270190946557553888087931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165513460631038369258725287 248270190946557553888087931)
  ·
    refine ⟨372405286419836330832131897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248270190946557553888087931 372405286419836330832131897)
    ·
      refine ⟨279303964814877248124098923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372405286419836330832131897 279303964814877248124098923)
      ·
        refine ⟨418955947222315872186148385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279303964814877248124098923 418955947222315872186148385)
        ·
          refine ⟨314216960416736904139611289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418955947222315872186148385 314216960416736904139611289)
          ·
            refine ⟨235662720312552678104708467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314216960416736904139611289 235662720312552678104708467)
            ·
              refine ⟨353494080468829017157062701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235662720312552678104708467 353494080468829017157062701)
              ·
                refine ⟨132560280175810881433898513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353494080468829017157062701 132560280175810881433898513)
                ·
                  refine ⟨99420210131858161075423885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132560280175810881433898513 99420210131858161075423885)
                  ·
                    refine ⟨37282578799446810403283957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99420210131858161075423885 37282578799446810403283957)
                    ·
                      refine ⟨3495241762448138475307871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37282578799446810403283957 3495241762448138475307871)
                      ·
                        rfl

theorem cell23_6806959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_6806959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806959 prefixEnd_6806959 := by exact prefixLift 6806959
  have htrace : WordTrace (prefixWord ++ tailWord_6806959) baseStart_6806959 baseEnd_6806959 := by
    simpa [prefixWord, tailWord_6806959, baseEnd_6806959] using wordTrace_append hprefix tailTrace_6806959
  have hstable : (prefixWord ++ tailWord_6806959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806959).length < 2 ^ (prefixWord ++ tailWord_6806959).sum := by decide
  have hdescent : baseEnd_6806959 < baseStart_6806959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806973 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 2, 4, 2]
def baseStart_6806973 : Nat := 118140960795 + 6806973 * 2 ^ 59
def prefixEnd_6806973 : Nat := 4983230072969 + 3 ^ 40 * 6806973 * 2
def baseEnd_6806973 : Nat := 3495248951177301420532807

theorem tailTrace_6806973 : CollatzResearch.WordTrace tailWord_6806973 prefixEnd_6806973 3495248951177301420532807 := by
  unfold tailWord_6806973
  simp only [CollatzResearch.WordTrace]
  refine ⟨248270701568506834279097573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165513801045671222852731715 248270701568506834279097573)
  ·
    refine ⟨46550756544095031427330795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248270701568506834279097573 46550756544095031427330795)
    ·
      refine ⟨69826134816142547140996193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46550756544095031427330795 69826134816142547140996193)
      ·
        refine ⟨52369601112106910355747145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69826134816142547140996193 52369601112106910355747145)
        ·
          refine ⟨39277200834080182766810359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52369601112106910355747145 39277200834080182766810359)
          ·
            refine ⟨58915801251120274150215539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39277200834080182766810359 58915801251120274150215539)
            ·
              refine ⟨88373701876680411225323309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58915801251120274150215539 88373701876680411225323309)
              ·
                refine ⟨33140138203755154209496241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88373701876680411225323309 33140138203755154209496241)
                ·
                  refine ⟨24855103652816365657122181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33140138203755154209496241 24855103652816365657122181)
                  ·
                    refine ⟨4660331934903068560710409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24855103652816365657122181 4660331934903068560710409)
                    ·
                      refine ⟨3495248951177301420532807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660331934903068560710409 3495248951177301420532807)
                      ·
                        rfl

theorem cell23_6806973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_6806973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806973 prefixEnd_6806973 := by exact prefixLift 6806973
  have htrace : WordTrace (prefixWord ++ tailWord_6806973) baseStart_6806973 baseEnd_6806973 := by
    simpa [prefixWord, tailWord_6806973, baseEnd_6806973] using wordTrace_append hprefix tailTrace_6806973
  have hstable : (prefixWord ++ tailWord_6806973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806973).length < 2 ^ (prefixWord ++ tailWord_6806973).sum := by decide
  have hdescent : baseEnd_6806973 < baseStart_6806973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6806976 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 3]
def baseStart_6806976 : Nat := 118140960795 + 6806976 * 2 ^ 59
def prefixEnd_6806976 : Nat := 4983230072969 + 3 ^ 40 * 6806976 * 2
def baseEnd_6806976 : Nat := 3495250491619264908795293

theorem tailTrace_6806976 : CollatzResearch.WordTrace tailWord_6806976 prefixEnd_6806976 3495250491619264908795293 := by
  unfold tailWord_6806976
  simp only [CollatzResearch.WordTrace]
  refine ⟨124135405493747982895728391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165513873991663977194304521 124135405493747982895728391)
  ·
    refine ⟨186203108240621974343592587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124135405493747982895728391 186203108240621974343592587)
    ·
      refine ⟨279304662360932961515388881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186203108240621974343592587 279304662360932961515388881)
      ·
        refine ⟨209478496770699721136541661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279304662360932961515388881 209478496770699721136541661)
        ·
          refine ⟨78554436289012395426203123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209478496770699721136541661 78554436289012395426203123)
          ·
            refine ⟨117831654433518593139304685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78554436289012395426203123 117831654433518593139304685)
            ·
              refine ⟨44186870412569472427239257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117831654433518593139304685 44186870412569472427239257)
              ·
                refine ⟨33140152809427104320429443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44186870412569472427239257 33140152809427104320429443)
                ·
                  refine ⟨49710229214140656480644165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33140152809427104320429443 49710229214140656480644165)
                  ·
                    refine ⟨9320667977651373090120781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49710229214140656480644165 9320667977651373090120781)
                    ·
                      refine ⟨3495250491619264908795293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9320667977651373090120781 3495250491619264908795293)
                      ·
                        rfl

theorem cell23_6806976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_6806976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6806976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6806976 prefixEnd_6806976 := by exact prefixLift 6806976
  have htrace : WordTrace (prefixWord ++ tailWord_6806976) baseStart_6806976 baseEnd_6806976 := by
    simpa [prefixWord, tailWord_6806976, baseEnd_6806976] using wordTrace_append hprefix tailTrace_6806976
  have hstable : (prefixWord ++ tailWord_6806976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6806976).length < 2 ^ (prefixWord ++ tailWord_6806976).sum := by decide
  have hdescent : baseEnd_6806976 < baseStart_6806976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6806976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807000 : List Nat := [2, 1, 2, 2, 2, 1, 5, 3, 1, 4]
def baseStart_6807000 : Nat := 118140960795 + 6807000 * 2 ^ 59
def prefixEnd_6807000 : Nat := 4983230072969 + 3 ^ 40 * 6807000 * 2
def baseEnd_6807000 : Nat := 1165087605051657604965061

theorem tailTrace_6807000 : CollatzResearch.WordTrace tailWord_6807000 prefixEnd_6807000 1165087605051657604965061 := by
  unfold tailWord_6807000
  simp only [CollatzResearch.WordTrace]
  refine ⟨124135843169704508945165227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165514457559606011926886969 124135843169704508945165227)
  ·
    refine ⟨186203764754556763417747841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124135843169704508945165227 186203764754556763417747841)
    ·
      refine ⟨139652823565917572563310881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186203764754556763417747841 139652823565917572563310881)
      ·
        refine ⟨104739617674438179422483161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139652823565917572563310881 104739617674438179422483161)
        ·
          refine ⟨78554713255828634566862371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104739617674438179422483161 78554713255828634566862371)
          ·
            refine ⟨117832069883742951850293557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78554713255828634566862371 117832069883742951850293557)
            ·
              refine ⟨11046756551600901735965021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117832069883742951850293557 11046756551600901735965021)
              ·
                refine ⟨4142533706850338150986883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11046756551600901735965021 4142533706850338150986883)
                ·
                  refine ⟨6213800560275507226480325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142533706850338150986883 6213800560275507226480325)
                  ·
                    refine ⟨1165087605051657604965061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6213800560275507226480325 1165087605051657604965061)
                    ·
                      rfl

theorem cell23_6807000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 1, 4].length) (baseStart_6807000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807000 prefixEnd_6807000 := by exact prefixLift 6807000
  have htrace : WordTrace (prefixWord ++ tailWord_6807000) baseStart_6807000 baseEnd_6807000 := by
    simpa [prefixWord, tailWord_6807000, baseEnd_6807000] using wordTrace_append hprefix tailTrace_6807000
  have hstable : (prefixWord ++ tailWord_6807000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807000).length < 2 ^ (prefixWord ++ tailWord_6807000).sum := by decide
  have hdescent : baseEnd_6807000 < baseStart_6807000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807030 : List Nat := [5, 1, 1, 1, 2, 2, 4, 1, 6]
def baseStart_6807030 : Nat := 118140960795 + 6807030 * 2 ^ 59
def prefixEnd_6807030 : Nat := 4983230072969 + 3 ^ 40 * 6807030 * 2
def baseEnd_6807030 : Nat := 388364246619400855280005

theorem tailTrace_6807030 : CollatzResearch.WordTrace tailWord_6807030 prefixEnd_6807030 388364246619400855280005 := by
  unfold tailWord_6807030
  simp only [CollatzResearch.WordTrace]
  refine ⟨15517048783081270813370159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165515187019533555342615029 15517048783081270813370159)
  ·
    refine ⟨23275573174621906220055239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15517048783081270813370159 23275573174621906220055239)
    ·
      refine ⟨34913359761932859330082859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23275573174621906220055239 34913359761932859330082859)
      ·
        refine ⟨52370039642899288995124289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34913359761932859330082859 52370039642899288995124289)
        ·
          refine ⟨39277529732174466746343217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52370039642899288995124289 39277529732174466746343217)
          ·
            refine ⟨29458147299130850059757413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39277529732174466746343217 29458147299130850059757413)
            ·
              refine ⟨5523402618587034386204515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29458147299130850059757413 5523402618587034386204515)
              ·
                refine ⟨8285103927880551579306773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523402618587034386204515 8285103927880551579306773)
                ·
                  refine ⟨388364246619400855280005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8285103927880551579306773 388364246619400855280005)
                  ·
                    rfl

theorem cell23_6807030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_6807030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807030 prefixEnd_6807030 := by exact prefixLift 6807030
  have htrace : WordTrace (prefixWord ++ tailWord_6807030) baseStart_6807030 baseEnd_6807030 := by
    simpa [prefixWord, tailWord_6807030, baseEnd_6807030] using wordTrace_append hprefix tailTrace_6807030
  have hstable : (prefixWord ++ tailWord_6807030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807030).length < 2 ^ (prefixWord ++ tailWord_6807030).sum := by decide
  have hdescent : baseEnd_6807030 < baseStart_6807030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807033 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 6, 3, 2]
def baseStart_6807033 : Nat := 118140960795 + 6807033 * 2 ^ 59
def prefixEnd_6807033 : Nat := 4983230072969 + 3 ^ 40 * 6807033 * 2
def baseEnd_6807033 : Nat := 3495279760016571185782531

theorem tailTrace_6807033 : CollatzResearch.WordTrace tailWord_6807033 prefixEnd_6807033 3495279760016571185782531 := by
  unfold tailWord_6807033
  simp only [CollatzResearch.WordTrace]
  refine ⟨248272889948289464526281753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165515259965526309684187835 248272889948289464526281753)
  ·
    refine ⟨186204667461217098394711315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248272889948289464526281753 186204667461217098394711315)
    ·
      refine ⟨279307001191825647592066973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186204667461217098394711315 279307001191825647592066973)
      ·
        refine ⟨104740125446934617847025115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279307001191825647592066973 104740125446934617847025115)
        ·
          refine ⟨157110188170401926770537673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104740125446934617847025115 157110188170401926770537673)
          ·
            refine ⟨117832641127801445077903255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157110188170401926770537673 117832641127801445077903255)
            ·
              refine ⟨176748961691702167616854883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117832641127801445077903255 176748961691702167616854883)
              ·
                refine ⟨265123442537553251425282325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176748961691702167616854883 265123442537553251425282325)
                ·
                  refine ⟨12427661368947808660560109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 265123442537553251425282325 12427661368947808660560109)
                  ·
                    refine ⟨4660373013355428247710041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12427661368947808660560109 4660373013355428247710041)
                    ·
                      refine ⟨3495279760016571185782531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660373013355428247710041 3495279760016571185782531)
                      ·
                        rfl

theorem cell23_6807033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_6807033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807033 prefixEnd_6807033 := by exact prefixLift 6807033
  have htrace : WordTrace (prefixWord ++ tailWord_6807033) baseStart_6807033 baseEnd_6807033 := by
    simpa [prefixWord, tailWord_6807033, baseEnd_6807033] using wordTrace_append hprefix tailTrace_6807033
  have hstable : (prefixWord ++ tailWord_6807033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807033).length < 2 ^ (prefixWord ++ tailWord_6807033).sum := by decide
  have hdescent : baseEnd_6807033 < baseStart_6807033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807050 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 2, 3, 2]
def baseStart_6807050 : Nat := 118140960795 + 6807050 * 2 ^ 59
def prefixEnd_6807050 : Nat := 4983230072969 + 3 ^ 40 * 6807050 * 2
def baseEnd_6807050 : Nat := 3495288489187697619269953

theorem tailTrace_6807050 : CollatzResearch.WordTrace tailWord_6807050 prefixEnd_6807050 3495288489187697619269953 := by
  unfold tailWord_6807050
  simp only [CollatzResearch.WordTrace]
  refine ⟨62068377497306969107412651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165515673326151917619767069 62068377497306969107412651)
  ·
    refine ⟨93102566245960453661118977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62068377497306969107412651 93102566245960453661118977)
    ·
      refine ⟨69826924684470340245839233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93102566245960453661118977 69826924684470340245839233)
      ·
        refine ⟨52370193513352755184379425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69826924684470340245839233 52370193513352755184379425)
        ·
          refine ⟨39277645135014566388284569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52370193513352755184379425 39277645135014566388284569)
          ·
            refine ⟨29458233851260924791213427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39277645135014566388284569 29458233851260924791213427)
            ·
              refine ⟨44187350776891387186820141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29458233851260924791213427 44187350776891387186820141)
              ·
                refine ⟨16570256541334270195057553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44187350776891387186820141 16570256541334270195057553)
                ·
                  refine ⟨12427692406000702646293165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16570256541334270195057553 12427692406000702646293165)
                  ·
                    refine ⟨4660384652250263492359937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12427692406000702646293165 4660384652250263492359937)
                    ·
                      refine ⟨3495288489187697619269953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660384652250263492359937 3495288489187697619269953)
                      ·
                        rfl

theorem cell23_6807050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_6807050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807050 prefixEnd_6807050 := by exact prefixLift 6807050
  have htrace : WordTrace (prefixWord ++ tailWord_6807050) baseStart_6807050 baseEnd_6807050 := by
    simpa [prefixWord, tailWord_6807050, baseEnd_6807050] using wordTrace_append hprefix tailTrace_6807050
  have hstable : (prefixWord ++ tailWord_6807050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807050).length < 2 ^ (prefixWord ++ tailWord_6807050).sum := by decide
  have hdescent : baseEnd_6807050 < baseStart_6807050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807074 : List Nat := [3, 3, 1, 1, 1, 1, 6, 2, 1, 1, 3]
def baseStart_6807074 : Nat := 118140960795 + 6807074 * 2 ^ 59
def prefixEnd_6807074 : Nat := 4983230072969 + 3 ^ 40 * 6807074 * 2
def baseEnd_6807074 : Nat := 3495300812723405525369843

theorem tailTrace_6807074 : CollatzResearch.WordTrace tailWord_6807074 prefixEnd_6807074 3495300812723405525369843 := by
  unfold tailWord_6807074
  simp only [CollatzResearch.WordTrace]
  refine ⟨62068596335285232132131069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165516256894093952352349517 62068596335285232132131069)
  ·
    refine ⟨23275723625731962049549151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62068596335285232132131069 23275723625731962049549151)
    ·
      refine ⟨34913585438597943074323727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23275723625731962049549151 34913585438597943074323727)
      ·
        refine ⟨52370378157896914611485591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34913585438597943074323727 52370378157896914611485591)
        ·
          refine ⟨78555567236845371917228387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52370378157896914611485591 78555567236845371917228387)
          ·
            refine ⟨117833350855268057875842581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78555567236845371917228387 117833350855268057875842581)
            ·
              refine ⟨5523438321340690212930121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117833350855268057875842581 5523438321340690212930121)
              ·
                refine ⟨4142578741005517659697591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5523438321340690212930121 4142578741005517659697591)
                ·
                  refine ⟨6213868111508276489546387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142578741005517659697591 6213868111508276489546387)
                  ·
                    refine ⟨9320802167262414734319581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6213868111508276489546387 9320802167262414734319581)
                    ·
                      refine ⟨3495300812723405525369843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9320802167262414734319581 3495300812723405525369843)
                      ·
                        rfl

theorem cell23_6807074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_6807074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807074 prefixEnd_6807074 := by exact prefixLift 6807074
  have htrace : WordTrace (prefixWord ++ tailWord_6807074) baseStart_6807074 baseEnd_6807074 := by
    simpa [prefixWord, tailWord_6807074, baseEnd_6807074] using wordTrace_append hprefix tailTrace_6807074
  have hstable : (prefixWord ++ tailWord_6807074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807074).length < 2 ^ (prefixWord ++ tailWord_6807074).sum := by decide
  have hdescent : baseEnd_6807074 < baseStart_6807074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807093 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_6807093 : Nat := 118140960795 + 6807093 * 2 ^ 59
def prefixEnd_6807093 : Nat := 4983230072969 + 3 ^ 40 * 6807093 * 2
def baseEnd_6807093 : Nat := 3495310568855840951032255

theorem tailTrace_6807093 : CollatzResearch.WordTrace tailWord_6807093 prefixEnd_6807093 3495310568855840951032255 := by
  unfold tailWord_6807093
  simp only [CollatzResearch.WordTrace]
  refine ⟨248275078328072094773465933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165516718885381396515643955 248275078328072094773465933)
  ·
    refine ⟨93103154373027035540049725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248275078328072094773465933 93103154373027035540049725)
    ·
      refine ⟨34913682889885138327518647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93103154373027035540049725 34913682889885138327518647)
      ·
        refine ⟨52370524334827707491277971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34913682889885138327518647 52370524334827707491277971)
        ·
          refine ⟨78555786502241561236916957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52370524334827707491277971 78555786502241561236916957)
          ·
            refine ⟨29458419938340585463843859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78555786502241561236916957 29458419938340585463843859)
            ·
              refine ⟨44187629907510878195765789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29458419938340585463843859 44187629907510878195765789)
              ·
                refine ⟨16570361215316579323412171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44187629907510878195765789 16570361215316579323412171)
                ·
                  refine ⟨24855541822974868985118257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16570361215316579323412171 24855541822974868985118257)
                  ·
                    refine ⟨18641656367231151738838693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24855541822974868985118257 18641656367231151738838693)
                    ·
                      refine ⟨3495310568855840951032255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18641656367231151738838693 3495310568855840951032255)
                      ·
                        rfl

theorem cell23_6807093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_6807093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807093 prefixEnd_6807093 := by exact prefixLift 6807093
  have htrace : WordTrace (prefixWord ++ tailWord_6807093) baseStart_6807093 baseEnd_6807093 := by
    simpa [prefixWord, tailWord_6807093, baseEnd_6807093] using wordTrace_append hprefix tailTrace_6807093
  have hstable : (prefixWord ++ tailWord_6807093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807093).length < 2 ^ (prefixWord ++ tailWord_6807093).sum := by decide
  have hdescent : baseEnd_6807093 < baseStart_6807093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807097 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 3, 2, 2]
def baseStart_6807097 : Nat := 118140960795 + 6807097 * 2 ^ 59
def prefixEnd_6807097 : Nat := 4983230072969 + 3 ^ 40 * 6807097 * 2
def baseEnd_6807097 : Nat := 3495312622778458935382237

theorem tailTrace_6807097 : CollatzResearch.WordTrace tailWord_6807097 prefixEnd_6807097 3495312622778458935382237 := by
  unfold tailWord_6807097
  simp only [CollatzResearch.WordTrace]
  refine ⟨248275224220057603456611545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165516816146705068971074363 248275224220057603456611545)
  ·
    refine ⟨186206418165043202592458659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248275224220057603456611545 186206418165043202592458659)
    ·
      refine ⟨279309627247564803888687989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186206418165043202592458659 279309627247564803888687989)
      ·
        refine ⟨26185277554459200364564499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279309627247564803888687989 26185277554459200364564499)
        ·
          refine ⟨39277916331688800546846749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26185277554459200364564499 39277916331688800546846749)
          ·
            refine ⟨14729218624383300205067531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39277916331688800546846749 14729218624383300205067531)
            ·
              refine ⟨22093827936574950307601297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14729218624383300205067531 22093827936574950307601297)
              ·
                refine ⟨16570370952431212730700973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22093827936574950307601297 16570370952431212730700973)
                ·
                  refine ⟨6213889107161704774012865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16570370952431212730700973 6213889107161704774012865)
                  ·
                    refine ⟨4660416830371278580509649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6213889107161704774012865 4660416830371278580509649)
                    ·
                      refine ⟨3495312622778458935382237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660416830371278580509649 3495312622778458935382237)
                      ·
                        rfl

theorem cell23_6807097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_6807097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807097 prefixEnd_6807097 := by exact prefixLift 6807097
  have htrace : WordTrace (prefixWord ++ tailWord_6807097) baseStart_6807097 baseEnd_6807097 := by
    simpa [prefixWord, tailWord_6807097, baseEnd_6807097] using wordTrace_append hprefix tailTrace_6807097
  have hstable : (prefixWord ++ tailWord_6807097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807097).length < 2 ^ (prefixWord ++ tailWord_6807097).sum := by decide
  have hdescent : baseEnd_6807097 < baseStart_6807097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807103 : List Nat := [1, 1, 2, 2, 3, 4, 3, 7]
def baseStart_6807103 : Nat := 118140960795 + 6807103 * 2 ^ 59
def prefixEnd_6807103 : Nat := 4983230072969 + 3 ^ 40 * 6807103 * 2
def baseEnd_6807103 : Nat := 129456137172680959700267

theorem tailTrace_6807103 : CollatzResearch.WordTrace tailWord_6807103 prefixEnd_6807103 129456137172680959700267 := by
  unfold tailWord_6807103
  simp only [CollatzResearch.WordTrace]
  refine ⟨248275443058035866481329963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165516962038690577654219975 248275443058035866481329963)
  ·
    refine ⟨372413164587053799721994945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248275443058035866481329963 372413164587053799721994945)
    ·
      refine ⟨279309873440290349791496209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372413164587053799721994945 279309873440290349791496209)
      ·
        refine ⟨209482405080217762343622157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279309873440290349791496209 209482405080217762343622157)
        ·
          refine ⟨78555901905081660878858309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209482405080217762343622157 78555901905081660878858309)
          ·
            refine ⟨14729231607202811414785933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78555901905081660878858309 14729231607202811414785933)
            ·
              refine ⟨5523461852701054280544725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14729231607202811414785933 5523461852701054280544725)
              ·
                refine ⟨129456137172680959700267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5523461852701054280544725 129456137172680959700267)
                ·
                  rfl

theorem cell23_6807103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 7].length) (baseStart_6807103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807103 prefixEnd_6807103 := by exact prefixLift 6807103
  have htrace : WordTrace (prefixWord ++ tailWord_6807103) baseStart_6807103 baseEnd_6807103 := by
    simpa [prefixWord, tailWord_6807103, baseEnd_6807103] using wordTrace_append hprefix tailTrace_6807103
  have hstable : (prefixWord ++ tailWord_6807103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807103).length < 2 ^ (prefixWord ++ tailWord_6807103).sum := by decide
  have hdescent : baseEnd_6807103 < baseStart_6807103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807114 : List Nat := [3, 1, 2, 1, 1, 3, 4, 3, 1, 2, 2]
def baseStart_6807114 : Nat := 118140960795 + 6807114 * 2 ^ 59
def prefixEnd_6807114 : Nat := 4983230072969 + 3 ^ 40 * 6807114 * 2
def baseEnd_6807114 : Nat := 3495321351949585368869659

theorem tailTrace_6807114 : CollatzResearch.WordTrace tailWord_6807114 prefixEnd_6807114 3495321351949585368869659 := by
  unfold tailWord_6807114
  simp only [CollatzResearch.WordTrace]
  refine ⟨62068961065249003839995099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165517229507330676906653597 62068961065249003839995099)
  ·
    refine ⟨93103441597873505759992649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62068961065249003839995099 93103441597873505759992649)
    ·
      refine ⟨69827581198405129319994487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93103441597873505759992649 69827581198405129319994487)
      ·
        refine ⟨104741371797607693979991731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69827581198405129319994487 104741371797607693979991731)
        ·
          refine ⟨157112057696411540969987597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104741371797607693979991731 157112057696411540969987597)
          ·
            refine ⟨58917021636154327863745349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157112057696411540969987597 58917021636154327863745349)
            ·
              refine ⟨11046941556778936474452253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58917021636154327863745349 11046941556778936474452253)
              ·
                refine ⟨4142603083792101177919595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11046941556778936474452253 4142603083792101177919595)
                ·
                  refine ⟨6213904625688151766879393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142603083792101177919595 6213904625688151766879393)
                  ·
                    refine ⟨4660428469266113825159545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6213904625688151766879393 4660428469266113825159545)
                    ·
                      refine ⟨3495321351949585368869659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660428469266113825159545 3495321351949585368869659)
                      ·
                        rfl

theorem cell23_6807114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_6807114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807114 prefixEnd_6807114 := by exact prefixLift 6807114
  have htrace : WordTrace (prefixWord ++ tailWord_6807114) baseStart_6807114 baseEnd_6807114 := by
    simpa [prefixWord, tailWord_6807114, baseEnd_6807114] using wordTrace_append hprefix tailTrace_6807114
  have hstable : (prefixWord ++ tailWord_6807114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807114).length < 2 ^ (prefixWord ++ tailWord_6807114).sum := by decide
  have hdescent : baseEnd_6807114 < baseStart_6807114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807173 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 2, 1, 5]
def baseStart_6807173 : Nat := 118140960795 + 6807173 * 2 ^ 59
def prefixEnd_6807173 : Nat := 4983230072969 + 3 ^ 40 * 6807173 * 2
def baseEnd_6807173 : Nat := 3495351647308200638031887

theorem tailTrace_6807173 : CollatzResearch.WordTrace tailWord_6807173 prefixEnd_6807173 3495351647308200638031887 := by
  unfold tailWord_6807173
  simp only [CollatzResearch.WordTrace]
  refine ⟨248277996167782268436378173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165518664111854845624252115 248277996167782268436378173)
  ·
    refine ⟨93104248562918350663641815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248277996167782268436378173 93104248562918350663641815)
    ·
      refine ⟨139656372844377525995462723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93104248562918350663641815 139656372844377525995462723)
      ·
        refine ⟨209484559266566288993194085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139656372844377525995462723 209484559266566288993194085)
        ·
          refine ⟨39278354862481179186223891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209484559266566288993194085 39278354862481179186223891)
          ·
            refine ⟨58917532293721768779335837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39278354862481179186223891 58917532293721768779335837)
            ·
              refine ⟨22094074610145663292250939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58917532293721768779335837 22094074610145663292250939)
              ·
                refine ⟨33141111915218494938376409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22094074610145663292250939 33141111915218494938376409)
                ·
                  refine ⟨24855833936413871203782307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33141111915218494938376409 24855833936413871203782307)
                  ·
                    refine ⟨37283750904620806805673461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24855833936413871203782307 37283750904620806805673461)
                    ·
                      refine ⟨3495351647308200638031887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37283750904620806805673461 3495351647308200638031887)
                      ·
                        rfl

theorem cell23_6807173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_6807173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807173 prefixEnd_6807173 := by exact prefixLift 6807173
  have htrace : WordTrace (prefixWord ++ tailWord_6807173) baseStart_6807173 baseEnd_6807173 := by
    simpa [prefixWord, tailWord_6807173, baseEnd_6807173] using wordTrace_append hprefix tailTrace_6807173
  have hstable : (prefixWord ++ tailWord_6807173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807173).length < 2 ^ (prefixWord ++ tailWord_6807173).sum := by decide
  have hdescent : baseEnd_6807173 < baseStart_6807173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807203 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 3]
def baseStart_6807203 : Nat := 118140960795 + 6807203 * 2 ^ 59
def prefixEnd_6807203 : Nat := 4983230072969 + 3 ^ 40 * 6807203 * 2
def baseEnd_6807203 : Nat := 3495367051727835520656749

theorem tailTrace_6807203 : CollatzResearch.WordTrace tailWord_6807203 prefixEnd_6807203 3495367051727835520656749 := by
  unfold tailWord_6807203
  simp only [CollatzResearch.WordTrace]
  refine ⟨248279090357673583559970263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165519393571782389039980175 248279090357673583559970263)
  ·
    refine ⟨372418635536510375339955395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248279090357673583559970263 372418635536510375339955395)
    ·
      refine ⟨558627953304765563009933093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372418635536510375339955395 558627953304765563009933093)
      ·
        refine ⟨104742741244643543064362455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 558627953304765563009933093 104742741244643543064362455)
        ·
          refine ⟨157114111866965314596543683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104742741244643543064362455 157114111866965314596543683)
          ·
            refine ⟨235671167800447971894815525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157114111866965314596543683 235671167800447971894815525)
            ·
              refine ⟨44188343962583994730277911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235671167800447971894815525 44188343962583994730277911)
              ·
                refine ⟨66282515943875992095416867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44188343962583994730277911 66282515943875992095416867)
                ·
                  refine ⟨99423773915813988143125301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66282515943875992095416867 99423773915813988143125301)
                  ·
                    refine ⟨9320978804607561388417997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99423773915813988143125301 9320978804607561388417997)
                    ·
                      refine ⟨3495367051727835520656749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9320978804607561388417997 3495367051727835520656749)
                      ·
                        rfl

theorem cell23_6807203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_6807203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807203 prefixEnd_6807203 := by exact prefixLift 6807203
  have htrace : WordTrace (prefixWord ++ tailWord_6807203) baseStart_6807203 baseEnd_6807203 := by
    simpa [prefixWord, tailWord_6807203, baseEnd_6807203] using wordTrace_append hprefix tailTrace_6807203
  have hstable : (prefixWord ++ tailWord_6807203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807203).length < 2 ^ (prefixWord ++ tailWord_6807203).sum := by decide
  have hdescent : baseEnd_6807203 < baseStart_6807203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807204 : List Nat := [2, 3, 1, 2, 2, 3, 1, 3, 2, 2, 2]
def baseStart_6807204 : Nat := 118140960795 + 6807204 * 2 ^ 59
def prefixEnd_6807204 : Nat := 4983230072969 + 3 ^ 40 * 6807204 * 2
def baseEnd_6807204 : Nat := 3495367565208490016744245

theorem tailTrace_6807204 : CollatzResearch.WordTrace tailWord_6807204 prefixEnd_6807204 3495367565208490016744245 := by
  unfold tailWord_6807204
  simp only [CollatzResearch.WordTrace]
  refine ⟨124139563415334980365378333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165519417887113307153837777 124139563415334980365378333)
  ·
    refine ⟨46552336280750617637016875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124139563415334980365378333 46552336280750617637016875)
    ·
      refine ⟨69828504421125926455525313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46552336280750617637016875 69828504421125926455525313)
      ·
        refine ⟨52371378315844444841643985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69828504421125926455525313 52371378315844444841643985)
        ·
          refine ⟨39278533736883333631232989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52371378315844444841643985 39278533736883333631232989)
          ·
            refine ⟨14729450151331250111712371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39278533736883333631232989 14729450151331250111712371)
            ·
              refine ⟨22094175226996875167568557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14729450151331250111712371 22094175226996875167568557)
              ·
                refine ⟨8285315710123828187838209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22094175226996875167568557 8285315710123828187838209)
                ·
                  refine ⟨6213986782592871140878657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8285315710123828187838209 6213986782592871140878657)
                  ·
                    refine ⟨4660490086944653355658993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6213986782592871140878657 4660490086944653355658993)
                    ·
                      refine ⟨3495367565208490016744245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660490086944653355658993 3495367565208490016744245)
                      ·
                        rfl

theorem cell23_6807204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_6807204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807204 prefixEnd_6807204 := by exact prefixLift 6807204
  have htrace : WordTrace (prefixWord ++ tailWord_6807204) baseStart_6807204 baseEnd_6807204 := by
    simpa [prefixWord, tailWord_6807204, baseEnd_6807204] using wordTrace_append hprefix tailTrace_6807204
  have hstable : (prefixWord ++ tailWord_6807204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807204).length < 2 ^ (prefixWord ++ tailWord_6807204).sum := by decide
  have hdescent : baseEnd_6807204 < baseStart_6807204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807238 : List Nat := [6, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_6807238 : Nat := 118140960795 + 6807238 * 2 ^ 59
def prefixEnd_6807238 : Nat := 4983230072969 + 3 ^ 40 * 6807238 * 2
def baseEnd_6807238 : Nat := 3495385023550742883719089

theorem tailTrace_6807238 : CollatzResearch.WordTrace tailWord_6807238 prefixEnd_6807238 3495385023550742883719089 := by
  unfold tailWord_6807238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7758761466017087016796699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 165520244608364523024996245 7758761466017087016796699)
  ·
    refine ⟨11638142199025630525195049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7758761466017087016796699 11638142199025630525195049)
    ·
      refine ⟨8728606649269222893896287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11638142199025630525195049 8728606649269222893896287)
      ·
        refine ⟨13092909973903834340844431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8728606649269222893896287 13092909973903834340844431)
        ·
          refine ⟨19639364960855751511266647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13092909973903834340844431 19639364960855751511266647)
          ·
            refine ⟨29459047441283627266899971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19639364960855751511266647 29459047441283627266899971)
            ·
              refine ⟨44188571161925440900349957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29459047441283627266899971 44188571161925440900349957)
              ·
                refine ⟨8285357092861020168815617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44188571161925440900349957 8285357092861020168815617)
                ·
                  refine ⟨6214017819645765126611713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8285357092861020168815617 6214017819645765126611713)
                  ·
                    refine ⟨4660513364734323844958785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6214017819645765126611713 4660513364734323844958785)
                    ·
                      refine ⟨3495385023550742883719089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660513364734323844958785 3495385023550742883719089)
                      ·
                        rfl

theorem cell23_6807238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_6807238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807238 prefixEnd_6807238 := by exact prefixLift 6807238
  have htrace : WordTrace (prefixWord ++ tailWord_6807238) baseStart_6807238 baseEnd_6807238 := by
    simpa [prefixWord, tailWord_6807238, baseEnd_6807238] using wordTrace_append hprefix tailTrace_6807238
  have hstable : (prefixWord ++ tailWord_6807238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807238).length < 2 ^ (prefixWord ++ tailWord_6807238).sum := by decide
  have hdescent : baseEnd_6807238 < baseStart_6807238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807250 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_6807250 : Nat := 118140960795 + 6807250 * 2 ^ 59
def prefixEnd_6807250 : Nat := 4983230072969 + 3 ^ 40 * 6807250 * 2
def baseEnd_6807250 : Nat := 3495391185318596836769033

theorem tailTrace_6807250 : CollatzResearch.WordTrace tailWord_6807250 prefixEnd_6807250 3495391185318596836769033 := by
  unfold tailWord_6807250
  simp only [CollatzResearch.WordTrace]
  refine ⟨62070201147125827646732801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165520536392335540391287469 62070201147125827646732801)
  ·
    refine ⟨46552650860344370735049601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62070201147125827646732801 46552650860344370735049601)
    ·
      refine ⟨34914488145258278051287201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46552650860344370735049601 34914488145258278051287201)
      ·
        refine ⟨26185866108943708538465401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34914488145258278051287201 26185866108943708538465401)
        ·
          refine ⟨19639399581707781403849051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26185866108943708538465401 19639399581707781403849051)
          ·
            refine ⟨29459099372561672105773577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19639399581707781403849051 29459099372561672105773577)
            ·
              refine ⟨22094324529421254079330183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29459099372561672105773577 22094324529421254079330183)
              ·
                refine ⟨33141486794131881118995275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22094324529421254079330183 33141486794131881118995275)
                ·
                  refine ⟨49712230191197821678492913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33141486794131881118995275 49712230191197821678492913)
                  ·
                    refine ⟨37284172643398366258869685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49712230191197821678492913 37284172643398366258869685)
                    ·
                      refine ⟨3495391185318596836769033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37284172643398366258869685 3495391185318596836769033)
                      ·
                        rfl

theorem cell23_6807250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_6807250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807250 prefixEnd_6807250 := by exact prefixLift 6807250
  have htrace : WordTrace (prefixWord ++ tailWord_6807250) baseStart_6807250 baseEnd_6807250 := by
    simpa [prefixWord, tailWord_6807250, baseEnd_6807250] using wordTrace_append hprefix tailTrace_6807250
  have hstable : (prefixWord ++ tailWord_6807250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807250).length < 2 ^ (prefixWord ++ tailWord_6807250).sum := by decide
  have hdescent : baseEnd_6807250 < baseStart_6807250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807277 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_6807277 : Nat := 118140960795 + 6807277 * 2 ^ 59
def prefixEnd_6807277 : Nat := 4983230072969 + 3 ^ 40 * 6807277 * 2
def baseEnd_6807277 : Nat := 3495405049296268231131409

theorem tailTrace_6807277 : CollatzResearch.WordTrace tailWord_6807277 prefixEnd_6807277 3495405049296268231131409 := by
  unfold tailWord_6807277
  simp only [CollatzResearch.WordTrace]
  refine ⟨248281789359405494198164085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165521192906270329465442723 248281789359405494198164085)
  ·
    refine ⟨23276417752444265081077883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 248281789359405494198164085 23276417752444265081077883)
    ·
      refine ⟨34914626628666397621616825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23276417752444265081077883 34914626628666397621616825)
      ·
        refine ⟨26185969971499798216212619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34914626628666397621616825 26185969971499798216212619)
        ·
          refine ⟨39278954957249697324318929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26185969971499798216212619 39278954957249697324318929)
          ·
            refine ⟨29459216217937272993239197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39278954957249697324318929 29459216217937272993239197)
            ·
              refine ⟨11047206081726477372464699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29459216217937272993239197 11047206081726477372464699)
              ·
                refine ⟨16570809122589716058697049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11047206081726477372464699 16570809122589716058697049)
                ·
                  refine ⟨12428106841942287044022787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16570809122589716058697049 12428106841942287044022787)
                  ·
                    refine ⟨18642160262913430566034181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12428106841942287044022787 18642160262913430566034181)
                    ·
                      refine ⟨3495405049296268231131409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18642160262913430566034181 3495405049296268231131409)
                      ·
                        rfl

theorem cell23_6807277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_6807277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807277 prefixEnd_6807277 := by exact prefixLift 6807277
  have htrace : WordTrace (prefixWord ++ tailWord_6807277) baseStart_6807277 baseEnd_6807277 := by
    simpa [prefixWord, tailWord_6807277, baseEnd_6807277] using wordTrace_append hprefix tailTrace_6807277
  have hstable : (prefixWord ++ tailWord_6807277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807277).length < 2 ^ (prefixWord ++ tailWord_6807277).sum := by decide
  have hdescent : baseEnd_6807277 < baseStart_6807277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807280 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 3]
def baseStart_6807280 : Nat := 118140960795 + 6807280 * 2 ^ 59
def prefixEnd_6807280 : Nat := 4983230072969 + 3 ^ 40 * 6807280 * 2
def baseEnd_6807280 : Nat := 3495406589738231719393895

theorem tailTrace_6807280 : CollatzResearch.WordTrace tailWord_6807280 prefixEnd_6807280 3495406589738231719393895 := by
  unfold tailWord_6807280
  simp only [CollatzResearch.WordTrace]
  refine ⟨124140949389197312855261647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165521265852263083807015529 124140949389197312855261647)
  ·
    refine ⟨186211424083795969282892471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124140949389197312855261647 186211424083795969282892471)
    ·
      refine ⟨279317136125693953924338707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186211424083795969282892471 279317136125693953924338707)
      ·
        refine ⟨418975704188540930886508061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279317136125693953924338707 418975704188540930886508061)
        ·
          refine ⟨157115889070702849082440523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418975704188540930886508061 157115889070702849082440523)
          ·
            refine ⟨235673833606054273623660785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157115889070702849082440523 235673833606054273623660785)
            ·
              refine ⟨176755375204540705217745589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235673833606054273623660785 176755375204540705217745589)
              ·
                refine ⟨16570816425425691114163649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176755375204540705217745589 16570816425425691114163649)
                ·
                  refine ⟨12428112319069268335622737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16570816425425691114163649 12428112319069268335622737)
                  ·
                    refine ⟨9321084239301951251717053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12428112319069268335622737 9321084239301951251717053)
                    ·
                      refine ⟨3495406589738231719393895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9321084239301951251717053 3495406589738231719393895)
                      ·
                        rfl

theorem cell23_6807280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 3].length) (baseStart_6807280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807280 prefixEnd_6807280 := by exact prefixLift 6807280
  have htrace : WordTrace (prefixWord ++ tailWord_6807280) baseStart_6807280 baseEnd_6807280 := by
    simpa [prefixWord, tailWord_6807280, baseEnd_6807280] using wordTrace_append hprefix tailTrace_6807280
  have hstable : (prefixWord ++ tailWord_6807280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807280).length < 2 ^ (prefixWord ++ tailWord_6807280).sum := by decide
  have hdescent : baseEnd_6807280 < baseStart_6807280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807287 : List Nat := [1, 1, 3, 1, 1, 1, 5, 5, 1, 4]
def baseStart_6807287 : Nat := 118140960795 + 6807287 * 2 ^ 59
def prefixEnd_6807287 : Nat := 4983230072969 + 3 ^ 40 * 6807287 * 2
def baseEnd_6807287 : Nat := 1165136728034271064002121

theorem tailTrace_6807287 : CollatzResearch.WordTrace tailWord_6807287 prefixEnd_6807287 1165136728034271064002121 := by
  unfold tailWord_6807287
  simp only [CollatzResearch.WordTrace]
  refine ⟨248282154089369265906028115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165521436059579510604018743 248282154089369265906028115)
  ·
    refine ⟨372423231134053898859042173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248282154089369265906028115 372423231134053898859042173)
    ·
      refine ⟨139658711675270212072140815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372423231134053898859042173 139658711675270212072140815)
      ·
        refine ⟨209488067512905318108211223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139658711675270212072140815 209488067512905318108211223)
        ·
          refine ⟨314232101269357977162316835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209488067512905318108211223 314232101269357977162316835)
          ·
            refine ⟨471348151904036965743475253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314232101269357977162316835 471348151904036965743475253)
            ·
              refine ⟨44188889241003465538450805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 471348151904036965743475253 44188889241003465538450805)
              ·
                refine ⟨4142708366344074894229763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44188889241003465538450805 4142708366344074894229763)
                ·
                  refine ⟨6214062549516112341344645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142708366344074894229763 6214062549516112341344645)
                  ·
                    refine ⟨1165136728034271064002121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6214062549516112341344645 1165136728034271064002121)
                    ·
                      rfl

theorem cell23_6807287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 1, 4].length) (baseStart_6807287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807287 prefixEnd_6807287 := by exact prefixLift 6807287
  have htrace : WordTrace (prefixWord ++ tailWord_6807287) baseStart_6807287 baseEnd_6807287 := by
    simpa [prefixWord, tailWord_6807287, baseEnd_6807287] using wordTrace_append hprefix tailTrace_6807287
  have hstable : (prefixWord ++ tailWord_6807287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807287).length < 2 ^ (prefixWord ++ tailWord_6807287).sum := by decide
  have hdescent : baseEnd_6807287 < baseStart_6807287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807300 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 8]
def baseStart_6807300 : Nat := 118140960795 + 6807300 * 2 ^ 59
def prefixEnd_6807300 : Nat := 4983230072969 + 3 ^ 40 * 6807300 * 2
def baseEnd_6807300 : Nat := 388379651039035737904867

theorem tailTrace_6807300 : CollatzResearch.WordTrace tailWord_6807300 prefixEnd_6807300 388379651039035737904867 := by
  unfold tailWord_6807300
  simp only [CollatzResearch.WordTrace]
  refine ⟨124141314119161084563125677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165521752158881446084167569 124141314119161084563125677)
  ·
    refine ⟨46552992794685406711172129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124141314119161084563125677 46552992794685406711172129)
    ·
      refine ⟨34914744596014055033379097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46552992794685406711172129 34914744596014055033379097)
      ·
        refine ⟨26186058447010541275034323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34914744596014055033379097 26186058447010541275034323)
        ·
          refine ⟨39279087670515811912551485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26186058447010541275034323 39279087670515811912551485)
          ·
            refine ⟨14729657876443429467206807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39279087670515811912551485 14729657876443429467206807)
            ·
              refine ⟨22094486814665144200810211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14729657876443429467206807 22094486814665144200810211)
              ·
                refine ⟨33141730221997716301215317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22094486814665144200810211 33141730221997716301215317)
                ·
                  refine ⟨388379651039035737904867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33141730221997716301215317 388379651039035737904867)
                  ·
                    rfl

theorem cell23_6807300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_6807300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807300 prefixEnd_6807300 := by exact prefixLift 6807300
  have htrace : WordTrace (prefixWord ++ tailWord_6807300) baseStart_6807300 baseEnd_6807300 := by
    simpa [prefixWord, tailWord_6807300, baseEnd_6807300] using wordTrace_append hprefix tailTrace_6807300
  have hstable : (prefixWord ++ tailWord_6807300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807300).length < 2 ^ (prefixWord ++ tailWord_6807300).sum := by decide
  have hdescent : baseEnd_6807300 < baseStart_6807300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807317 : List Nat := [1, 3, 2, 1, 2, 4, 3, 1, 6]
def baseStart_6807317 : Nat := 118140960795 + 6807317 * 2 ^ 59
def prefixEnd_6807317 : Nat := 4983230072969 + 3 ^ 40 * 6807317 * 2
def baseEnd_6807317 : Nat := 388380620946938674959025

theorem tailTrace_6807317 : CollatzResearch.WordTrace tailWord_6807317 prefixEnd_6807317 388380620946938674959025 := by
  unfold tailWord_6807317
  simp only [CollatzResearch.WordTrace]
  refine ⟨248283248279260581029620205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165522165519507054019746803 248283248279260581029620205)
  ·
    refine ⟨93106218104722717886107577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248283248279260581029620205 93106218104722717886107577)
    ·
      refine ⟨69829663578542038414580683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93106218104722717886107577 69829663578542038414580683)
      ·
        refine ⟨104744495367813057621871025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69829663578542038414580683 104744495367813057621871025)
        ·
          refine ⟨78558371525859793216403269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104744495367813057621871025 78558371525859793216403269)
          ·
            refine ⟨14729694661098711228075613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78558371525859793216403269 14729694661098711228075613)
            ·
              refine ⟨5523635497912016710528355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14729694661098711228075613 5523635497912016710528355)
              ·
                refine ⟨8285453246868025065792533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523635497912016710528355 8285453246868025065792533)
                ·
                  refine ⟨388380620946938674959025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8285453246868025065792533 388380620946938674959025)
                  ·
                    rfl

theorem cell23_6807317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 6].length) (baseStart_6807317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807317 prefixEnd_6807317 := by exact prefixLift 6807317
  have htrace : WordTrace (prefixWord ++ tailWord_6807317) baseStart_6807317 baseEnd_6807317 := by
    simpa [prefixWord, tailWord_6807317, baseEnd_6807317] using wordTrace_append hprefix tailTrace_6807317
  have hstable : (prefixWord ++ tailWord_6807317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807317).length < 2 ^ (prefixWord ++ tailWord_6807317).sum := by decide
  have hdescent : baseEnd_6807317 < baseStart_6807317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807327 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 3, 1, 3]
def baseStart_6807327 : Nat := 118140960795 + 6807327 * 2 ^ 59
def prefixEnd_6807327 : Nat := 4983230072969 + 3 ^ 40 * 6807327 * 2
def baseEnd_6807327 : Nat := 3495430723328993035506179

theorem tailTrace_6807327 : CollatzResearch.WordTrace tailWord_6807327 prefixEnd_6807327 3495430723328993035506179 := by
  unfold tailWord_6807327
  simp only [CollatzResearch.WordTrace]
  refine ⟨248283613009224352737484235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165522408672816235158322823 248283613009224352737484235)
  ·
    refine ⟨372425419513836529106226353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248283613009224352737484235 372425419513836529106226353)
    ·
      refine ⟨279319064635377396829669765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372425419513836529106226353 279319064635377396829669765)
      ·
        refine ⟨52372324619133261905563081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279319064635377396829669765 52372324619133261905563081)
        ·
          refine ⟨39279243464349946429172311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52372324619133261905563081 39279243464349946429172311)
          ·
            refine ⟨58918865196524919643758467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39279243464349946429172311 58918865196524919643758467)
            ·
              refine ⟨88378297794787379465637701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58918865196524919643758467 88378297794787379465637701)
              ·
                refine ⟨16570930836522633649807069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88378297794787379465637701 16570930836522633649807069)
                ·
                  refine ⟨6214099063695987618677651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16570930836522633649807069 6214099063695987618677651)
                  ·
                    refine ⟨9321148595543981428016477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6214099063695987618677651 9321148595543981428016477)
                    ·
                      refine ⟨3495430723328993035506179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9321148595543981428016477 3495430723328993035506179)
                      ·
                        rfl

theorem cell23_6807327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_6807327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807327 prefixEnd_6807327 := by exact prefixLift 6807327
  have htrace : WordTrace (prefixWord ++ tailWord_6807327) baseStart_6807327 baseEnd_6807327 := by
    simpa [prefixWord, tailWord_6807327, baseEnd_6807327] using wordTrace_append hprefix tailTrace_6807327
  have hstable : (prefixWord ++ tailWord_6807327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807327).length < 2 ^ (prefixWord ++ tailWord_6807327).sum := by decide
  have hdescent : baseEnd_6807327 < baseStart_6807327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807354 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2]
def baseStart_6807354 : Nat := 118140960795 + 6807354 * 2 ^ 59
def prefixEnd_6807354 : Nat := 4983230072969 + 3 ^ 40 * 6807354 * 2
def baseEnd_6807354 : Nat := 3495444587306664429868555

theorem tailTrace_6807354 : CollatzResearch.WordTrace tailWord_6807354 prefixEnd_6807354 3495444587306664429868555 := by
  unfold tailWord_6807354
  simp only [CollatzResearch.WordTrace]
  refine ⟨62071149445031634087179279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165523065186751024232478077 62071149445031634087179279)
  ·
    refine ⟨93106724167547451130768919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62071149445031634087179279 93106724167547451130768919)
    ·
      refine ⟨139660086251321176696153379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93106724167547451130768919 139660086251321176696153379)
      ·
        refine ⟨209490129376981765044230069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139660086251321176696153379 209490129376981765044230069)
        ·
          refine ⟨19639699629092040472896569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 209490129376981765044230069 19639699629092040472896569)
          ·
            refine ⟨14729774721819030354672427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19639699629092040472896569 14729774721819030354672427)
            ·
              refine ⟨22094662082728545532008641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14729774721819030354672427 22094662082728545532008641)
              ·
                refine ⟨16570996562046409149006481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22094662082728545532008641 16570996562046409149006481)
                ·
                  refine ⟨12428247421534806861754861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16570996562046409149006481 12428247421534806861754861)
                  ·
                    refine ⟨4660592783075552573158073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12428247421534806861754861 4660592783075552573158073)
                    ·
                      refine ⟨3495444587306664429868555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660592783075552573158073 3495444587306664429868555)
                      ·
                        rfl

theorem cell23_6807354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2].length) (baseStart_6807354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807354 prefixEnd_6807354 := by exact prefixLift 6807354
  have htrace : WordTrace (prefixWord ++ tailWord_6807354) baseStart_6807354 baseEnd_6807354 := by
    simpa [prefixWord, tailWord_6807354, baseEnd_6807354] using wordTrace_append hprefix tailTrace_6807354
  have hstable : (prefixWord ++ tailWord_6807354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807354).length < 2 ^ (prefixWord ++ tailWord_6807354).sum := by decide
  have hdescent : baseEnd_6807354 < baseStart_6807354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807370 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_6807370 : Nat := 118140960795 + 6807370 * 2 ^ 59
def prefixEnd_6807370 : Nat := 4983230072969 + 3 ^ 40 * 6807370 * 2
def baseEnd_6807370 : Nat := 3495452802997136367268481

theorem tailTrace_6807370 : CollatzResearch.WordTrace tailWord_6807370 prefixEnd_6807370 3495452802997136367268481 := by
  unfold tailWord_6807370
  simp only [CollatzResearch.WordTrace]
  refine ⟨62071295337017142770324891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165523454232045714054199709 62071295337017142770324891)
  ·
    refine ⟨93106943005525714155487337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62071295337017142770324891 93106943005525714155487337)
    ·
      refine ⟨69830207254144285616615503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93106943005525714155487337 69830207254144285616615503)
      ·
        refine ⟨104745310881216428424923255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69830207254144285616615503 104745310881216428424923255)
        ·
          refine ⟨157117966321824642637384883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104745310881216428424923255 157117966321824642637384883)
          ·
            refine ⟨235676949482736963956077325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157117966321824642637384883 235676949482736963956077325)
            ·
              refine ⟨88378856056026361483528997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235676949482736963956077325 88378856056026361483528997)
              ·
                refine ⟨16571035510504942778161687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88378856056026361483528997 16571035510504942778161687)
                ·
                  refine ⟨24856553265757414167242531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16571035510504942778161687 24856553265757414167242531)
                  ·
                    refine ⟨37284829898636121250863797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24856553265757414167242531 37284829898636121250863797)
                    ·
                      refine ⟨3495452802997136367268481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37284829898636121250863797 3495452802997136367268481)
                      ·
                        rfl

theorem cell23_6807370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_6807370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807370 prefixEnd_6807370 := by exact prefixLift 6807370
  have htrace : WordTrace (prefixWord ++ tailWord_6807370) baseStart_6807370 baseEnd_6807370 := by
    simpa [prefixWord, tailWord_6807370, baseEnd_6807370] using wordTrace_append hprefix tailTrace_6807370
  have hstable : (prefixWord ++ tailWord_6807370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807370).length < 2 ^ (prefixWord ++ tailWord_6807370).sum := by decide
  have hdescent : baseEnd_6807370 < baseStart_6807370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807418 : List Nat := [3, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2]
def baseStart_6807418 : Nat := 118140960795 + 6807418 * 2 ^ 59
def prefixEnd_6807418 : Nat := 4983230072969 + 3 ^ 40 * 6807418 * 2
def baseEnd_6807418 : Nat := 3495477450068552179468261

theorem tailTrace_6807418 : CollatzResearch.WordTrace tailWord_6807418 prefixEnd_6807418 3495477450068552179468261 := by
  unfold tailWord_6807418
  simp only [CollatzResearch.WordTrace]
  refine ⟨62071733012973668819761727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165524621367929783519364605 62071733012973668819761727)
  ·
    refine ⟨93107599519460503229642591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62071733012973668819761727 93107599519460503229642591)
    ·
      refine ⟨139661399279190754844463887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93107599519460503229642591 139661399279190754844463887)
      ·
        refine ⟨209492098918786132266695831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139661399279190754844463887 209492098918786132266695831)
        ·
          refine ⟨314238148378179198400043747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209492098918786132266695831 314238148378179198400043747)
          ·
            refine ⟨471357222567268797600065621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314238148378179198400043747 471357222567268797600065621)
            ·
              refine ⟨5523717451960181221875769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 471357222567268797600065621 5523717451960181221875769)
              ·
                refine ⟨4142788088970135916406827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5523717451960181221875769 4142788088970135916406827)
                ·
                  refine ⟨6214182133455203874610241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142788088970135916406827 6214182133455203874610241)
                  ·
                    refine ⟨4660636600091402905957681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6214182133455203874610241 4660636600091402905957681)
                    ·
                      refine ⟨3495477450068552179468261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660636600091402905957681 3495477450068552179468261)
                      ·
                        rfl

theorem cell23_6807418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2].length) (baseStart_6807418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807418 prefixEnd_6807418 := by exact prefixLift 6807418
  have htrace : WordTrace (prefixWord ++ tailWord_6807418) baseStart_6807418 baseEnd_6807418 := by
    simpa [prefixWord, tailWord_6807418, baseEnd_6807418] using wordTrace_append hprefix tailTrace_6807418
  have hstable : (prefixWord ++ tailWord_6807418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807418).length < 2 ^ (prefixWord ++ tailWord_6807418).sum := by decide
  have hdescent : baseEnd_6807418 < baseStart_6807418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807520 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 7]
def baseStart_6807520 : Nat := 118140960795 + 6807520 * 2 ^ 59
def prefixEnd_6807520 : Nat := 4983230072969 + 3 ^ 40 * 6807520 * 2
def baseEnd_6807520 : Nat := 3495529825095310780392791

theorem tailTrace_6807520 : CollatzResearch.WordTrace tailWord_6807520 prefixEnd_6807520 3495529825095310780392791 := by
  unfold tailWord_6807520
  simp only [CollatzResearch.WordTrace]
  refine ⟨124145326148762573349630007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165527101531683431132840009 124145326148762573349630007)
  ·
    refine ⟨186217989223143860024445011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124145326148762573349630007 186217989223143860024445011)
    ·
      refine ⟨279326983834715790036667517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186217989223143860024445011 279326983834715790036667517)
      ·
        refine ⟨104747618938018421263750319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279326983834715790036667517 104747618938018421263750319)
        ·
          refine ⟨157121428407027631895625479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104747618938018421263750319 157121428407027631895625479)
          ·
            refine ⟨235682142610541447843438219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157121428407027631895625479 235682142610541447843438219)
            ·
              refine ⟨353523213915812171765157329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235682142610541447843438219 353523213915812171765157329)
              ·
                refine ⟨265142410436859128823867997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353523213915812171765157329 265142410436859128823867997)
                ·
                  refine ⟨99428403913822173308950499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265142410436859128823867997 99428403913822173308950499)
                  ·
                    refine ⟨149142605870733259963425749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99428403913822173308950499 149142605870733259963425749)
                    ·
                      refine ⟨3495529825095310780392791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149142605870733259963425749 3495529825095310780392791)
                      ·
                        rfl

theorem cell23_6807520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_6807520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807520 prefixEnd_6807520 := by exact prefixLift 6807520
  have htrace : WordTrace (prefixWord ++ tailWord_6807520) baseStart_6807520 baseEnd_6807520 := by
    simpa [prefixWord, tailWord_6807520, baseEnd_6807520] using wordTrace_append hprefix tailTrace_6807520
  have hstable : (prefixWord ++ tailWord_6807520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807520).length < 2 ^ (prefixWord ++ tailWord_6807520).sum := by decide
  have hdescent : baseEnd_6807520 < baseStart_6807520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807542 : List Nat := [5, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2]
def baseStart_6807542 : Nat := 118140960795 + 6807542 * 2 ^ 59
def prefixEnd_6807542 : Nat := 4983230072969 + 3 ^ 40 * 6807542 * 2
def baseEnd_6807542 : Nat := 3495541121669709694317691

theorem tailTrace_6807542 : CollatzResearch.WordTrace tailWord_6807542 prefixEnd_6807542 3495541121669709694317691 := by
  unfold tailWord_6807542
  simp only [CollatzResearch.WordTrace]
  refine ⟨15518215918965340278535055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165527636468963629637707253 15518215918965340278535055)
  ·
    refine ⟨23277323878448010417802583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15518215918965340278535055 23277323878448010417802583)
    ·
      refine ⟨34915985817672015626703875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23277323878448010417802583 34915985817672015626703875)
      ·
        refine ⟨52373978726508023440055813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34915985817672015626703875 52373978726508023440055813)
        ·
          refine ⟨9820121011220254395010465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52373978726508023440055813 9820121011220254395010465)
          ·
            refine ⟨7365090758415190796257849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9820121011220254395010465 7365090758415190796257849)
            ·
              refine ⟨5523818068811393097193387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7365090758415190796257849 5523818068811393097193387)
              ·
                refine ⟨8285727103217089645790081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523818068811393097193387 8285727103217089645790081)
                ·
                  refine ⟨6214295327412817234342561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8285727103217089645790081 6214295327412817234342561)
                  ·
                    refine ⟨4660721495559612925756921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6214295327412817234342561 4660721495559612925756921)
                    ·
                      refine ⟨3495541121669709694317691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660721495559612925756921 3495541121669709694317691)
                      ·
                        rfl

theorem cell23_6807542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_6807542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807542 prefixEnd_6807542 := by exact prefixLift 6807542
  have htrace : WordTrace (prefixWord ++ tailWord_6807542) baseStart_6807542 baseEnd_6807542 := by
    simpa [prefixWord, tailWord_6807542, baseEnd_6807542] using wordTrace_append hprefix tailTrace_6807542
  have hstable : (prefixWord ++ tailWord_6807542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807542).length < 2 ^ (prefixWord ++ tailWord_6807542).sum := by decide
  have hdescent : baseEnd_6807542 < baseStart_6807542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807564 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 2, 1, 4]
def baseStart_6807564 : Nat := 118140960795 + 6807564 * 2 ^ 59
def prefixEnd_6807564 : Nat := 4983230072969 + 3 ^ 40 * 6807564 * 2
def baseEnd_6807564 : Nat := 3495552418244108608242589

theorem tailTrace_6807564 : CollatzResearch.WordTrace tailWord_6807564 prefixEnd_6807564 3495552418244108608242589 := by
  unfold tailWord_6807564
  simp only [CollatzResearch.WordTrace]
  refine ⟨124146128554682871106930873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165528171406243828142574497 124146128554682871106930873)
  ·
    refine ⟨93109596416012153330198155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124146128554682871106930873 93109596416012153330198155)
    ·
      refine ⟨139664394624018229995297233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93109596416012153330198155 139664394624018229995297233)
      ·
        refine ⟨104748295968013672496472925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139664394624018229995297233 104748295968013672496472925)
        ·
          refine ⟨39280610988005127186177347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104748295968013672496472925 39280610988005127186177347)
          ·
            refine ⟨58920916482007690779266021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39280610988005127186177347 58920916482007690779266021)
            ·
              refine ⟨11047671840376442021112379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58920916482007690779266021 11047671840376442021112379)
              ·
                refine ⟨16571507760564663031668569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11047671840376442021112379 16571507760564663031668569)
                ·
                  refine ⟨12428630820423497273751427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16571507760564663031668569 12428630820423497273751427)
                  ·
                    refine ⟨18642946230635245910627141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12428630820423497273751427 18642946230635245910627141)
                    ·
                      refine ⟨3495552418244108608242589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18642946230635245910627141 3495552418244108608242589)
                      ·
                        rfl

theorem cell23_6807564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_6807564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807564 prefixEnd_6807564 := by exact prefixLift 6807564
  have htrace : WordTrace (prefixWord ++ tailWord_6807564) baseStart_6807564 baseEnd_6807564 := by
    simpa [prefixWord, tailWord_6807564, baseEnd_6807564] using wordTrace_append hprefix tailTrace_6807564
  have hstable : (prefixWord ++ tailWord_6807564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807564).length < 2 ^ (prefixWord ++ tailWord_6807564).sum := by decide
  have hdescent : baseEnd_6807564 < baseStart_6807564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807638 : List Nat := [5, 2, 2, 1, 1, 1, 3, 2, 6]
def baseStart_6807638 : Nat := 118140960795 + 6807638 * 2 ^ 59
def prefixEnd_6807638 : Nat := 4983230072969 + 3 ^ 40 * 6807638 * 2
def baseEnd_6807638 : Nat := 388398935090282368746361

theorem tailTrace_6807638 : CollatzResearch.WordTrace tailWord_6807638 prefixEnd_6807638 388398935090282368746361 := by
  unfold tailWord_6807638
  simp only [CollatzResearch.WordTrace]
  refine ⟨15518434756943603303253473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165529970740731768568037045 15518434756943603303253473)
  ·
    refine ⟨11638826067707702477440105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15518434756943603303253473 11638826067707702477440105)
    ·
      refine ⟨8729119550780776858080079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11638826067707702477440105 8729119550780776858080079)
      ·
        refine ⟨13093679326171165287120119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8729119550780776858080079 13093679326171165287120119)
        ·
          refine ⟨19640518989256747930680179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13093679326171165287120119 19640518989256747930680179)
          ·
            refine ⟨29460778483885121896020269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19640518989256747930680179 29460778483885121896020269)
            ·
              refine ⟨11047791931456920711007601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29460778483885121896020269 11047791931456920711007601)
              ·
                refine ⟨8285843948592690533255701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11047791931456920711007601 8285843948592690533255701)
                ·
                  refine ⟨388398935090282368746361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8285843948592690533255701 388398935090282368746361)
                  ·
                    rfl

theorem cell23_6807638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_6807638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807638 prefixEnd_6807638 := by exact prefixLift 6807638
  have htrace : WordTrace (prefixWord ++ tailWord_6807638) baseStart_6807638 baseEnd_6807638 := by
    simpa [prefixWord, tailWord_6807638, baseEnd_6807638] using wordTrace_append hprefix tailTrace_6807638
  have hstable : (prefixWord ++ tailWord_6807638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807638).length < 2 ^ (prefixWord ++ tailWord_6807638).sum := by decide
  have hdescent : baseEnd_6807638 < baseStart_6807638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807648 : List Nat := [2, 1, 1, 3, 2, 3, 2, 4, 1, 1, 3]
def baseStart_6807648 : Nat := 118140960795 + 6807648 * 2 ^ 59
def prefixEnd_6807648 : Nat := 4983230072969 + 3 ^ 40 * 6807648 * 2
def baseEnd_6807648 : Nat := 3495595550619086279592203

theorem tailTrace_6807648 : CollatzResearch.WordTrace tailWord_6807648 prefixEnd_6807648 3495595550619086279592203 := by
  unfold tailWord_6807648
  simp only [CollatzResearch.WordTrace]
  refine ⟨124147660420530712279959799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165530213894040949706613065 124147660420530712279959799)
  ·
    refine ⟨186221490630796068419939699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124147660420530712279959799 186221490630796068419939699)
    ·
      refine ⟨279332235946194102629909549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186221490630796068419939699 279332235946194102629909549)
      ·
        refine ⟨104749588479822788486216081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279332235946194102629909549 104749588479822788486216081)
        ·
          refine ⟨78562191359867091364662061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104749588479822788486216081 78562191359867091364662061)
          ·
            refine ⟨29460821759950159261748273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78562191359867091364662061 29460821759950159261748273)
            ·
              refine ⟨22095616319962619446311205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29460821759950159261748273 22095616319962619446311205)
              ·
                refine ⟨4142928059992991146183351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22095616319962619446311205 4142928059992991146183351)
                ·
                  refine ⟨6214392089989486719275027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142928059992991146183351 6214392089989486719275027)
                  ·
                    refine ⟨9321588134984230078912541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6214392089989486719275027 9321588134984230078912541)
                    ·
                      refine ⟨3495595550619086279592203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9321588134984230078912541 3495595550619086279592203)
                      ·
                        rfl

theorem cell23_6807648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_6807648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807648 prefixEnd_6807648 := by exact prefixLift 6807648
  have htrace : WordTrace (prefixWord ++ tailWord_6807648) baseStart_6807648 baseEnd_6807648 := by
    simpa [prefixWord, tailWord_6807648, baseEnd_6807648] using wordTrace_append hprefix tailTrace_6807648
  have hstable : (prefixWord ++ tailWord_6807648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807648).length < 2 ^ (prefixWord ++ tailWord_6807648).sum := by decide
  have hdescent : baseEnd_6807648 < baseStart_6807648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807664 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 1, 6]
def baseStart_6807664 : Nat := 118140960795 + 6807664 * 2 ^ 59
def prefixEnd_6807664 : Nat := 4983230072969 + 3 ^ 40 * 6807664 * 2
def baseEnd_6807664 : Nat := 1165201255436519405664043

theorem tailTrace_6807664 : CollatzResearch.WordTrace tailWord_6807664 prefixEnd_6807664 1165201255436519405664043 := by
  unfold tailWord_6807664
  simp only [CollatzResearch.WordTrace]
  refine ⟨124147952204501729646251023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165530602939335639528334697 124147952204501729646251023)
  ·
    refine ⟨186221928306752594469376535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124147952204501729646251023 186221928306752594469376535)
    ·
      refine ⟨279332892460128891704064803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186221928306752594469376535 279332892460128891704064803)
      ·
        refine ⟨418999338690193337556097205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279332892460128891704064803 418999338690193337556097205)
        ·
          refine ⟨39281188002205625395884113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 418999338690193337556097205 39281188002205625395884113)
          ·
            refine ⟨29460891001654219046913085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39281188002205625395884113 29460891001654219046913085)
            ·
              refine ⟨11047834125620332142592407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29460891001654219046913085 11047834125620332142592407)
              ·
                refine ⟨16571751188430498213888611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11047834125620332142592407 16571751188430498213888611)
                ·
                  refine ⟨24857626782645747320832917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16571751188430498213888611 24857626782645747320832917)
                  ·
                    refine ⟨1165201255436519405664043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24857626782645747320832917 1165201255436519405664043)
                    ·
                      rfl

theorem cell23_6807664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 1, 6].length) (baseStart_6807664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807664 prefixEnd_6807664 := by exact prefixLift 6807664
  have htrace : WordTrace (prefixWord ++ tailWord_6807664) baseStart_6807664 baseEnd_6807664 := by
    simpa [prefixWord, tailWord_6807664, baseEnd_6807664] using wordTrace_append hprefix tailTrace_6807664
  have hstable : (prefixWord ++ tailWord_6807664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807664).length < 2 ^ (prefixWord ++ tailWord_6807664).sum := by decide
  have hdescent : baseEnd_6807664 < baseStart_6807664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807671 : List Nat := [1, 1, 3, 1, 1, 6, 2, 2, 1, 1, 4]
def baseStart_6807671 : Nat := 118140960795 + 6807671 * 2 ^ 59
def prefixEnd_6807671 : Nat := 4983230072969 + 3 ^ 40 * 6807671 * 2
def baseEnd_6807671 : Nat := 3495607360674139689604597

theorem tailTrace_6807671 : CollatzResearch.WordTrace tailWord_6807671 prefixEnd_6807671 3495607360674139689604597 := by
  unfold tailWord_6807671
  simp only [CollatzResearch.WordTrace]
  refine ⟨248296159719978099488006867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165530773146652066325337911 248296159719978099488006867)
  ·
    refine ⟨372444239579967149232010301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248296159719978099488006867 372444239579967149232010301)
    ·
      refine ⟨139666589842487680962003863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372444239579967149232010301 139666589842487680962003863)
      ·
        refine ⟨209499884763731521443005795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139666589842487680962003863 209499884763731521443005795)
        ·
          refine ⟨314249827145597282164508693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209499884763731521443005795 314249827145597282164508693)
          ·
            refine ⟨14730460647449872601461345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 314249827145597282164508693 14730460647449872601461345)
            ·
              refine ⟨11047845485587404451096009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14730460647449872601461345 11047845485587404451096009)
              ·
                refine ⟨8285884114190553338322007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11047845485587404451096009 8285884114190553338322007)
                ·
                  refine ⟨12428826171285830007483011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8285884114190553338322007 12428826171285830007483011)
                  ·
                    refine ⟨18643239256928745011224517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12428826171285830007483011 18643239256928745011224517)
                    ·
                      refine ⟨3495607360674139689604597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18643239256928745011224517 3495607360674139689604597)
                      ·
                        rfl

theorem cell23_6807671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_6807671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807671 prefixEnd_6807671 := by exact prefixLift 6807671
  have htrace : WordTrace (prefixWord ++ tailWord_6807671) baseStart_6807671 baseEnd_6807671 := by
    simpa [prefixWord, tailWord_6807671, baseEnd_6807671] using wordTrace_append hprefix tailTrace_6807671
  have hstable : (prefixWord ++ tailWord_6807671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807671).length < 2 ^ (prefixWord ++ tailWord_6807671).sum := by decide
  have hdescent : baseEnd_6807671 < baseStart_6807671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807684 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_6807684 : Nat := 118140960795 + 6807684 * 2 ^ 59
def prefixEnd_6807684 : Nat := 4983230072969 + 3 ^ 40 * 6807684 * 2
def baseEnd_6807684 : Nat := 3495614035922648138742037

theorem tailTrace_6807684 : CollatzResearch.WordTrace tailWord_6807684 prefixEnd_6807684 3495614035922648138742037 := by
  unfold tailWord_6807684
  simp only [CollatzResearch.WordTrace]
  refine ⟨124148316934465501354115053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165531089245954001805486737 124148316934465501354115053)
  ·
    refine ⟨46555618850424563007793145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124148316934465501354115053 46555618850424563007793145)
    ·
      refine ⟨34916714137818422255844859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46555618850424563007793145 34916714137818422255844859)
      ·
        refine ⟨52375071206727633383767289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34916714137818422255844859 52375071206727633383767289)
        ·
          refine ⟨39281303405045725037825467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52375071206727633383767289 39281303405045725037825467)
          ·
            refine ⟨58921955107568587556738201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39281303405045725037825467 58921955107568587556738201)
            ·
              refine ⟨44191466330676440667553651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58921955107568587556738201 44191466330676440667553651)
              ·
                refine ⟨66287199496014661001330477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44191466330676440667553651 66287199496014661001330477)
                ·
                  refine ⟨24857699811005497875498929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66287199496014661001330477 24857699811005497875498929)
                  ·
                    refine ⟨18643274858254123406624197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24857699811005497875498929 18643274858254123406624197)
                    ·
                      refine ⟨3495614035922648138742037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18643274858254123406624197 3495614035922648138742037)
                      ·
                        rfl

theorem cell23_6807684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_6807684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807684 prefixEnd_6807684 := by exact prefixLift 6807684
  have htrace : WordTrace (prefixWord ++ tailWord_6807684) baseStart_6807684 baseEnd_6807684 := by
    simpa [prefixWord, tailWord_6807684, baseEnd_6807684] using wordTrace_append hprefix tailTrace_6807684
  have hstable : (prefixWord ++ tailWord_6807684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807684).length < 2 ^ (prefixWord ++ tailWord_6807684).sum := by decide
  have hdescent : baseEnd_6807684 < baseStart_6807684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807722 : List Nat := [3, 1, 5, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_6807722 : Nat := 118140960795 + 6807722 * 2 ^ 59
def prefixEnd_6807722 : Nat := 4983230072969 + 3 ^ 40 * 6807722 * 2
def baseEnd_6807722 : Nat := 3495633548187518990066863

theorem tailTrace_6807722 : CollatzResearch.WordTrace tailWord_6807722 prefixEnd_6807722 3495633548187518990066863 := by
  unfold tailWord_6807722
  simp only [CollatzResearch.WordTrace]
  refine ⟨62074504960698333799528355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165532013228528890132075613 62074504960698333799528355)
  ·
    refine ⟨93111757441047500699292533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62074504960698333799528355 93111757441047500699292533)
    ·
      refine ⟨8729227260098203190558675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93111757441047500699292533 8729227260098203190558675)
      ·
        refine ⟨13093840890147304785838013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8729227260098203190558675 13093840890147304785838013)
        ·
          refine ⟨4910190333805239294689255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13093840890147304785838013 4910190333805239294689255)
          ·
            refine ⟨7365285500707858942033883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4910190333805239294689255 7365285500707858942033883)
            ·
              refine ⟨11047928251061788413050825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7365285500707858942033883 11047928251061788413050825)
              ·
                refine ⟨8285946188296341309788119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11047928251061788413050825 8285946188296341309788119)
                ·
                  refine ⟨12428919282444511964682179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8285946188296341309788119 12428919282444511964682179)
                  ·
                    refine ⟨18643378923666767947023269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12428919282444511964682179 18643378923666767947023269)
                    ·
                      refine ⟨3495633548187518990066863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18643378923666767947023269 3495633548187518990066863)
                      ·
                        rfl

theorem cell23_6807722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_6807722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807722 prefixEnd_6807722 := by exact prefixLift 6807722
  have htrace : WordTrace (prefixWord ++ tailWord_6807722) baseStart_6807722 baseEnd_6807722 := by
    simpa [prefixWord, tailWord_6807722, baseEnd_6807722] using wordTrace_append hprefix tailTrace_6807722
  have hstable : (prefixWord ++ tailWord_6807722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807722).length < 2 ^ (prefixWord ++ tailWord_6807722).sum := by decide
  have hdescent : baseEnd_6807722 < baseStart_6807722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807725 : List Nat := [1, 5, 2, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_6807725 : Nat := 118140960795 + 6807725 * 2 ^ 59
def prefixEnd_6807725 : Nat := 4983230072969 + 3 ^ 40 * 6807725 * 2
def baseEnd_6807725 : Nat := 3495635088629482478329349

theorem tailTrace_6807725 : CollatzResearch.WordTrace tailWord_6807725 prefixEnd_6807725 3495635088629482478329349 := by
  unfold tailWord_6807725
  simp only [CollatzResearch.WordTrace]
  refine ⟨248298129261782466710472629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165532086174521644473648419 248298129261782466710472629)
  ·
    refine ⟨23277949618292106254106809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 248298129261782466710472629 23277949618292106254106809)
    ·
      refine ⟨17458462213719079690580107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23277949618292106254106809 17458462213719079690580107)
      ·
        refine ⟨26187693320578619535870161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17458462213719079690580107 26187693320578619535870161)
        ·
          refine ⟨19640769990433964651902621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26187693320578619535870161 19640769990433964651902621)
          ·
            refine ⟨7365288746412736744463483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19640769990433964651902621 7365288746412736744463483)
            ·
              refine ⟨11047933119619105116695225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7365288746412736744463483 11047933119619105116695225)
              ·
                refine ⟨8285949839714328837521419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11047933119619105116695225 8285949839714328837521419)
                ·
                  refine ⟨12428924759571493256282129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8285949839714328837521419 12428924759571493256282129)
                  ·
                    refine ⟨9321693569678619942211597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12428924759571493256282129 9321693569678619942211597)
                    ·
                      refine ⟨3495635088629482478329349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9321693569678619942211597 3495635088629482478329349)
                      ·
                        rfl

theorem cell23_6807725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_6807725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807725 prefixEnd_6807725 := by exact prefixLift 6807725
  have htrace : WordTrace (prefixWord ++ tailWord_6807725) baseStart_6807725 baseEnd_6807725 := by
    simpa [prefixWord, tailWord_6807725, baseEnd_6807725] using wordTrace_append hprefix tailTrace_6807725
  have hstable : (prefixWord ++ tailWord_6807725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807725).length < 2 ^ (prefixWord ++ tailWord_6807725).sum := by decide
  have hdescent : baseEnd_6807725 < baseStart_6807725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807727 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 8]
def baseStart_6807727 : Nat := 118140960795 + 6807727 * 2 ^ 59
def prefixEnd_6807727 : Nat := 4983230072969 + 3 ^ 40 * 6807727 * 2
def baseEnd_6807727 : Nat := 3495636115590791470504339

theorem tailTrace_6807727 : CollatzResearch.WordTrace tailWord_6807727 prefixEnd_6807727 3495636115590791470504339 := by
  unfold tailWord_6807727
  simp only [CollatzResearch.WordTrace]
  refine ⟨248298202207775221052045435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165532134805183480701363623 248298202207775221052045435)
  ·
    refine ⟨372447303311662831578068153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248298202207775221052045435 372447303311662831578068153)
    ·
      refine ⟨279335477483747123683551115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372447303311662831578068153 279335477483747123683551115)
      ·
        refine ⟨419003216225620685525326673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279335477483747123683551115 419003216225620685525326673)
        ·
          refine ⟨314252412169215514143995005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419003216225620685525326673 314252412169215514143995005)
          ·
            refine ⟨117844654563455817803998127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314252412169215514143995005 117844654563455817803998127)
            ·
              refine ⟨176766981845183726705997191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117844654563455817803998127 176766981845183726705997191)
              ·
                refine ⟨265150472767775590058995787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176766981845183726705997191 265150472767775590058995787)
                ·
                  refine ⟨397725709151663385088493681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265150472767775590058995787 397725709151663385088493681)
                  ·
                    refine ⟨298294281863747538816370261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 397725709151663385088493681 298294281863747538816370261)
                    ·
                      refine ⟨3495636115590791470504339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 298294281863747538816370261 3495636115590791470504339)
                      ·
                        rfl

theorem cell23_6807727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_6807727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807727 prefixEnd_6807727 := by exact prefixLift 6807727
  have htrace : WordTrace (prefixWord ++ tailWord_6807727) baseStart_6807727 baseEnd_6807727 := by
    simpa [prefixWord, tailWord_6807727, baseEnd_6807727] using wordTrace_append hprefix tailTrace_6807727
  have hstable : (prefixWord ++ tailWord_6807727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807727).length < 2 ^ (prefixWord ++ tailWord_6807727).sum := by decide
  have hdescent : baseEnd_6807727 < baseStart_6807727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807754 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 2, 6]
def baseStart_6807754 : Nat := 118140960795 + 6807754 * 2 ^ 59
def prefixEnd_6807754 : Nat := 4983230072969 + 3 ^ 40 * 6807754 * 2
def baseEnd_6807754 : Nat := 1165216659856154288288905

theorem tailTrace_6807754 : CollatzResearch.WordTrace tailWord_6807754 prefixEnd_6807754 1165216659856154288288905 := by
  unfold tailWord_6807754
  simp only [CollatzResearch.WordTrace]
  refine ⟨62074796744669351165819579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165532791319118269775518877 62074796744669351165819579)
  ·
    refine ⟨93112195117004026748729369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62074796744669351165819579 93112195117004026748729369)
    ·
      refine ⟨69834146337753020061547027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93112195117004026748729369 69834146337753020061547027)
      ·
        refine ⟨104751219506629530092320541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69834146337753020061547027 104751219506629530092320541)
        ·
          refine ⟨39281707314986073784620203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104751219506629530092320541 39281707314986073784620203)
          ·
            refine ⟨58922560972479110676930305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39281707314986073784620203 58922560972479110676930305)
            ·
              refine ⟨44191920729359333007697729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58922560972479110676930305 44191920729359333007697729)
              ·
                refine ⟨33143940547019499755773297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44191920729359333007697729 33143940547019499755773297)
                ·
                  refine ⟨24857955410264624816829973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33143940547019499755773297 24857955410264624816829973)
                  ·
                    refine ⟨1165216659856154288288905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24857955410264624816829973 1165216659856154288288905)
                    ·
                      rfl

theorem cell23_6807754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_6807754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807754 prefixEnd_6807754 := by exact prefixLift 6807754
  have htrace : WordTrace (prefixWord ++ tailWord_6807754) baseStart_6807754 baseEnd_6807754 := by
    simpa [prefixWord, tailWord_6807754, baseEnd_6807754] using wordTrace_append hprefix tailTrace_6807754
  have hstable : (prefixWord ++ tailWord_6807754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807754).length < 2 ^ (prefixWord ++ tailWord_6807754).sum := by decide
  have hdescent : baseEnd_6807754 < baseStart_6807754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807756 : List Nat := [2, 2, 1, 6, 1, 2, 2, 2, 1, 2, 2]
def baseStart_6807756 : Nat := 118140960795 + 6807756 * 2 ^ 59
def prefixEnd_6807756 : Nat := 4983230072969 + 3 ^ 40 * 6807756 * 2
def baseEnd_6807756 : Nat := 3495651006529771857041707

theorem tailTrace_6807756 : CollatzResearch.WordTrace tailWord_6807756 prefixEnd_6807756 3495651006529771857041707 := by
  unfold tailWord_6807756
  simp only [CollatzResearch.WordTrace]
  refine ⟨124149629962335079502425561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165532839949780106003234081 124149629962335079502425561)
  ·
    refine ⟨93112222471751309626819171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124149629962335079502425561 93112222471751309626819171)
    ·
      refine ⟨139668333707626964440228757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93112222471751309626819171 139668333707626964440228757)
      ·
        refine ⟨6546953142545013958135723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139668333707626964440228757 6546953142545013958135723)
        ·
          refine ⟨9820429713817520937203585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6546953142545013958135723 9820429713817520937203585)
          ·
            refine ⟨7365322285363140702902689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9820429713817520937203585 7365322285363140702902689)
            ·
              refine ⟨5523991714022355527177017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7365322285363140702902689 5523991714022355527177017)
              ·
                refine ⟨4142993785516766645382763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5523991714022355527177017 4142993785516766645382763)
                ·
                  refine ⟨6214490678275149968074145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142993785516766645382763 6214490678275149968074145)
                  ·
                    refine ⟨4660868008706362476055609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6214490678275149968074145 4660868008706362476055609)
                    ·
                      refine ⟨3495651006529771857041707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4660868008706362476055609 3495651006529771857041707)
                      ·
                        rfl

theorem cell23_6807756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_6807756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807756 prefixEnd_6807756 := by exact prefixLift 6807756
  have htrace : WordTrace (prefixWord ++ tailWord_6807756) baseStart_6807756 baseEnd_6807756 := by
    simpa [prefixWord, tailWord_6807756, baseEnd_6807756] using wordTrace_append hprefix tailTrace_6807756
  have hstable : (prefixWord ++ tailWord_6807756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807756).length < 2 ^ (prefixWord ++ tailWord_6807756).sum := by decide
  have hdescent : baseEnd_6807756 < baseStart_6807756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807784 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 9]
def baseStart_6807784 : Nat := 118140960795 + 6807784 * 2 ^ 59
def prefixEnd_6807784 : Nat := 4983230072969 + 3 ^ 40 * 6807784 * 2
def baseEnd_6807784 : Nat := 388407264887566416387953

theorem tailTrace_6807784 : CollatzResearch.WordTrace tailWord_6807784 prefixEnd_6807784 388407264887566416387953 := by
  unfold tailWord_6807784
  simp only [CollatzResearch.WordTrace]
  refine ⟨124150140584284359893435203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165533520779045813191246937 124150140584284359893435203)
  ·
    refine ⟨186225210876426539840152805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124150140584284359893435203 186225210876426539840152805)
    ·
      refine ⟨34917227039329976220028651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186225210876426539840152805 34917227039329976220028651)
      ·
        refine ⟨52375840558994964330042977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34917227039329976220028651 52375840558994964330042977)
        ·
          refine ⟨39281880419246223247532233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52375840558994964330042977 39281880419246223247532233)
          ·
            refine ⟨29461410314434667435649175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39281880419246223247532233 29461410314434667435649175)
            ·
              refine ⟨44192115471652001153473763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29461410314434667435649175 44192115471652001153473763)
              ·
                refine ⟨66288173207478001730210645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44192115471652001153473763 66288173207478001730210645)
                ·
                  refine ⟨388407264887566416387953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66288173207478001730210645 388407264887566416387953)
                  ·
                    rfl

theorem cell23_6807784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 9].length) (baseStart_6807784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807784 prefixEnd_6807784 := by exact prefixLift 6807784
  have htrace : WordTrace (prefixWord ++ tailWord_6807784) baseStart_6807784 baseEnd_6807784 := by
    simpa [prefixWord, tailWord_6807784, baseEnd_6807784] using wordTrace_append hprefix tailTrace_6807784
  have hstable : (prefixWord ++ tailWord_6807784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807784).length < 2 ^ (prefixWord ++ tailWord_6807784).sum := by decide
  have hdescent : baseEnd_6807784 < baseStart_6807784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807864 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 1, 3, 6]
def baseStart_6807864 : Nat := 118140960795 + 6807864 * 2 ^ 59
def prefixEnd_6807864 : Nat := 4983230072969 + 3 ^ 40 * 6807864 * 2
def baseEnd_6807864 : Nat := 3495706462440457434491209

theorem tailTrace_6807864 : CollatzResearch.WordTrace tailWord_6807864 prefixEnd_6807864 3495706462440457434491209 := by
  unfold tailWord_6807864
  simp only [CollatzResearch.WordTrace]
  refine ⟨124151599504139446724891323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165535466005519262299855097 124151599504139446724891323)
  ·
    refine ⟨186227399256209170087336985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124151599504139446724891323 186227399256209170087336985)
    ·
      refine ⟨139670549442156877565502739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186227399256209170087336985 139670549442156877565502739)
      ·
        refine ⟨209505824163235316348254109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139670549442156877565502739 209505824163235316348254109)
        ·
          refine ⟨78564684061213243630595291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209505824163235316348254109 78564684061213243630595291)
          ·
            refine ⟨117847026091819865445892937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78564684061213243630595291 117847026091819865445892937)
            ·
              refine ⟨88385269568864899084419703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117847026091819865445892937 88385269568864899084419703)
              ·
                refine ⟨132577904353297348626629555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88385269568864899084419703 132577904353297348626629555)
                ·
                  refine ⟨198866856529946022939944333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132577904353297348626629555 198866856529946022939944333)
                  ·
                    refine ⟨74575071198729758602479125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 198866856529946022939944333 74575071198729758602479125)
                    ·
                      refine ⟨3495706462440457434491209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74575071198729758602479125 3495706462440457434491209)
                      ·
                        rfl

theorem cell23_6807864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_6807864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807864 prefixEnd_6807864 := by exact prefixLift 6807864
  have htrace : WordTrace (prefixWord ++ tailWord_6807864) baseStart_6807864 baseEnd_6807864 := by
    simpa [prefixWord, tailWord_6807864, baseEnd_6807864] using wordTrace_append hprefix tailTrace_6807864
  have hstable : (prefixWord ++ tailWord_6807864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807864).length < 2 ^ (prefixWord ++ tailWord_6807864).sum := by decide
  have hdescent : baseEnd_6807864 < baseStart_6807864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807935 : List Nat := [1, 1, 2, 2, 1, 1, 2, 8, 1, 1, 3]
def baseStart_6807935 : Nat := 118140960795 + 6807935 * 2 ^ 59
def prefixEnd_6807935 : Nat := 4983230072969 + 3 ^ 40 * 6807935 * 2
def baseEnd_6807935 : Nat := 3495742919566926656703383

theorem tailTrace_6807935 : CollatzResearch.WordTrace tailWord_6807935 prefixEnd_6807935 3495742919566926656703383 := by
  unfold tailWord_6807935
  simp only [CollatzResearch.WordTrace]
  refine ⟨248305788591021672575617259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165537192394014448383744839 248305788591021672575617259)
  ·
    refine ⟨372458682886532508863425889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248305788591021672575617259 372458682886532508863425889)
    ·
      refine ⟨279344012164899381647569417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372458682886532508863425889 279344012164899381647569417)
      ·
        refine ⟨209508009123674536235677063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279344012164899381647569417 209508009123674536235677063)
        ·
          refine ⟨314262013685511804353515595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209508009123674536235677063 314262013685511804353515595)
          ·
            refine ⟨471393020528267706530273393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314262013685511804353515595 471393020528267706530273393)
            ·
              refine ⟨353544765396200779897705045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471393020528267706530273393 353544765396200779897705045)
              ·
                refine ⟨4143102719486727889426231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 353544765396200779897705045 4143102719486727889426231)
                ·
                  refine ⟨6214654079230091834139347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4143102719486727889426231 6214654079230091834139347)
                  ·
                    refine ⟨9321981118845137751209021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6214654079230091834139347 9321981118845137751209021)
                    ·
                      refine ⟨3495742919566926656703383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9321981118845137751209021 3495742919566926656703383)
                      ·
                        rfl

theorem cell23_6807935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 1, 1, 3].length) (baseStart_6807935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807935 prefixEnd_6807935 := by exact prefixLift 6807935
  have htrace : WordTrace (prefixWord ++ tailWord_6807935) baseStart_6807935 baseEnd_6807935 := by
    simpa [prefixWord, tailWord_6807935, baseEnd_6807935] using wordTrace_append hprefix tailTrace_6807935
  have hstable : (prefixWord ++ tailWord_6807935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807935).length < 2 ^ (prefixWord ++ tailWord_6807935).sum := by decide
  have hdescent : baseEnd_6807935 < baseStart_6807935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807962 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2]
def baseStart_6807962 : Nat := 118140960795 + 6807962 * 2 ^ 59
def prefixEnd_6807962 : Nat := 4983230072969 + 3 ^ 40 * 6807962 * 2
def baseEnd_6807962 : Nat := 3495756783544598051065759

theorem tailTrace_6807962 : CollatzResearch.WordTrace tailWord_6807962 prefixEnd_6807962 3495756783544598051065759 := by
  unfold tailWord_6807962
  simp only [CollatzResearch.WordTrace]
  refine ⟨62076693340480964046712535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165537848907949237457900093 62076693340480964046712535)
  ·
    refine ⟨93115040010721446070068803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62076693340480964046712535 93115040010721446070068803)
    ·
      refine ⟨139672560016082169105103205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93115040010721446070068803 139672560016082169105103205)
      ·
        refine ⟨26188605003015406707206851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139672560016082169105103205 26188605003015406707206851)
        ·
          refine ⟨39282907504523110060810277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26188605003015406707206851 39282907504523110060810277)
          ·
            refine ⟨7365545157098083136401927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39282907504523110060810277 7365545157098083136401927)
            ·
              refine ⟨11048317735647124704602891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7365545157098083136401927 11048317735647124704602891)
              ·
                refine ⟨16572476603470687056904337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11048317735647124704602891 16572476603470687056904337)
                ·
                  refine ⟨12429357452603015292678253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16572476603470687056904337 12429357452603015292678253)
                  ·
                    refine ⟨4661009044726130734754345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12429357452603015292678253 4661009044726130734754345)
                    ·
                      refine ⟨3495756783544598051065759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4661009044726130734754345 3495756783544598051065759)
                      ·
                        rfl

theorem cell23_6807962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_6807962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807962 prefixEnd_6807962 := by exact prefixLift 6807962
  have htrace : WordTrace (prefixWord ++ tailWord_6807962) baseStart_6807962 baseEnd_6807962 := by
    simpa [prefixWord, tailWord_6807962, baseEnd_6807962] using wordTrace_append hprefix tailTrace_6807962
  have hstable : (prefixWord ++ tailWord_6807962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807962).length < 2 ^ (prefixWord ++ tailWord_6807962).sum := by decide
  have hdescent : baseEnd_6807962 < baseStart_6807962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807975 : List Nat := [1, 1, 6, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_6807975 : Nat := 118140960795 + 6807975 * 2 ^ 59
def prefixEnd_6807975 : Nat := 4983230072969 + 3 ^ 40 * 6807975 * 2
def baseEnd_6807975 : Nat := 3495763458793106500203199

theorem tailTrace_6807975 : CollatzResearch.WordTrace tailWord_6807975 prefixEnd_6807975 3495763458793106500203199 := by
  unfold tailWord_6807975
  simp only [CollatzResearch.WordTrace]
  refine ⟨248307247510876759407073379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165538165007251172938048919 248307247510876759407073379)
  ·
    refine ⟨372460871266315139110610069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248307247510876759407073379 372460871266315139110610069)
    ·
      refine ⟨17459103340608522145809847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 372460871266315139110610069 17459103340608522145809847)
      ·
        refine ⟨26188655010912783218714771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17459103340608522145809847 26188655010912783218714771)
        ·
          refine ⟨39282982516369174828072157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26188655010912783218714771 39282982516369174828072157)
          ·
            refine ⟨14731118443638440560527059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39282982516369174828072157 14731118443638440560527059)
            ·
              refine ⟨22096677665457660840790589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14731118443638440560527059 22096677665457660840790589)
              ·
                refine ⟨8286254124546622815296471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22096677665457660840790589 8286254124546622815296471)
                ·
                  refine ⟨12429381186819934222944707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8286254124546622815296471 12429381186819934222944707)
                  ·
                    refine ⟨18644071780229901334417061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12429381186819934222944707 18644071780229901334417061)
                    ·
                      refine ⟨3495763458793106500203199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18644071780229901334417061 3495763458793106500203199)
                      ·
                        rfl

theorem cell23_6807975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_6807975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807975 prefixEnd_6807975 := by exact prefixLift 6807975
  have htrace : WordTrace (prefixWord ++ tailWord_6807975) baseStart_6807975 baseEnd_6807975 := by
    simpa [prefixWord, tailWord_6807975, baseEnd_6807975] using wordTrace_append hprefix tailTrace_6807975
  have hstable : (prefixWord ++ tailWord_6807975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807975).length < 2 ^ (prefixWord ++ tailWord_6807975).sum := by decide
  have hdescent : baseEnd_6807975 < baseStart_6807975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6807985 : List Nat := [1, 2, 2, 4, 1, 2, 3, 2, 2, 4]
def baseStart_6807985 : Nat := 118140960795 + 6807985 * 2 ^ 59
def prefixEnd_6807985 : Nat := 4983230072969 + 3 ^ 40 * 6807985 * 2
def baseEnd_6807985 : Nat := 1165256197866550487026051

theorem tailTrace_6807985 : CollatzResearch.WordTrace tailWord_6807985 prefixEnd_6807985 1165256197866550487026051 := by
  unfold tailWord_6807985
  simp only [CollatzResearch.WordTrace]
  refine ⟨248307612240840531114937409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165538408160560354076624939 248307612240840531114937409)
  ·
    refine ⟨186230709180630398336203057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248307612240840531114937409 186230709180630398336203057)
    ·
      refine ⟨139673031885472798752152293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186230709180630398336203057 139673031885472798752152293)
      ·
        refine ⟨26188693478526149766028555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139673031885472798752152293 26188693478526149766028555)
        ·
          refine ⟨39283040217789224649042833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26188693478526149766028555 39283040217789224649042833)
          ·
            refine ⟨29462280163341918486782125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39283040217789224649042833 29462280163341918486782125)
            ·
              refine ⟨11048355061253219432543297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29462280163341918486782125 11048355061253219432543297)
              ·
                refine ⟨8286266295939914574407473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11048355061253219432543297 8286266295939914574407473)
                ·
                  refine ⟨6214699721954935930805605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8286266295939914574407473 6214699721954935930805605)
                  ·
                    refine ⟨1165256197866550487026051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6214699721954935930805605 1165256197866550487026051)
                    ·
                      rfl

theorem cell23_6807985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_6807985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6807985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6807985 prefixEnd_6807985 := by exact prefixLift 6807985
  have htrace : WordTrace (prefixWord ++ tailWord_6807985) baseStart_6807985 baseEnd_6807985 := by
    simpa [prefixWord, tailWord_6807985, baseEnd_6807985] using wordTrace_append hprefix tailTrace_6807985
  have hstable : (prefixWord ++ tailWord_6807985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6807985).length < 2 ^ (prefixWord ++ tailWord_6807985).sum := by decide
  have hdescent : baseEnd_6807985 < baseStart_6807985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6807985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808012 : List Nat := [2, 2, 1, 4, 3, 1, 2, 2, 1, 2, 3]
def baseStart_6808012 : Nat := 118140960795 + 6808012 * 2 ^ 59
def prefixEnd_6808012 : Nat := 4983230072969 + 3 ^ 40 * 6808012 * 2
def baseEnd_6808012 : Nat := 3495782457577322855440529

theorem tailTrace_6808012 : CollatzResearch.WordTrace tailWord_6808012 prefixEnd_6808012 3495782457577322855440529 := by
  unfold tailWord_6808012
  simp only [CollatzResearch.WordTrace]
  refine ⟨124154298505871357363085145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165539064674495143150780193 124154298505871357363085145)
  ·
    refine ⟨93115723879403518022313859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124154298505871357363085145 93115723879403518022313859)
    ·
      refine ⟨139673585819105277033470789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93115723879403518022313859 139673585819105277033470789)
      ·
        refine ⟨26188797341082239443775773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139673585819105277033470789 26188797341082239443775773)
        ·
          refine ⟨9820799002905839791415915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26188797341082239443775773 9820799002905839791415915)
          ·
            refine ⟨14731198504358759687123873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9820799002905839791415915 14731198504358759687123873)
            ·
              refine ⟨11048398878269069765342905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14731198504358759687123873 11048398878269069765342905)
              ·
                refine ⟨8286299158701802324007179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11048398878269069765342905 8286299158701802324007179)
                ·
                  refine ⟨12429448738052703486010769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8286299158701802324007179 12429448738052703486010769)
                  ·
                    refine ⟨9322086553539527614508077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12429448738052703486010769 9322086553539527614508077)
                    ·
                      refine ⟨3495782457577322855440529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9322086553539527614508077 3495782457577322855440529)
                      ·
                        rfl

theorem cell23_6808012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_6808012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808012 prefixEnd_6808012 := by exact prefixLift 6808012
  have htrace : WordTrace (prefixWord ++ tailWord_6808012) baseStart_6808012 baseEnd_6808012 := by
    simpa [prefixWord, tailWord_6808012, baseEnd_6808012] using wordTrace_append hprefix tailTrace_6808012
  have hstable : (prefixWord ++ tailWord_6808012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808012).length < 2 ^ (prefixWord ++ tailWord_6808012).sum := by decide
  have hdescent : baseEnd_6808012 < baseStart_6808012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808041 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 2, 6]
def baseStart_6808041 : Nat := 118140960795 + 6808041 * 2 ^ 59
def prefixEnd_6808041 : Nat := 4983230072969 + 3 ^ 40 * 6808041 * 2
def baseEnd_6808041 : Nat := 1165265782838767747325965

theorem tailTrace_6808041 : CollatzResearch.WordTrace tailWord_6808041 prefixEnd_6808041 1165265782838767747325965 := by
  unfold tailWord_6808041
  simp only [CollatzResearch.WordTrace]
  refine ⟨248309654728637652678975977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165539769819091768452650651 248309654728637652678975977)
  ·
    refine ⟨186232241046478239509231983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248309654728637652678975977 186232241046478239509231983)
    ·
      refine ⟨279348361569717359263847975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186232241046478239509231983 279348361569717359263847975)
      ·
        refine ⟨419022542354576038895771963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279348361569717359263847975 419022542354576038895771963)
        ·
          refine ⟨628533813531864058343657945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419022542354576038895771963 628533813531864058343657945)
          ·
            refine ⟨471400360148898043757743459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628533813531864058343657945 471400360148898043757743459)
            ·
              refine ⟨707100540223347065636615189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471400360148898043757743459 707100540223347065636615189)
              ·
                refine ⟨33145337822969393701716337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 707100540223347065636615189 33145337822969393701716337)
                ·
                  refine ⟨24859003367227045276287253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33145337822969393701716337 24859003367227045276287253)
                  ·
                    refine ⟨1165265782838767747325965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24859003367227045276287253 1165265782838767747325965)
                    ·
                      rfl

theorem cell23_6808041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 6].length) (baseStart_6808041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808041 prefixEnd_6808041 := by exact prefixLift 6808041
  have htrace : WordTrace (prefixWord ++ tailWord_6808041) baseStart_6808041 baseEnd_6808041 := by
    simpa [prefixWord, tailWord_6808041, baseEnd_6808041] using wordTrace_append hprefix tailTrace_6808041
  have hstable : (prefixWord ++ tailWord_6808041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808041).length < 2 ^ (prefixWord ++ tailWord_6808041).sum := by decide
  have hdescent : baseEnd_6808041 < baseStart_6808041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808051 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 5]
def baseStart_6808051 : Nat := 118140960795 + 6808051 * 2 ^ 59
def prefixEnd_6808051 : Nat := 4983230072969 + 3 ^ 40 * 6808051 * 2
def baseEnd_6808051 : Nat := 3495802483322848202852849

theorem tailTrace_6808051 : CollatzResearch.WordTrace tailWord_6808051 prefixEnd_6808051 3495802483322848202852849 := by
  unfold tailWord_6808051
  simp only [CollatzResearch.WordTrace]
  refine ⟨248310019458601424386840007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165540012972400949591226671 248310019458601424386840007)
  ·
    refine ⟨372465029187902136580260011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248310019458601424386840007 372465029187902136580260011)
    ·
      refine ⟨558697543781853204870390017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372465029187902136580260011 558697543781853204870390017)
      ·
        refine ⟨419023157836389903652792513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558697543781853204870390017 419023157836389903652792513)
        ·
          refine ⟨314267368377292427739594385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419023157836389903652792513 314267368377292427739594385)
          ·
            refine ⟨235700526282969320804695789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314267368377292427739594385 235700526282969320804695789)
            ·
              refine ⟨88387697356113495301760921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235700526282969320804695789 88387697356113495301760921)
              ·
                refine ⟨66290773017085121476320691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88387697356113495301760921 66290773017085121476320691)
                ·
                  refine ⟨99436159525627682214481037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66290773017085121476320691 99436159525627682214481037)
                  ·
                    refine ⟨37288559822110380830430389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99436159525627682214481037 37288559822110380830430389)
                    ·
                      refine ⟨3495802483322848202852849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37288559822110380830430389 3495802483322848202852849)
                      ·
                        rfl

theorem cell23_6808051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_6808051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808051 prefixEnd_6808051 := by exact prefixLift 6808051
  have htrace : WordTrace (prefixWord ++ tailWord_6808051) baseStart_6808051 baseEnd_6808051 := by
    simpa [prefixWord, tailWord_6808051, baseEnd_6808051] using wordTrace_append hprefix tailTrace_6808051
  have hstable : (prefixWord ++ tailWord_6808051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808051).length < 2 ^ (prefixWord ++ tailWord_6808051).sum := by decide
  have hdescent : baseEnd_6808051 < baseStart_6808051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808081 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 7]
def baseStart_6808081 : Nat := 118140960795 + 6808081 * 2 ^ 59
def prefixEnd_6808081 : Nat := 4983230072969 + 3 ^ 40 * 6808081 * 2
def baseEnd_6808081 : Nat := 3495817887742483085477711

theorem tailTrace_6808081 : CollatzResearch.WordTrace tailWord_6808081 prefixEnd_6808081 3495817887742483085477711 := by
  unfold tailWord_6808081
  simp only [CollatzResearch.WordTrace]
  refine ⟨248311113648492739510432097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165540742432328493006954731 248311113648492739510432097)
  ·
    refine ⟨186233335236369554632824073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248311113648492739510432097 186233335236369554632824073)
    ·
      refine ⟨139675001427277165974618055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186233335236369554632824073 139675001427277165974618055)
      ·
        refine ⟨209512502140915748961927083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139675001427277165974618055 209512502140915748961927083)
        ·
          refine ⟨314268753211373623442890625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209512502140915748961927083 314268753211373623442890625)
          ·
            refine ⟨235701564908530217582167969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314268753211373623442890625 235701564908530217582167969)
            ·
              refine ⟨176776173681397663186625977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235701564908530217582167969 176776173681397663186625977)
              ·
                refine ⟨132582130261048247389969483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176776173681397663186625977 132582130261048247389969483)
                ·
                  refine ⟨198873195391572371084954225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132582130261048247389969483 198873195391572371084954225)
                  ·
                    refine ⟨149154896543679278313715669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 198873195391572371084954225 149154896543679278313715669)
                    ·
                      refine ⟨3495817887742483085477711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149154896543679278313715669 3495817887742483085477711)
                      ·
                        rfl

theorem cell23_6808081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_6808081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808081 prefixEnd_6808081 := by exact prefixLift 6808081
  have htrace : WordTrace (prefixWord ++ tailWord_6808081) baseStart_6808081 baseEnd_6808081 := by
    simpa [prefixWord, tailWord_6808081, baseEnd_6808081] using wordTrace_append hprefix tailTrace_6808081
  have hstable : (prefixWord ++ tailWord_6808081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808081).length < 2 ^ (prefixWord ++ tailWord_6808081).sum := by decide
  have hdescent : baseEnd_6808081 < baseStart_6808081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808099 : List Nat := [1, 1, 1, 4, 4, 2, 2, 2, 2, 2, 2]
def baseStart_6808099 : Nat := 118140960795 + 6808099 * 2 ^ 59
def prefixEnd_6808099 : Nat := 4983230072969 + 3 ^ 40 * 6808099 * 2
def baseEnd_6808099 : Nat := 3495827130394264015052629

theorem tailTrace_6808099 : CollatzResearch.WordTrace tailWord_6808099 prefixEnd_6808099 3495827130394264015052629 := by
  unfold tailWord_6808099
  simp only [CollatzResearch.WordTrace]
  refine ⟨248311770162427528584587351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165541180108285019056391567 248311770162427528584587351)
  ·
    refine ⟨372467655243641292876881027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248311770162427528584587351 372467655243641292876881027)
    ·
      refine ⟨558701482865461939315321541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372467655243641292876881027 558701482865461939315321541)
      ·
        refine ⟨104756528037274113621622789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 558701482865461939315321541 104756528037274113621622789)
        ·
          refine ⟨19641849006988896304054273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104756528037274113621622789 19641849006988896304054273)
          ·
            refine ⟨14731386755241672228040705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19641849006988896304054273 14731386755241672228040705)
            ·
              refine ⟨11048540066431254171030529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14731386755241672228040705 11048540066431254171030529)
              ·
                refine ⟨8286405049823440628272897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11048540066431254171030529 8286405049823440628272897)
                ·
                  refine ⟨6214803787367580471204673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8286405049823440628272897 6214803787367580471204673)
                  ·
                    refine ⟨4661102840525685353403505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6214803787367580471204673 4661102840525685353403505)
                    ·
                      refine ⟨3495827130394264015052629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4661102840525685353403505 3495827130394264015052629)
                      ·
                        rfl

theorem cell23_6808099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_6808099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808099 prefixEnd_6808099 := by exact prefixLift 6808099
  have htrace : WordTrace (prefixWord ++ tailWord_6808099) baseStart_6808099 baseEnd_6808099 := by
    simpa [prefixWord, tailWord_6808099, baseEnd_6808099] using wordTrace_append hprefix tailTrace_6808099
  have hstable : (prefixWord ++ tailWord_6808099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808099).length < 2 ^ (prefixWord ++ tailWord_6808099).sum := by decide
  have hdescent : baseEnd_6808099 < baseStart_6808099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808109 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_6808109 : Nat := 118140960795 + 6808109 * 2 ^ 59
def prefixEnd_6808109 : Nat := 4983230072969 + 3 ^ 40 * 6808109 * 2
def baseEnd_6808109 : Nat := 1165277421733602991975861

theorem tailTrace_6808109 : CollatzResearch.WordTrace tailWord_6808109 prefixEnd_6808109 1165277421733602991975861 := by
  unfold tailWord_6808109
  simp only [CollatzResearch.WordTrace]
  refine ⟨248312134892391300292451381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165541423261594200194967587 248312134892391300292451381)
  ·
    refine ⟨23279262646161684402417317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 248312134892391300292451381 23279262646161684402417317)
    ·
      refine ⟨4364861746155315825453247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23279262646161684402417317 4364861746155315825453247)
      ·
        refine ⟨6547292619232973738179871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4364861746155315825453247 6547292619232973738179871)
        ·
          refine ⟨9820938928849460607269807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6547292619232973738179871 9820938928849460607269807)
          ·
            refine ⟨14731408393274190910904711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9820938928849460607269807 14731408393274190910904711)
            ·
              refine ⟨22097112589911286366357067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14731408393274190910904711 22097112589911286366357067)
              ·
                refine ⟨33145668884866929549535601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22097112589911286366357067 33145668884866929549535601)
                ·
                  refine ⟨24859251663650197162151701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33145668884866929549535601 24859251663650197162151701)
                  ·
                    refine ⟨1165277421733602991975861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24859251663650197162151701 1165277421733602991975861)
                    ·
                      rfl

theorem cell23_6808109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_6808109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808109 prefixEnd_6808109 := by exact prefixLift 6808109
  have htrace : WordTrace (prefixWord ++ tailWord_6808109) baseStart_6808109 baseEnd_6808109 := by
    simpa [prefixWord, tailWord_6808109, baseEnd_6808109] using wordTrace_append hprefix tailTrace_6808109
  have hstable : (prefixWord ++ tailWord_6808109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808109).length < 2 ^ (prefixWord ++ tailWord_6808109).sum := by decide
  have hdescent : baseEnd_6808109 < baseStart_6808109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808116 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_6808116 : Nat := 118140960795 + 6808116 * 2 ^ 59
def prefixEnd_6808116 : Nat := 4983230072969 + 3 ^ 40 * 6808116 * 2
def baseEnd_6808116 : Nat := 3495835859565390448540051

theorem tailTrace_6808116 : CollatzResearch.WordTrace tailWord_6808116 prefixEnd_6808116 3495835859565390448540051 := by
  unfold tailWord_6808116
  simp only [CollatzResearch.WordTrace]
  refine ⟨124156195101682970243978101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165541593468910626991970801 124156195101682970243978101)
  ·
    refine ⟨11639643290782778460372947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124156195101682970243978101 11639643290782778460372947)
    ·
      refine ⟨17459464936174167690559421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11639643290782778460372947 17459464936174167690559421)
      ·
        refine ⟨6547299351065312883959783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17459464936174167690559421 6547299351065312883959783)
        ·
          refine ⟨9820949026597969325939675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6547299351065312883959783 9820949026597969325939675)
          ·
            refine ⟨14731423539896953988909513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9820949026597969325939675 14731423539896953988909513)
            ·
              refine ⟨11048567654922715491682135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14731423539896953988909513 11048567654922715491682135)
              ·
                refine ⟨16572851482384073237523203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11048567654922715491682135 16572851482384073237523203)
                ·
                  refine ⟨24859277223576109856284805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16572851482384073237523203 24859277223576109856284805)
                  ·
                    refine ⟨4661114479420520598053401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24859277223576109856284805 4661114479420520598053401)
                    ·
                      refine ⟨3495835859565390448540051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4661114479420520598053401 3495835859565390448540051)
                      ·
                        rfl

theorem cell23_6808116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_6808116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808116 prefixEnd_6808116 := by exact prefixLift 6808116
  have htrace : WordTrace (prefixWord ++ tailWord_6808116) baseStart_6808116 baseEnd_6808116 := by
    simpa [prefixWord, tailWord_6808116, baseEnd_6808116] using wordTrace_append hprefix tailTrace_6808116
  have hstable : (prefixWord ++ tailWord_6808116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808116).length < 2 ^ (prefixWord ++ tailWord_6808116).sum := by decide
  have hdescent : baseEnd_6808116 < baseStart_6808116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808135 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 2, 5]
def baseStart_6808135 : Nat := 118140960795 + 6808135 * 2 ^ 59
def prefixEnd_6808135 : Nat := 4983230072969 + 3 ^ 40 * 6808135 * 2
def baseEnd_6808135 : Nat := 1165281871899275291400821

theorem tailTrace_6808135 : CollatzResearch.WordTrace tailWord_6808135 prefixEnd_6808135 1165281871899275291400821 := by
  unfold tailWord_6808135
  simp only [CollatzResearch.WordTrace]
  refine ⟨248313083190297106732897859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165542055460198071155265239 248313083190297106732897859)
  ·
    refine ⟨372469624785445660099346789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248313083190297106732897859 372469624785445660099346789)
    ·
      refine ⟨69838054647271061268627523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372469624785445660099346789 69838054647271061268627523)
      ·
        refine ⟨104757081970906591902941285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69838054647271061268627523 104757081970906591902941285)
        ·
          refine ⟨19641952869544985981801491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104757081970906591902941285 19641952869544985981801491)
          ·
            refine ⟨29462929304317478972702237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19641952869544985981801491 29462929304317478972702237)
            ·
              refine ⟨11048598489119054614763339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29462929304317478972702237 11048598489119054614763339)
              ·
                refine ⟨16572897733678581922145009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11048598489119054614763339 16572897733678581922145009)
                ·
                  refine ⟨12429673300258936441608757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16572897733678581922145009 12429673300258936441608757)
                  ·
                    refine ⟨1165281871899275291400821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12429673300258936441608757 1165281871899275291400821)
                    ·
                      rfl

theorem cell23_6808135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_6808135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808135 prefixEnd_6808135 := by exact prefixLift 6808135
  have htrace : WordTrace (prefixWord ++ tailWord_6808135) baseStart_6808135 baseEnd_6808135 := by
    simpa [prefixWord, tailWord_6808135, baseEnd_6808135] using wordTrace_append hprefix tailTrace_6808135
  have hstable : (prefixWord ++ tailWord_6808135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808135).length < 2 ^ (prefixWord ++ tailWord_6808135).sum := by decide
  have hdescent : baseEnd_6808135 < baseStart_6808135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808208 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 7, 5]
def baseStart_6808208 : Nat := 118140960795 + 6808208 * 2 ^ 59
def prefixEnd_6808208 : Nat := 4983230072969 + 3 ^ 40 * 6808208 * 2
def baseEnd_6808208 : Nat := 1165294366595201362863209

theorem tailTrace_6808208 : CollatzResearch.WordTrace tailWord_6808208 prefixEnd_6808208 1165294366595201362863209 := by
  unfold tailWord_6808208
  simp only [CollatzResearch.WordTrace]
  refine ⟨124157872859516320100152639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165543830479355093466870185 124157872859516320100152639)
  ·
    refine ⟨186236809289274480150228959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124157872859516320100152639 186236809289274480150228959)
    ·
      refine ⟨279355213933911720225343439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186236809289274480150228959 279355213933911720225343439)
      ·
        refine ⟨419032820900867580338015159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279355213933911720225343439 419032820900867580338015159)
        ·
          refine ⟨628549231351301370507022739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419032820900867580338015159 628549231351301370507022739)
          ·
            refine ⟨942823847026952055760534109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628549231351301370507022739 942823847026952055760534109)
            ·
              refine ⟨353558942635107020910200291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 942823847026952055760534109 353558942635107020910200291)
              ·
                refine ⟨530338413952660531365300437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353558942635107020910200291 530338413952660531365300437)
                ·
                  refine ⟨12429806577015481203874229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 530338413952660531365300437 12429806577015481203874229)
                  ·
                    refine ⟨1165294366595201362863209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12429806577015481203874229 1165294366595201362863209)
                    ·
                      rfl

theorem cell23_6808208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 7, 5].length) (baseStart_6808208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808208 prefixEnd_6808208 := by exact prefixLift 6808208
  have htrace : WordTrace (prefixWord ++ tailWord_6808208) baseStart_6808208 baseEnd_6808208 := by
    simpa [prefixWord, tailWord_6808208, baseEnd_6808208] using wordTrace_append hprefix tailTrace_6808208
  have hstable : (prefixWord ++ tailWord_6808208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808208).length < 2 ^ (prefixWord ++ tailWord_6808208).sum := by decide
  have hdescent : baseEnd_6808208 < baseStart_6808208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808248 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 2, 5, 5]
def baseStart_6808248 : Nat := 118140960795 + 6808248 * 2 ^ 59
def prefixEnd_6808248 : Nat := 4983230072969 + 3 ^ 40 * 6808248 * 2
def baseEnd_6808248 : Nat := 3495903639011783932089443

theorem tailTrace_6808248 : CollatzResearch.WordTrace tailWord_6808248 prefixEnd_6808248 3495903639011783932089443 := by
  unfold tailWord_6808248
  simp only [CollatzResearch.WordTrace]
  refine ⟨124158602319443863515880699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165544803092591818021174265 124158602319443863515880699)
  ·
    refine ⟨186237903479165795273821049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124158602319443863515880699 186237903479165795273821049)
    ·
      refine ⟨139678427609374346455365787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186237903479165795273821049 139678427609374346455365787)
      ·
        refine ⟨209517641414061519683048681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139678427609374346455365787 209517641414061519683048681)
        ·
          refine ⟨157138231060546139762286511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209517641414061519683048681 157138231060546139762286511)
          ·
            refine ⟨235707346590819209643429767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157138231060546139762286511 235707346590819209643429767)
            ·
              refine ⟨353561019886228814465144651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235707346590819209643429767 353561019886228814465144651)
              ·
                refine ⟨530341529829343221697716977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353561019886228814465144651 530341529829343221697716977)
                ·
                  refine ⟨397756147372007416273287733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 530341529829343221697716977 397756147372007416273287733)
                  ·
                    refine ⟨37289638816125695275620725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 397756147372007416273287733 37289638816125695275620725)
                    ·
                      refine ⟨3495903639011783932089443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37289638816125695275620725 3495903639011783932089443)
                      ·
                        rfl

theorem cell23_6808248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_6808248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808248 prefixEnd_6808248 := by exact prefixLift 6808248
  have htrace : WordTrace (prefixWord ++ tailWord_6808248) baseStart_6808248 baseEnd_6808248 := by
    simpa [prefixWord, tailWord_6808248, baseEnd_6808248] using wordTrace_append hprefix tailTrace_6808248
  have hstable : (prefixWord ++ tailWord_6808248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808248).length < 2 ^ (prefixWord ++ tailWord_6808248).sum := by decide
  have hdescent : baseEnd_6808248 < baseStart_6808248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808255 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 1, 6]
def baseStart_6808255 : Nat := 118140960795 + 6808255 * 2 ^ 59
def prefixEnd_6808255 : Nat := 4983230072969 + 3 ^ 40 * 6808255 * 2
def baseEnd_6808255 : Nat := 1165302411125455134900637

theorem tailTrace_6808255 : CollatzResearch.WordTrace tailWord_6808255 prefixEnd_6808255 1165302411125455134900637 := by
  unfold tailWord_6808255
  simp only [CollatzResearch.WordTrace]
  refine ⟨248317459949862367227266219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165544973299908244818177479 248317459949862367227266219)
  ·
    refine ⟨372476189924793550840899329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248317459949862367227266219 372476189924793550840899329)
    ·
      refine ⟨279357142443595163130674497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372476189924793550840899329 279357142443595163130674497)
      ·
        refine ⟨209517856832696372348005873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279357142443595163130674497 209517856832696372348005873)
        ·
          refine ⟨157138392624522279261004405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209517856832696372348005873 157138392624522279261004405)
          ·
            refine ⟨14731724308548963680719163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157138392624522279261004405 14731724308548963680719163)
            ·
              refine ⟨22097586462823445521078745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14731724308548963680719163 22097586462823445521078745)
              ·
                refine ⟨16573189847117584140809059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22097586462823445521078745 16573189847117584140809059)
                ·
                  refine ⟨24859784770676376211213589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16573189847117584140809059 24859784770676376211213589)
                  ·
                    refine ⟨1165302411125455134900637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24859784770676376211213589 1165302411125455134900637)
                    ·
                      rfl

theorem cell23_6808255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 6].length) (baseStart_6808255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808255 prefixEnd_6808255 := by exact prefixLift 6808255
  have htrace : WordTrace (prefixWord ++ tailWord_6808255) baseStart_6808255 baseEnd_6808255 := by
    simpa [prefixWord, tailWord_6808255, baseEnd_6808255] using wordTrace_append hprefix tailTrace_6808255
  have hstable : (prefixWord ++ tailWord_6808255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808255).length < 2 ^ (prefixWord ++ tailWord_6808255).sum := by decide
  have hdescent : baseEnd_6808255 < baseStart_6808255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808292 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 1, 2, 4]
def baseStart_6808292 : Nat := 118140960795 + 6808292 * 2 ^ 59
def prefixEnd_6808292 : Nat := 4983230072969 + 3 ^ 40 * 6808292 * 2
def baseEnd_6808292 : Nat := 3495926232160581759939241

theorem tailTrace_6808292 : CollatzResearch.WordTrace tailWord_6808292 prefixEnd_6808292 3495926232160581759939241 := by
  unfold tailWord_6808292
  simp only [CollatzResearch.WordTrace]
  refine ⟨124159404725364161273181565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165545872967152215030908753 124159404725364161273181565)
  ·
    refine ⟨46559776772011560477443087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124159404725364161273181565 46559776772011560477443087)
    ·
      refine ⟨69839665158017340716164631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46559776772011560477443087 69839665158017340716164631)
      ·
        refine ⟨104759497737026011074246947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69839665158017340716164631 104759497737026011074246947)
        ·
          refine ⟨157139246605539016611370421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104759497737026011074246947 157139246605539016611370421)
          ·
            refine ⟨14731804369269282807315977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157139246605539016611370421 14731804369269282807315977)
            ·
              refine ⟨11048853276951962105486983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14731804369269282807315977 11048853276951962105486983)
              ·
                refine ⟨16573279915427943158230475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11048853276951962105486983 16573279915427943158230475)
                ·
                  refine ⟨24859919873141914737345713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16573279915427943158230475 24859919873141914737345713)
                  ·
                    refine ⟨18644939904856436053009285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24859919873141914737345713 18644939904856436053009285)
                    ·
                      refine ⟨3495926232160581759939241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18644939904856436053009285 3495926232160581759939241)
                      ·
                        rfl

theorem cell23_6808292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_6808292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808292 prefixEnd_6808292 := by exact prefixLift 6808292
  have htrace : WordTrace (prefixWord ++ tailWord_6808292) baseStart_6808292 baseEnd_6808292 := by
    simpa [prefixWord, tailWord_6808292, baseEnd_6808292] using wordTrace_append hprefix tailTrace_6808292
  have hstable : (prefixWord ++ tailWord_6808292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808292).length < 2 ^ (prefixWord ++ tailWord_6808292).sum := by decide
  have hdescent : baseEnd_6808292 < baseStart_6808292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808296 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 3, 2, 2]
def baseStart_6808296 : Nat := 118140960795 + 6808296 * 2 ^ 59
def prefixEnd_6808296 : Nat := 4983230072969 + 3 ^ 40 * 6808296 * 2
def baseEnd_6808296 : Nat := 3495928286083199744289223

theorem tailTrace_6808296 : CollatzResearch.WordTrace tailWord_6808296 prefixEnd_6808296 3495928286083199744289223 := by
  unfold tailWord_6808296
  simp only [CollatzResearch.WordTrace]
  refine ⟨124159477671356915614754371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165545970228475887486339161 124159477671356915614754371)
  ·
    refine ⟨186239216507035373422131557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124159477671356915614754371 186239216507035373422131557)
    ·
      refine ⟨34919853095069132516649667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186239216507035373422131557 34919853095069132516649667)
      ·
        refine ⟨52379779642603698774974501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34919853095069132516649667 52379779642603698774974501)
        ·
          refine ⟨9821208682988193520307719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52379779642603698774974501 9821208682988193520307719)
          ·
            refine ⟨14731813024482290280461579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9821208682988193520307719 14731813024482290280461579)
            ·
              refine ⟨22097719536723435420692369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14731813024482290280461579 22097719536723435420692369)
              ·
                refine ⟨16573289652542576565519277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22097719536723435420692369 16573289652542576565519277)
                ·
                  refine ⟨6214983619703466212069729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16573289652542576565519277 6214983619703466212069729)
                  ·
                    refine ⟨4661237714777599659052297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6214983619703466212069729 4661237714777599659052297)
                    ·
                      refine ⟨3495928286083199744289223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4661237714777599659052297 3495928286083199744289223)
                      ·
                        rfl

theorem cell23_6808296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_6808296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808296 prefixEnd_6808296 := by exact prefixLift 6808296
  have htrace : WordTrace (prefixWord ++ tailWord_6808296) baseStart_6808296 baseEnd_6808296 := by
    simpa [prefixWord, tailWord_6808296, baseEnd_6808296] using wordTrace_append hprefix tailTrace_6808296
  have hstable : (prefixWord ++ tailWord_6808296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808296).length < 2 ^ (prefixWord ++ tailWord_6808296).sum := by decide
  have hdescent : baseEnd_6808296 < baseStart_6808296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808302 : List Nat := [4, 1, 2, 1, 1, 4, 3, 7]
def baseStart_6808302 : Nat := 118140960795 + 6808302 * 2 ^ 59
def prefixEnd_6808302 : Nat := 4983230072969 + 3 ^ 40 * 6808302 * 2
def baseEnd_6808302 : Nat := 129478939517300989659785

theorem tailTrace_6808302 : CollatzResearch.WordTrace tailWord_6808302 prefixEnd_6808302 129478939517300989659785 := by
  unfold tailWord_6808302
  simp only [CollatzResearch.WordTrace]
  refine ⟨31039896772586511781778395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165546116120461396169484773 31039896772586511781778395)
  ·
    refine ⟨46559845158879767672667593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31039896772586511781778395 46559845158879767672667593)
    ·
      refine ⟨34919883869159825754500695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46559845158879767672667593 34919883869159825754500695)
      ·
        refine ⟨52379825803739738631751043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34919883869159825754500695 52379825803739738631751043)
        ·
          refine ⟨78569738705609607947626565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52379825803739738631751043 78569738705609607947626565)
          ·
            refine ⟨14731826007301801490179981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78569738705609607947626565 14731826007301801490179981)
            ·
              refine ⟨5524434752738175558817493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14731826007301801490179981 5524434752738175558817493)
              ·
                refine ⟨129478939517300989659785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5524434752738175558817493 129478939517300989659785)
                ·
                  rfl

theorem cell23_6808302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 7].length) (baseStart_6808302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808302 prefixEnd_6808302 := by exact prefixLift 6808302
  have htrace : WordTrace (prefixWord ++ tailWord_6808302) baseStart_6808302 baseEnd_6808302 := by
    simpa [prefixWord, tailWord_6808302, baseEnd_6808302] using wordTrace_append hprefix tailTrace_6808302
  have hstable : (prefixWord ++ tailWord_6808302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808302).length < 2 ^ (prefixWord ++ tailWord_6808302).sum := by decide
  have hdescent : baseEnd_6808302 < baseStart_6808302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808312 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 4, 1, 3]
def baseStart_6808312 : Nat := 118140960795 + 6808312 * 2 ^ 59
def prefixEnd_6808312 : Nat := 4983230072969 + 3 ^ 40 * 6808312 * 2
def baseEnd_6808312 : Nat := 3495936501773671681689149

theorem tailTrace_6808312 : CollatzResearch.WordTrace tailWord_6808312 prefixEnd_6808312 3495936501773671681689149 := by
  unfold tailWord_6808312
  simp only [CollatzResearch.WordTrace]
  refine ⟨124159769455327932981045595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165546359273770577308060793 124159769455327932981045595)
  ·
    refine ⟨186239654182991899471568393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124159769455327932981045595 186239654182991899471568393)
    ·
      refine ⟨139679740637243924603676295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186239654182991899471568393 139679740637243924603676295)
      ·
        refine ⟨209519610955865886905514443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139679740637243924603676295 209519610955865886905514443)
        ·
          refine ⟨314279416433798830358271665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209519610955865886905514443 314279416433798830358271665)
          ·
            refine ⟨235709562325349122768703749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314279416433798830358271665 235709562325349122768703749)
            ·
              refine ⟨44195542936002960519131953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235709562325349122768703749 44195542936002960519131953)
              ·
                refine ⟨33146657202002220389348965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44195542936002960519131953 33146657202002220389348965)
                ·
                  refine ⟨6214998225375416323002931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33146657202002220389348965 6214998225375416323002931)
                  ·
                    refine ⟨9322497338063124484504397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6214998225375416323002931 9322497338063124484504397)
                    ·
                      refine ⟨3495936501773671681689149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9322497338063124484504397 3495936501773671681689149)
                      ·
                        rfl

theorem cell23_6808312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_6808312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808312 prefixEnd_6808312 := by exact prefixLift 6808312
  have htrace : WordTrace (prefixWord ++ tailWord_6808312) baseStart_6808312 baseEnd_6808312 := by
    simpa [prefixWord, tailWord_6808312, baseEnd_6808312] using wordTrace_append hprefix tailTrace_6808312
  have hstable : (prefixWord ++ tailWord_6808312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808312).length < 2 ^ (prefixWord ++ tailWord_6808312).sum := by decide
  have hdescent : baseEnd_6808312 < baseStart_6808312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808316 : List Nat := [2, 2, 2, 1, 3, 4, 2, 1, 1, 2, 3]
def baseStart_6808316 : Nat := 118140960795 + 6808316 * 2 ^ 59
def prefixEnd_6808316 : Nat := 4983230072969 + 3 ^ 40 * 6808316 * 2
def baseEnd_6808316 : Nat := 3495938555696289666039131

theorem tailTrace_6808316 : CollatzResearch.WordTrace tailWord_6808316 prefixEnd_6808316 3495938555696289666039131 := by
  unfold tailWord_6808316
  simp only [CollatzResearch.WordTrace]
  refine ⟨124159842401320687322618401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165546456535094249763491201 124159842401320687322618401)
  ·
    refine ⟨93119881800990515491963801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124159842401320687322618401 93119881800990515491963801)
    ·
      refine ⟨69839911350742886618972851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93119881800990515491963801 69839911350742886618972851)
      ·
        refine ⟨104759867026114329928459277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69839911350742886618972851 104759867026114329928459277)
        ·
          refine ⟨39284950134792873723172229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104759867026114329928459277 39284950134792873723172229)
          ·
            refine ⟨7365928150273663823094793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39284950134792873723172229 7365928150273663823094793)
            ·
              refine ⟨5524446112705247867321095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7365928150273663823094793 5524446112705247867321095)
              ·
                refine ⟨8286669169057871800981643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5524446112705247867321095 8286669169057871800981643)
                ·
                  refine ⟨12430003753586807701472465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8286669169057871800981643 12430003753586807701472465)
                  ·
                    refine ⟨9322502815190105776104349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12430003753586807701472465 9322502815190105776104349)
                    ·
                      refine ⟨3495938555696289666039131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9322502815190105776104349 3495938555696289666039131)
                      ·
                        rfl

theorem cell23_6808316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_6808316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808316 prefixEnd_6808316 := by exact prefixLift 6808316
  have htrace : WordTrace (prefixWord ++ tailWord_6808316) baseStart_6808316 baseEnd_6808316 := by
    simpa [prefixWord, tailWord_6808316, baseEnd_6808316] using wordTrace_append hprefix tailTrace_6808316
  have hstable : (prefixWord ++ tailWord_6808316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808316).length < 2 ^ (prefixWord ++ tailWord_6808316).sum := by decide
  have hdescent : baseEnd_6808316 < baseStart_6808316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808329 : List Nat := [1, 2, 1, 1, 3, 2, 5, 2, 2, 1, 3]
def baseStart_6808329 : Nat := 118140960795 + 6808329 * 2 ^ 59
def prefixEnd_6808329 : Nat := 4983230072969 + 3 ^ 40 * 6808329 * 2
def baseEnd_6808329 : Nat := 3495945230944798115176571

theorem tailTrace_6808329 : CollatzResearch.WordTrace tailWord_6808329 prefixEnd_6808329 3495945230944798115176571 := by
  unfold tailWord_6808329
  simp only [CollatzResearch.WordTrace]
  refine ⟨248320158951594277865460041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165546772634396185243640027 248320158951594277865460041)
  ·
    refine ⟨186240119213695708399095031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248320158951594277865460041 186240119213695708399095031)
    ·
      refine ⟨279360178820543562598642547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186240119213695708399095031 279360178820543562598642547)
      ·
        refine ⟨419040268230815343897963821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279360178820543562598642547 419040268230815343897963821)
        ·
          refine ⟨157140100586555753961736433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 419040268230815343897963821 157140100586555753961736433)
          ·
            refine ⟨117855075439916815471302325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157140100586555753961736433 117855075439916815471302325)
            ·
              refine ⟨11048913322492201450434593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117855075439916815471302325 11048913322492201450434593)
              ·
                refine ⟨8286684991869151087825945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11048913322492201450434593 8286684991869151087825945)
                ·
                  refine ⟨6215013743901863315869459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8286684991869151087825945 6215013743901863315869459)
                  ·
                    refine ⟨9322520615852794973804189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6215013743901863315869459 9322520615852794973804189)
                    ·
                      refine ⟨3495945230944798115176571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9322520615852794973804189 3495945230944798115176571)
                      ·
                        rfl

theorem cell23_6808329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 1, 3].length) (baseStart_6808329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808329 prefixEnd_6808329 := by exact prefixLift 6808329
  have htrace : WordTrace (prefixWord ++ tailWord_6808329) baseStart_6808329 baseEnd_6808329 := by
    simpa [prefixWord, tailWord_6808329, baseEnd_6808329] using wordTrace_append hprefix tailTrace_6808329
  have hstable : (prefixWord ++ tailWord_6808329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808329).length < 2 ^ (prefixWord ++ tailWord_6808329).sum := by decide
  have hdescent : baseEnd_6808329 < baseStart_6808329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808346 : List Nat := [3, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3]
def baseStart_6808346 : Nat := 118140960795 + 6808346 * 2 ^ 59
def prefixEnd_6808346 : Nat := 4983230072969 + 3 ^ 40 * 6808346 * 2
def baseEnd_6808346 : Nat := 3495953960115924548663993

theorem tailTrace_6808346 : CollatzResearch.WordTrace tailWord_6808346 prefixEnd_6808346 3495953960115924548663993 := by
  unfold tailWord_6808346
  simp only [CollatzResearch.WordTrace]
  refine ⟨62080194748133172442207223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165547185995021793179219261 62080194748133172442207223)
  ·
    refine ⟨93120292122199758663310835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62080194748133172442207223 93120292122199758663310835)
    ·
      refine ⟨139680438183299637994966253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93120292122199758663310835 139680438183299637994966253)
      ·
        refine ⟨52380164318737364248112345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139680438183299637994966253 52380164318737364248112345)
        ·
          refine ⟨39285123239053023186084259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52380164318737364248112345 39285123239053023186084259)
          ·
            refine ⟨58927684858579534779126389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39285123239053023186084259 58927684858579534779126389)
            ·
              refine ⟨5524470455491831385543099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58927684858579534779126389 5524470455491831385543099)
              ·
                refine ⟨8286705683237747078314649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5524470455491831385543099 8286705683237747078314649)
                ·
                  refine ⟨6215029262428310308735987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8286705683237747078314649 6215029262428310308735987)
                  ·
                    refine ⟨9322543893642465463103981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6215029262428310308735987 9322543893642465463103981)
                    ·
                      refine ⟨3495953960115924548663993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9322543893642465463103981 3495953960115924548663993)
                      ·
                        rfl

theorem cell23_6808346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_6808346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808346 prefixEnd_6808346 := by exact prefixLift 6808346
  have htrace : WordTrace (prefixWord ++ tailWord_6808346) baseStart_6808346 baseEnd_6808346 := by
    simpa [prefixWord, tailWord_6808346, baseEnd_6808346] using wordTrace_append hprefix tailTrace_6808346
  have hstable : (prefixWord ++ tailWord_6808346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808346).length < 2 ^ (prefixWord ++ tailWord_6808346).sum := by decide
  have hdescent : baseEnd_6808346 < baseStart_6808346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808355 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 5]
def baseStart_6808355 : Nat := 118140960795 + 6808355 * 2 ^ 59
def prefixEnd_6808355 : Nat := 4983230072969 + 3 ^ 40 * 6808355 * 2
def baseEnd_6808355 : Nat := 3495958581441815013451451

theorem tailTrace_6808355 : CollatzResearch.WordTrace tailWord_6808355 prefixEnd_6808355 3495958581441815013451451 := by
  unfold tailWord_6808355
  simp only [CollatzResearch.WordTrace]
  refine ⟨248321107249500084305906519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165547404833000056203937679 248321107249500084305906519)
  ·
    refine ⟨372481660874250126458859779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248321107249500084305906519 372481660874250126458859779)
    ·
      refine ⟨558722491311375189688289669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372481660874250126458859779 558722491311375189688289669)
      ·
        refine ⟨104760467120882848066554313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 558722491311375189688289669 104760467120882848066554313)
        ·
          refine ⟨78570350340662136049915735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104760467120882848066554313 78570350340662136049915735)
          ·
            refine ⟨117855525510993204074873603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78570350340662136049915735 117855525510993204074873603)
            ·
              refine ⟨176783288266489806112310405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117855525510993204074873603 176783288266489806112310405)
              ·
                refine ⟨33146866549966838646058201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176783288266489806112310405 33146866549966838646058201)
                ·
                  refine ⟨24860149912475128984543651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33146866549966838646058201 24860149912475128984543651)
                  ·
                    refine ⟨37290224868712693476815477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24860149912475128984543651 37290224868712693476815477)
                    ·
                      refine ⟨3495958581441815013451451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37290224868712693476815477 3495958581441815013451451)
                      ·
                        rfl

theorem cell23_6808355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_6808355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808355 prefixEnd_6808355 := by exact prefixLift 6808355
  have htrace : WordTrace (prefixWord ++ tailWord_6808355) baseStart_6808355 baseEnd_6808355 := by
    simpa [prefixWord, tailWord_6808355, baseEnd_6808355] using wordTrace_append hprefix tailTrace_6808355
  have hstable : (prefixWord ++ tailWord_6808355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808355).length < 2 ^ (prefixWord ++ tailWord_6808355).sum := by decide
  have hdescent : baseEnd_6808355 < baseStart_6808355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808369 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 6, 2, 2]
def baseStart_6808369 : Nat := 118140960795 + 6808369 * 2 ^ 59
def prefixEnd_6808369 : Nat := 4983230072969 + 3 ^ 40 * 6808369 * 2
def baseEnd_6808369 : Nat := 3495965770170977958676387

theorem tailTrace_6808369 : CollatzResearch.WordTrace tailWord_6808369 prefixEnd_6808369 3495965770170977958676387 := by
  unfold tailWord_6808369
  simp only [CollatzResearch.WordTrace]
  refine ⟨248321617871449364696916161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165547745247632909797944107 248321617871449364696916161)
  ·
    refine ⟨186241213403587023522687121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248321617871449364696916161 186241213403587023522687121)
    ·
      refine ⟨139680910052690267642015341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186241213403587023522687121 139680910052690267642015341)
      ·
        refine ⟨52380341269758850365755753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139680910052690267642015341 52380341269758850365755753)
        ·
          refine ⟨39285255952319137774316815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52380341269758850365755753 39285255952319137774316815)
          ·
            refine ⟨58927883928478706661475223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39285255952319137774316815 58927883928478706661475223)
            ·
              refine ⟨88391825892718059992212835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58927883928478706661475223 88391825892718059992212835)
              ·
                refine ⟨132587738839077089988319253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88391825892718059992212835 132587738839077089988319253)
                ·
                  refine ⟨6215050258081738593202465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132587738839077089988319253 6215050258081738593202465)
                  ·
                    refine ⟨4661287693561303944901849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6215050258081738593202465 4661287693561303944901849)
                    ·
                      refine ⟨3495965770170977958676387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4661287693561303944901849 3495965770170977958676387)
                      ·
                        rfl

theorem cell23_6808369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_6808369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808369 prefixEnd_6808369 := by exact prefixLift 6808369
  have htrace : WordTrace (prefixWord ++ tailWord_6808369) baseStart_6808369 baseEnd_6808369 := by
    simpa [prefixWord, tailWord_6808369, baseEnd_6808369] using wordTrace_append hprefix tailTrace_6808369
  have hstable : (prefixWord ++ tailWord_6808369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808369).length < 2 ^ (prefixWord ++ tailWord_6808369).sum := by decide
  have hdescent : baseEnd_6808369 < baseStart_6808369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808397 : List Nat := [1, 6, 1, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_6808397 : Nat := 118140960795 + 6808397 * 2 ^ 59
def prefixEnd_6808397 : Nat := 4983230072969 + 3 ^ 40 * 6808397 * 2
def baseEnd_6808397 : Nat := 3495980147629303849126259

theorem tailTrace_6808397 : CollatzResearch.WordTrace tailWord_6808397 prefixEnd_6808397 3495980147629303849126259 := by
  unfold tailWord_6808397
  simp only [CollatzResearch.WordTrace]
  refine ⟨248322639115347925478935445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165548426076898616985956963 248322639115347925478935445)
  ·
    refine ⟨11640123708531934006825099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 248322639115347925478935445 11640123708531934006825099)
    ·
      refine ⟨17460185562797901010237649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11640123708531934006825099 17460185562797901010237649)
      ·
        refine ⟨13095139172098425757678237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17460185562797901010237649 13095139172098425757678237)
        ·
          refine ⟨4910677189536909659129339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13095139172098425757678237 4910677189536909659129339)
          ·
            refine ⟨7366015784305364488694009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4910677189536909659129339 7366015784305364488694009)
            ·
              refine ⟨5524511838229023366520507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7366015784305364488694009 5524511838229023366520507)
              ·
                refine ⟨8286767757343535049780761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5524511838229023366520507 8286767757343535049780761)
                ·
                  refine ⟨6215075818007651287335571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8286767757343535049780761 6215075818007651287335571)
                  ·
                    refine ⟨9322613727011476931003357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6215075818007651287335571 9322613727011476931003357)
                    ·
                      refine ⟨3495980147629303849126259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9322613727011476931003357 3495980147629303849126259)
                      ·
                        rfl

theorem cell23_6808397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_6808397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808397 prefixEnd_6808397 := by exact prefixLift 6808397
  have htrace : WordTrace (prefixWord ++ tailWord_6808397) baseStart_6808397 baseEnd_6808397 := by
    simpa [prefixWord, tailWord_6808397, baseEnd_6808397] using wordTrace_append hprefix tailTrace_6808397
  have hstable : (prefixWord ++ tailWord_6808397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808397).length < 2 ^ (prefixWord ++ tailWord_6808397).sum := by decide
  have hdescent : baseEnd_6808397 < baseStart_6808397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808402 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_6808402 : Nat := 118140960795 + 6808402 * 2 ^ 59
def prefixEnd_6808402 : Nat := 4983230072969 + 3 ^ 40 * 6808402 * 2
def baseEnd_6808402 : Nat := 3495982715032576329563735

theorem tailTrace_6808402 : CollatzResearch.WordTrace tailWord_6808402 prefixEnd_6808402 3495982715032576329563735 := by
  unfold tailWord_6808402
  simp only [CollatzResearch.WordTrace]
  refine ⟨62080705370082452833216865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165548547653553207555244973 62080705370082452833216865)
  ·
    refine ⟨46560529027561839624912649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62080705370082452833216865 46560529027561839624912649)
    ·
      refine ⟨34920396770671379718684487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46560529027561839624912649 34920396770671379718684487)
      ·
        refine ⟨52380595156007069578026731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34920396770671379718684487 52380595156007069578026731)
        ·
          refine ⟨78570892734010604367040097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52380595156007069578026731 78570892734010604367040097)
          ·
            refine ⟨58928169550507953275280073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78570892734010604367040097 58928169550507953275280073)
            ·
              refine ⟨44196127162880964956460055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58928169550507953275280073 44196127162880964956460055)
              ·
                refine ⟨66294190744321447434690083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44196127162880964956460055 66294190744321447434690083)
                ·
                  refine ⟨99441286116482171152035125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66294190744321447434690083 99441286116482171152035125)
                  ·
                    refine ⟨9322620573420203545503293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99441286116482171152035125 9322620573420203545503293)
                    ·
                      refine ⟨3495982715032576329563735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9322620573420203545503293 3495982715032576329563735)
                      ·
                        rfl

theorem cell23_6808402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_6808402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808402 prefixEnd_6808402 := by exact prefixLift 6808402
  have htrace : WordTrace (prefixWord ++ tailWord_6808402) baseStart_6808402 baseEnd_6808402 := by
    simpa [prefixWord, tailWord_6808402, baseEnd_6808402] using wordTrace_append hprefix tailTrace_6808402
  have hstable : (prefixWord ++ tailWord_6808402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808402).length < 2 ^ (prefixWord ++ tailWord_6808402).sum := by decide
  have hdescent : baseEnd_6808402 < baseStart_6808402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808415 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 7]
def baseStart_6808415 : Nat := 118140960795 + 6808415 * 2 ^ 59
def prefixEnd_6808415 : Nat := 4983230072969 + 3 ^ 40 * 6808415 * 2
def baseEnd_6808415 : Nat := 3495989390281084778701175

theorem tailTrace_6808415 : CollatzResearch.WordTrace tailWord_6808415 prefixEnd_6808415 3495989390281084778701175 := by
  unfold tailWord_6808415
  simp only [CollatzResearch.WordTrace]
  refine ⟨248323295629282714553090699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165548863752855143035393799 248323295629282714553090699)
  ·
    refine ⟨372484943443924071829636049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248323295629282714553090699 372484943443924071829636049)
    ·
      refine ⟨279363707582943053872227037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372484943443924071829636049 279363707582943053872227037)
      ·
        refine ⟨104761390343603645202085139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279363707582943053872227037 104761390343603645202085139)
        ·
          refine ⟨157142085515405467803127709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104761390343603645202085139 157142085515405467803127709)
          ·
            refine ⟨58928282068277050426172891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157142085515405467803127709 58928282068277050426172891)
            ·
              refine ⟨88392423102415575639259337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58928282068277050426172891 88392423102415575639259337)
              ·
                refine ⟨66294317326811681729444503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88392423102415575639259337 66294317326811681729444503)
                ·
                  refine ⟨99441475990217522594166755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66294317326811681729444503 99441475990217522594166755)
                  ·
                    refine ⟨149162213985326283891250133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99441475990217522594166755 149162213985326283891250133)
                    ·
                      refine ⟨3495989390281084778701175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149162213985326283891250133 3495989390281084778701175)
                      ·
                        rfl

theorem cell23_6808415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_6808415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808415 prefixEnd_6808415 := by exact prefixLift 6808415
  have htrace : WordTrace (prefixWord ++ tailWord_6808415) baseStart_6808415 baseEnd_6808415 := by
    simpa [prefixWord, tailWord_6808415, baseEnd_6808415] using wordTrace_append hprefix tailTrace_6808415
  have hstable : (prefixWord ++ tailWord_6808415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808415).length < 2 ^ (prefixWord ++ tailWord_6808415).sum := by decide
  have hdescent : baseEnd_6808415 < baseStart_6808415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808465 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 10]
def baseStart_6808465 : Nat := 118140960795 + 6808465 * 2 ^ 59
def prefixEnd_6808465 : Nat := 4983230072969 + 3 ^ 40 * 6808465 * 2
def baseEnd_6808465 : Nat := 388446118257089953675105

theorem tailTrace_6808465 : CollatzResearch.WordTrace tailWord_6808465 prefixEnd_6808465 388446118257089953675105 := by
  unfold tailWord_6808465
  simp only [CollatzResearch.WordTrace]
  refine ⟨248325119279101573092410849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165550079519401048728273899 248325119279101573092410849)
  ·
    refine ⟨186243839459326179819308137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248325119279101573092410849 186243839459326179819308137)
    ·
      refine ⟨139682879594494634864481103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186243839459326179819308137 139682879594494634864481103)
      ·
        refine ⟨209524319391741952296721655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139682879594494634864481103 209524319391741952296721655)
        ·
          refine ⟨314286479087612928445082483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209524319391741952296721655 314286479087612928445082483)
          ·
            refine ⟨471429718631419392667623725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314286479087612928445082483 471429718631419392667623725)
            ·
              refine ⟨176786144486782272250358897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 471429718631419392667623725 176786144486782272250358897)
              ·
                refine ⟨132589608365086704187769173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176786144486782272250358897 132589608365086704187769173)
                ·
                  refine ⟨388446118257089953675105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 132589608365086704187769173 388446118257089953675105)
                  ·
                    rfl

theorem cell23_6808465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 10].length) (baseStart_6808465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808465 prefixEnd_6808465 := by exact prefixLift 6808465
  have htrace : WordTrace (prefixWord ++ tailWord_6808465) baseStart_6808465 baseEnd_6808465 := by
    simpa [prefixWord, tailWord_6808465, baseEnd_6808465] using wordTrace_append hprefix tailTrace_6808465
  have hstable : (prefixWord ++ tailWord_6808465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808465).length < 2 ^ (prefixWord ++ tailWord_6808465).sum := by decide
  have hdescent : baseEnd_6808465 < baseStart_6808465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808469 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 3, 4]
def baseStart_6808469 : Nat := 118140960795 + 6808469 * 2 ^ 59
def prefixEnd_6808469 : Nat := 4983230072969 + 3 ^ 40 * 6808469 * 2
def baseEnd_6808469 : Nat := 1165339039412142522475309

theorem tailTrace_6808469 : CollatzResearch.WordTrace tailWord_6808469 prefixEnd_6808469 1165339039412142522475309 := by
  unfold tailWord_6808469
  simp only [CollatzResearch.WordTrace]
  refine ⟨248325265171087081775556461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165550176780724721183704307 248325265171087081775556461)
  ·
    refine ⟨93121974439157655665833673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248325265171087081775556461 93121974439157655665833673)
    ·
      refine ⟨69841480829368241749375255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93121974439157655665833673 69841480829368241749375255)
      ·
        refine ⟨104762221244052362624062883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69841480829368241749375255 104762221244052362624062883)
        ·
          refine ⟨157143331866078543936094325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104762221244052362624062883 157143331866078543936094325)
          ·
            refine ⟨14732187362444863494008843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157143331866078543936094325 14732187362444863494008843)
            ·
              refine ⟨22098281043667295241013265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14732187362444863494008843 22098281043667295241013265)
              ·
                refine ⟨16573710782750471430759949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22098281043667295241013265 16573710782750471430759949)
                ·
                  refine ⟨6215141543531426786534981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16573710782750471430759949 6215141543531426786534981)
                  ·
                    refine ⟨1165339039412142522475309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6215141543531426786534981 1165339039412142522475309)
                    ·
                      rfl

theorem cell23_6808469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_6808469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808469 prefixEnd_6808469 := by exact prefixLift 6808469
  have htrace : WordTrace (prefixWord ++ tailWord_6808469) baseStart_6808469 baseEnd_6808469 := by
    simpa [prefixWord, tailWord_6808469, baseEnd_6808469] using wordTrace_append hprefix tailTrace_6808469
  have hstable : (prefixWord ++ tailWord_6808469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808469).length < 2 ^ (prefixWord ++ tailWord_6808469).sum := by decide
  have hdescent : baseEnd_6808469 < baseStart_6808469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808479 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 3]
def baseStart_6808479 : Nat := 118140960795 + 6808479 * 2 ^ 59
def prefixEnd_6808479 : Nat := 4983230072969 + 3 ^ 40 * 6808479 * 2
def baseEnd_6808479 : Nat := 3496022253042972528300881

theorem tailTrace_6808479 : CollatzResearch.WordTrace tailWord_6808479 prefixEnd_6808479 3496022253042972528300881 := by
  unfold tailWord_6808479
  simp only [CollatzResearch.WordTrace]
  refine ⟨248325629901050853483420491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165550419934033902322280327 248325629901050853483420491)
  ·
    refine ⟨372488444851576280225130737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248325629901050853483420491 372488444851576280225130737)
    ·
      refine ⟨279366333638682210168848053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372488444851576280225130737 279366333638682210168848053)
      ·
        refine ⟨26190593778626457203329505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279366333638682210168848053 26190593778626457203329505)
        ·
          refine ⟨19642945333969842902497129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26190593778626457203329505 19642945333969842902497129)
          ·
            refine ⟨14732209000477382176872847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19642945333969842902497129 14732209000477382176872847)
            ·
              refine ⟨22098313500716073265309271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14732209000477382176872847 22098313500716073265309271)
              ·
                refine ⟨33147470251074109897963907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22098313500716073265309271 33147470251074109897963907)
                ·
                  refine ⟨49721205376611164846945861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33147470251074109897963907 49721205376611164846945861)
                  ·
                    refine ⟨9322726008114593408802349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49721205376611164846945861 9322726008114593408802349)
                    ·
                      refine ⟨3496022253042972528300881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9322726008114593408802349 3496022253042972528300881)
                      ·
                        rfl

theorem cell23_6808479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_6808479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808479 prefixEnd_6808479 := by exact prefixLift 6808479
  have htrace : WordTrace (prefixWord ++ tailWord_6808479) baseStart_6808479 baseEnd_6808479 := by
    simpa [prefixWord, tailWord_6808479, baseEnd_6808479] using wordTrace_append hprefix tailTrace_6808479
  have hstable : (prefixWord ++ tailWord_6808479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808479).length < 2 ^ (prefixWord ++ tailWord_6808479).sum := by decide
  have hdescent : baseEnd_6808479 < baseStart_6808479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808519 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 1, 5, 2]
def baseStart_6808519 : Nat := 118140960795 + 6808519 * 2 ^ 59
def prefixEnd_6808519 : Nat := 4983230072969 + 3 ^ 40 * 6808519 * 2
def baseEnd_6808519 : Nat := 3496042792269152371800697

theorem tailTrace_6808519 : CollatzResearch.WordTrace tailWord_6808519 prefixEnd_6808519 3496042792269152371800697 := by
  unfold tailWord_6808519
  simp only [CollatzResearch.WordTrace]
  refine ⟨248327088820905940314876611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165551392547270626876584407 248327088820905940314876611)
  ·
    refine ⟨372490633231358910472314917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248327088820905940314876611 372490633231358910472314917)
    ·
      refine ⟨69841993730879795713559047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372490633231358910472314917 69841993730879795713559047)
      ·
        refine ⟨104762990596319693570338571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69841993730879795713559047 104762990596319693570338571)
        ·
          refine ⟨157144485894479540355507857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104762990596319693570338571 157144485894479540355507857)
          ·
            refine ⟨117858364420859655266630893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157144485894479540355507857 117858364420859655266630893)
            ·
              refine ⟨44196886657822370724986585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117858364420859655266630893 44196886657822370724986585)
              ·
                refine ⟨33147664993366778043739939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44196886657822370724986585 33147664993366778043739939)
                ·
                  refine ⟨49721497490050167065609909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33147664993366778043739939 49721497490050167065609909)
                  ·
                    refine ⟨4661390389692203162400929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49721497490050167065609909 4661390389692203162400929)
                    ·
                      refine ⟨3496042792269152371800697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4661390389692203162400929 3496042792269152371800697)
                      ·
                        rfl

theorem cell23_6808519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_6808519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808519 prefixEnd_6808519 := by exact prefixLift 6808519
  have htrace : WordTrace (prefixWord ++ tailWord_6808519) baseStart_6808519 baseEnd_6808519 := by
    simpa [prefixWord, tailWord_6808519, baseEnd_6808519] using wordTrace_append hprefix tailTrace_6808519
  have hstable : (prefixWord ++ tailWord_6808519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808519).length < 2 ^ (prefixWord ++ tailWord_6808519).sum := by decide
  have hdescent : baseEnd_6808519 < baseStart_6808519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808526 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3]
def baseStart_6808526 : Nat := 118140960795 + 6808526 * 2 ^ 59
def prefixEnd_6808526 : Nat := 4983230072969 + 3 ^ 40 * 6808526 * 2
def baseEnd_6808526 : Nat := 3496046386633733844413165

theorem tailTrace_6808526 : CollatzResearch.WordTrace tailWord_6808526 prefixEnd_6808526 3496046386633733844413165 := by
  unfold tailWord_6808526
  simp only [CollatzResearch.WordTrace]
  refine ⟨31040918016485072563797679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165551562754587053673587621 31040918016485072563797679)
  ·
    refine ⟨46561377024727608845696519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31040918016485072563797679 46561377024727608845696519)
    ·
      refine ⟨69842065537091413268544779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46561377024727608845696519 69842065537091413268544779)
      ·
        refine ⟨104763098305637119902817169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69842065537091413268544779 104763098305637119902817169)
        ·
          refine ⟨78572323729227839927112877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104763098305637119902817169 78572323729227839927112877)
          ·
            refine ⟨29464621398460439972667329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78572323729227839927112877 29464621398460439972667329)
            ·
              refine ⟨22098466048845329979500497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29464621398460439972667329 22098466048845329979500497)
              ·
                refine ⟨16573849536633997484625373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22098466048845329979500497 16573849536633997484625373)
                ·
                  refine ⟨6215193576237749056734515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16573849536633997484625373 6215193576237749056734515)
                  ·
                    refine ⟨9322790364356623585101773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6215193576237749056734515 9322790364356623585101773)
                    ·
                      refine ⟨3496046386633733844413165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9322790364356623585101773 3496046386633733844413165)
                      ·
                        rfl

theorem cell23_6808526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_6808526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808526 prefixEnd_6808526 := by exact prefixLift 6808526
  have htrace : WordTrace (prefixWord ++ tailWord_6808526) baseStart_6808526 baseEnd_6808526 := by
    simpa [prefixWord, tailWord_6808526, baseEnd_6808526] using wordTrace_append hprefix tailTrace_6808526
  have hstable : (prefixWord ++ tailWord_6808526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808526).length < 2 ^ (prefixWord ++ tailWord_6808526).sum := by decide
  have hdescent : baseEnd_6808526 < baseStart_6808526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808529 : List Nat := [1, 2, 2, 1, 2, 1, 6, 2, 1, 5]
def baseStart_6808529 : Nat := 118140960795 + 6808529 * 2 ^ 59
def prefixEnd_6808529 : Nat := 4983230072969 + 3 ^ 40 * 6808529 * 2
def baseEnd_6808529 : Nat := 1165349309025232444225217

theorem tailTrace_6808529 : CollatzResearch.WordTrace tailWord_6808529 prefixEnd_6808529 1165349309025232444225217 := by
  unfold tailWord_6808529
  simp only [CollatzResearch.WordTrace]
  refine ⟨248327453550869712022740641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165551635700579808015160427 248327453550869712022740641)
  ·
    refine ⟨186245590163152284017055481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248327453550869712022740641 186245590163152284017055481)
    ·
      refine ⟨139684192622364213012791611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186245590163152284017055481 139684192622364213012791611)
      ·
        refine ⟨209526288933546319519187417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139684192622364213012791611 209526288933546319519187417)
        ·
          refine ⟨157144716700159739639390563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209526288933546319519187417 157144716700159739639390563)
          ·
            refine ⟨235717075050239609459085845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157144716700159739639390563 235717075050239609459085845)
            ·
              refine ⟨11049237892979981693394649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 235717075050239609459085845 11049237892979981693394649)
              ·
                refine ⟨8286928419734986270045987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11049237892979981693394649 8286928419734986270045987)
                ·
                  refine ⟨12430392629602479405068981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8286928419734986270045987 12430392629602479405068981)
                  ·
                    refine ⟨1165349309025232444225217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12430392629602479405068981 1165349309025232444225217)
                    ·
                      rfl

theorem cell23_6808529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_6808529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808529 prefixEnd_6808529 := by exact prefixLift 6808529
  have htrace : WordTrace (prefixWord ++ tailWord_6808529) baseStart_6808529 baseEnd_6808529 := by
    simpa [prefixWord, tailWord_6808529, baseEnd_6808529] using wordTrace_append hprefix tailTrace_6808529
  have hstable : (prefixWord ++ tailWord_6808529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808529).length < 2 ^ (prefixWord ++ tailWord_6808529).sum := by decide
  have hdescent : baseEnd_6808529 < baseStart_6808529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808559 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 4, 4]
def baseStart_6808559 : Nat := 118140960795 + 6808559 * 2 ^ 59
def prefixEnd_6808559 : Nat := 4983230072969 + 3 ^ 40 * 6808559 * 2
def baseEnd_6808559 : Nat := 1165354443831777405100171

theorem tailTrace_6808559 : CollatzResearch.WordTrace tailWord_6808559 prefixEnd_6808559 1165354443831777405100171 := by
  unfold tailWord_6808559
  simp only [CollatzResearch.WordTrace]
  refine ⟨248328547740761027146332731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165552365160507351430888487 248328547740761027146332731)
  ·
    refine ⟨372492821611141540719499097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248328547740761027146332731 372492821611141540719499097)
    ·
      refine ⟨279369616208356155539624323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372492821611141540719499097 279369616208356155539624323)
      ·
        refine ⟨419054424312534233309436485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279369616208356155539624323 419054424312534233309436485)
        ·
          refine ⟨78572704558600168745519341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 419054424312534233309436485 78572704558600168745519341)
          ·
            refine ⟨29464764209475063279569753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78572704558600168745519341 29464764209475063279569753)
            ·
              refine ⟨22098573157106297459677315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29464764209475063279569753 22098573157106297459677315)
              ·
                refine ⟨33147859735659446189515973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22098573157106297459677315 33147859735659446189515973)
                ·
                  refine ⟨6215223700436146160534245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33147859735659446189515973 6215223700436146160534245)
                  ·
                    refine ⟨1165354443831777405100171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6215223700436146160534245 1165354443831777405100171)
                    ·
                      rfl

theorem cell23_6808559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 4].length) (baseStart_6808559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808559 prefixEnd_6808559 := by exact prefixLift 6808559
  have htrace : WordTrace (prefixWord ++ tailWord_6808559) baseStart_6808559 baseEnd_6808559 := by
    simpa [prefixWord, tailWord_6808559, baseEnd_6808559] using wordTrace_append hprefix tailTrace_6808559
  have hstable : (prefixWord ++ tailWord_6808559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808559).length < 2 ^ (prefixWord ++ tailWord_6808559).sum := by decide
  have hdescent : baseEnd_6808559 < baseStart_6808559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808569 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 3, 2, 3]
def baseStart_6808569 : Nat := 118140960795 + 6808569 * 2 ^ 59
def prefixEnd_6808569 : Nat := 4983230072969 + 3 ^ 40 * 6808569 * 2
def baseEnd_6808569 : Nat := 3496068466301877176175467

theorem tailTrace_6808569 : CollatzResearch.WordTrace tailWord_6808569 prefixEnd_6808569 3496068466301877176175467 := by
  unfold tailWord_6808569
  simp only [CollatzResearch.WordTrace]
  refine ⟨248328912470724798854196761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165552608313816532569464507 248328912470724798854196761)
  ·
    refine ⟨186246684353043599140647571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248328912470724798854196761 186246684353043599140647571)
    ·
      refine ⟨279370026529565398710971357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186246684353043599140647571 279370026529565398710971357)
      ·
        refine ⟨104763759948587024516614259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279370026529565398710971357 104763759948587024516614259)
        ·
          refine ⟨157145639922880536774921389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104763759948587024516614259 157145639922880536774921389)
          ·
            refine ⟨58929614971080201290595521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157145639922880536774921389 58929614971080201290595521)
            ·
              refine ⟨44197211228310150967946641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58929614971080201290595521 44197211228310150967946641)
              ·
                refine ⟨33147908421232613225959981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44197211228310150967946641 33147908421232613225959981)
                ·
                  refine ⟨12430465657962229959734993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33147908421232613225959981 12430465657962229959734993)
                  ·
                    refine ⟨9322849243471672469801245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12430465657962229959734993 9322849243471672469801245)
                    ·
                      refine ⟨3496068466301877176175467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9322849243471672469801245 3496068466301877176175467)
                      ·
                        rfl

theorem cell23_6808569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_6808569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808569 prefixEnd_6808569 := by exact prefixLift 6808569
  have htrace : WordTrace (prefixWord ++ tailWord_6808569) baseStart_6808569 baseEnd_6808569 := by
    simpa [prefixWord, tailWord_6808569, baseEnd_6808569] using wordTrace_append hprefix tailTrace_6808569
  have hstable : (prefixWord ++ tailWord_6808569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808569).length < 2 ^ (prefixWord ++ tailWord_6808569).sum := by decide
  have hdescent : baseEnd_6808569 < baseStart_6808569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808572 : List Nat := [2, 2, 2, 1, 2, 3, 1, 10]
def baseStart_6808572 : Nat := 118140960795 + 6808572 * 2 ^ 59
def prefixEnd_6808572 : Nat := 4983230072969 + 3 ^ 40 * 6808572 * 2
def baseEnd_6808572 : Nat := 129484074323845950534739

theorem tailTrace_6808572 : CollatzResearch.WordTrace tailWord_6808572 prefixEnd_6808572 129484074323845950534739 := by
  unfold tailWord_6808572
  simp only [CollatzResearch.WordTrace]
  refine ⟨124164510944856965183277985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165552681259809286911037313 124164510944856965183277985)
  ·
    refine ⟨93123383208642723887458489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124164510944856965183277985 93123383208642723887458489)
    ·
      refine ⟨69842537406482042915593867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93123383208642723887458489 69842537406482042915593867)
      ·
        refine ⟨104763806109723064373390801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69842537406482042915593867 104763806109723064373390801)
        ·
          refine ⟨78572854582292298280043101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104763806109723064373390801 78572854582292298280043101)
          ·
            refine ⟨29464820468359611855016163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78572854582292298280043101 29464820468359611855016163)
            ·
              refine ⟨44197230702539417782524245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29464820468359611855016163 44197230702539417782524245)
              ·
                refine ⟨129484074323845950534739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44197230702539417782524245 129484074323845950534739)
                ·
                  rfl

theorem cell23_6808572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 10].length) (baseStart_6808572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808572 prefixEnd_6808572 := by exact prefixLift 6808572
  have htrace : WordTrace (prefixWord ++ tailWord_6808572) baseStart_6808572 baseEnd_6808572 := by
    simpa [prefixWord, tailWord_6808572, baseEnd_6808572] using wordTrace_append hprefix tailTrace_6808572
  have hstable : (prefixWord ++ tailWord_6808572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808572).length < 2 ^ (prefixWord ++ tailWord_6808572).sum := by decide
  have hdescent : baseEnd_6808572 < baseStart_6808572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808586 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 3, 2, 3]
def baseStart_6808586 : Nat := 118140960795 + 6808586 * 2 ^ 59
def prefixEnd_6808586 : Nat := 4983230072969 + 3 ^ 40 * 6808586 * 2
def baseEnd_6808586 : Nat := 3496077195473003609662889

theorem tailTrace_6808586 : CollatzResearch.WordTrace tailWord_6808586 prefixEnd_6808586 3496077195473003609662889 := by
  unfold tailWord_6808586
  simp only [CollatzResearch.WordTrace]
  refine ⟨62082383127915802689391403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165553021674442140505043741 62082383127915802689391403)
  ·
    refine ⟨93123574691873704034087105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62082383127915802689391403 93123574691873704034087105)
    ·
      refine ⟨69842681018905278025565329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93123574691873704034087105 69842681018905278025565329)
      ·
        refine ⟨52382010764178958519173997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69842681018905278025565329 52382010764178958519173997)
        ·
          refine ⟨19643254036567109444690249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52382010764178958519173997 19643254036567109444690249)
          ·
            refine ⟨14732440527425332083517687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19643254036567109444690249 14732440527425332083517687)
            ·
              refine ⟨22098660791137998125276531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14732440527425332083517687 22098660791137998125276531)
              ·
                refine ⟨33147991186706997187914797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22098660791137998125276531 33147991186706997187914797)
                ·
                  refine ⟨12430496695015123945468049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33147991186706997187914797 12430496695015123945468049)
                  ·
                    refine ⟨9322872521261342959101037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12430496695015123945468049 9322872521261342959101037)
                    ·
                      refine ⟨3496077195473003609662889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9322872521261342959101037 3496077195473003609662889)
                      ·
                        rfl

theorem cell23_6808586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_6808586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808586 prefixEnd_6808586 := by exact prefixLift 6808586
  have htrace : WordTrace (prefixWord ++ tailWord_6808586) baseStart_6808586 baseEnd_6808586 := by
    simpa [prefixWord, tailWord_6808586, baseEnd_6808586] using wordTrace_append hprefix tailTrace_6808586
  have hstable : (prefixWord ++ tailWord_6808586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808586).length < 2 ^ (prefixWord ++ tailWord_6808586).sum := by decide
  have hdescent : baseEnd_6808586 < baseStart_6808586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808626 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2]
def baseStart_6808626 : Nat := 118140960795 + 6808626 * 2 ^ 59
def prefixEnd_6808626 : Nat := 4983230072969 + 3 ^ 40 * 6808626 * 2
def baseEnd_6808626 : Nat := 3496097734699183453162705

theorem tailTrace_6808626 : CollatzResearch.WordTrace tailWord_6808626 prefixEnd_6808626 3496097734699183453162705 := by
  unfold tailWord_6808626
  simp only [CollatzResearch.WordTrace]
  refine ⟨62082747857879574397255433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165553994287678865059347821 62082747857879574397255433)
  ·
    refine ⟨46562060893409680797941575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62082747857879574397255433 46562060893409680797941575)
    ·
      refine ⟨69843091340114521196912363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46562060893409680797941575 69843091340114521196912363)
      ·
        refine ⟨104764637010171781795368545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69843091340114521196912363 104764637010171781795368545)
        ·
          refine ⟨78573477757628836346526409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104764637010171781795368545 78573477757628836346526409)
          ·
            refine ⟨58930108318221627259894807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78573477757628836346526409 58930108318221627259894807)
            ·
              refine ⟨88395162477332440889842211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58930108318221627259894807 88395162477332440889842211)
              ·
                refine ⟨132592743715998661334763317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88395162477332440889842211 132592743715998661334763317)
                ·
                  refine ⟨12430569723374874500134061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132592743715998661334763317 12430569723374874500134061)
                  ·
                    refine ⟨4661463646265577937550273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12430569723374874500134061 4661463646265577937550273)
                    ·
                      refine ⟨3496097734699183453162705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4661463646265577937550273 3496097734699183453162705)
                      ·
                        rfl

theorem cell23_6808626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_6808626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808626 prefixEnd_6808626 := by exact prefixLift 6808626
  have htrace : WordTrace (prefixWord ++ tailWord_6808626) baseStart_6808626 baseEnd_6808626 := by
    simpa [prefixWord, tailWord_6808626, baseEnd_6808626] using wordTrace_append hprefix tailTrace_6808626
  have hstable : (prefixWord ++ tailWord_6808626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808626).length < 2 ^ (prefixWord ++ tailWord_6808626).sum := by decide
  have hdescent : baseEnd_6808626 < baseStart_6808626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808633 : List Nat := [1, 2, 1, 5, 2, 1, 2, 3, 2, 1, 3]
def baseStart_6808633 : Nat := 118140960795 + 6808633 * 2 ^ 59
def prefixEnd_6808633 : Nat := 4983230072969 + 3 ^ 40 * 6808633 * 2
def baseEnd_6808633 : Nat := 3496101329063764925775173

theorem tailTrace_6808633 : CollatzResearch.WordTrace tailWord_6808633 prefixEnd_6808633 3496101329063764925775173 := by
  unfold tailWord_6808633
  simp only [CollatzResearch.WordTrace]
  refine ⟨248331246742492937784526553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165554164494995291856351035 248331246742492937784526553)
  ·
    refine ⟨186248435056869703338394915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248331246742492937784526553 186248435056869703338394915)
    ·
      refine ⟨279372652585304555007592373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186248435056869703338394915 279372652585304555007592373)
      ·
        refine ⟨26191186179872302031961785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279372652585304555007592373 26191186179872302031961785)
        ·
          refine ⟨19643389634904226523971339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26191186179872302031961785 19643389634904226523971339)
          ·
            refine ⟨29465084452356339785957009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19643389634904226523971339 29465084452356339785957009)
            ·
              refine ⟨22098813339267254839467757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29465084452356339785957009 22098813339267254839467757)
              ·
                refine ⟨8287055002225220564800409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22098813339267254839467757 8287055002225220564800409)
                ·
                  refine ⟨6215291251668915423600307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8287055002225220564800409 6215291251668915423600307)
                  ·
                    refine ⟨9322936877503373135400461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6215291251668915423600307 9322936877503373135400461)
                    ·
                      refine ⟨3496101329063764925775173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9322936877503373135400461 3496101329063764925775173)
                      ·
                        rfl

theorem cell23_6808633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_6808633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808633 prefixEnd_6808633 := by exact prefixLift 6808633
  have htrace : WordTrace (prefixWord ++ tailWord_6808633) baseStart_6808633 baseEnd_6808633 := by
    simpa [prefixWord, tailWord_6808633, baseEnd_6808633] using wordTrace_append hprefix tailTrace_6808633
  have hstable : (prefixWord ++ tailWord_6808633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808633).length < 2 ^ (prefixWord ++ tailWord_6808633).sum := by decide
  have hdescent : baseEnd_6808633 < baseStart_6808633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808660 : List Nat := [2, 4, 1, 1, 1, 1, 6, 1, 1, 3, 2]
def baseStart_6808660 : Nat := 118140960795 + 6808660 * 2 ^ 59
def prefixEnd_6808660 : Nat := 4983230072969 + 3 ^ 40 * 6808660 * 2
def baseEnd_6808660 : Nat := 3496115193041436320137549

theorem tailTrace_6808660 : CollatzResearch.WordTrace tailWord_6808660 prefixEnd_6808660 3496115193041436320137549 := by
  unfold tailWord_6808660
  simp only [CollatzResearch.WordTrace]
  refine ⟨124166115756697560697879717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165554821008930080930506289 124166115756697560697879717)
  ·
    refine ⟨23281146704380792630852447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124166115756697560697879717 23281146704380792630852447)
    ·
      refine ⟨34921720056571188946278671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23281146704380792630852447 34921720056571188946278671)
      ·
        refine ⟨52382580084856783419418007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34921720056571188946278671 52382580084856783419418007)
        ·
          refine ⟨78573870127285175129127011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52382580084856783419418007 78573870127285175129127011)
          ·
            refine ⟨117860805190927762693690517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78573870127285175129127011 117860805190927762693690517)
            ·
              refine ⟨5524725243324738876266743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117860805190927762693690517 5524725243324738876266743)
              ·
                refine ⟨8287087864987108314400115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5524725243324738876266743 8287087864987108314400115)
                ·
                  refine ⟨12430631797480662471600173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8287087864987108314400115 12430631797480662471600173)
                  ·
                    refine ⟨4661486924055248426850065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12430631797480662471600173 4661486924055248426850065)
                    ·
                      refine ⟨3496115193041436320137549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4661486924055248426850065 3496115193041436320137549)
                      ·
                        rfl

theorem cell23_6808660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_6808660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808660 prefixEnd_6808660 := by exact prefixLift 6808660
  have htrace : WordTrace (prefixWord ++ tailWord_6808660) baseStart_6808660 baseEnd_6808660 := by
    simpa [prefixWord, tailWord_6808660, baseEnd_6808660] using wordTrace_append hprefix tailTrace_6808660
  have hstable : (prefixWord ++ tailWord_6808660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808660).length < 2 ^ (prefixWord ++ tailWord_6808660).sum := by decide
  have hdescent : baseEnd_6808660 < baseStart_6808660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808679 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 7]
def baseStart_6808679 : Nat := 118140960795 + 6808679 * 2 ^ 59
def prefixEnd_6808679 : Nat := 4983230072969 + 3 ^ 40 * 6808679 * 2
def baseEnd_6808679 : Nat := 388458327685985749533329

theorem tailTrace_6808679 : CollatzResearch.WordTrace tailWord_6808679 prefixEnd_6808679 388458327685985749533329 := by
  unfold tailWord_6808679
  simp only [CollatzResearch.WordTrace]
  refine ⟨248332924500326287640701091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165555283000217525093800727 248332924500326287640701091)
  ·
    refine ⟨372499386750489431461051637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248332924500326287640701091 372499386750489431461051637)
    ·
      refine ⟨34921817507858384199473591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 372499386750489431461051637 34921817507858384199473591)
      ·
        refine ⟨52382726261787576299210387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34921817507858384199473591 52382726261787576299210387)
        ·
          refine ⟨78574089392681364448815581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52382726261787576299210387 78574089392681364448815581)
          ·
            refine ⟨29465283522255511668305843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78574089392681364448815581 29465283522255511668305843)
            ·
              refine ⟨44197925283383267502458765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29465283522255511668305843 44197925283383267502458765)
              ·
                refine ⟨16574221981268725313422037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44197925283383267502458765 16574221981268725313422037)
                ·
                  refine ⟨388458327685985749533329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16574221981268725313422037 388458327685985749533329)
                  ·
                    rfl

theorem cell23_6808679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 7].length) (baseStart_6808679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808679 prefixEnd_6808679 := by exact prefixLift 6808679
  have htrace : WordTrace (prefixWord ++ tailWord_6808679) baseStart_6808679 baseEnd_6808679 := by
    simpa [prefixWord, tailWord_6808679, baseEnd_6808679] using wordTrace_append hprefix tailTrace_6808679
  have hstable : (prefixWord ++ tailWord_6808679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808679).length < 2 ^ (prefixWord ++ tailWord_6808679).sum := by decide
  have hdescent : baseEnd_6808679 < baseStart_6808679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808686 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_6808686 : Nat := 118140960795 + 6808686 * 2 ^ 59
def prefixEnd_6808686 : Nat := 4983230072969 + 3 ^ 40 * 6808686 * 2
def baseEnd_6808686 : Nat := 3496128543538453218412429

theorem tailTrace_6808686 : CollatzResearch.WordTrace tailWord_6808686 prefixEnd_6808686 3496128543538453218412429 := by
  unfold tailWord_6808686
  simp only [CollatzResearch.WordTrace]
  refine ⟨31041647476412615979525739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165555453207533951890803941 31041647476412615979525739)
  ·
    refine ⟨46562471214618923969288609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31041647476412615979525739 46562471214618923969288609)
    ·
      refine ⟨34921853410964192976966457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46562471214618923969288609 34921853410964192976966457)
      ·
        refine ⟨26191390058223144732724843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34921853410964192976966457 26191390058223144732724843)
        ·
          refine ⟨39287085087334717099087265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26191390058223144732724843 39287085087334717099087265)
          ·
            refine ⟨29465313815501037824315449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39287085087334717099087265 29465313815501037824315449)
            ·
              refine ⟨22098985361625778368236587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29465313815501037824315449 22098985361625778368236587)
              ·
                refine ⟨33148478042438667552354881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22098985361625778368236587 33148478042438667552354881)
                ·
                  refine ⟨24861358531829000664266161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33148478042438667552354881 24861358531829000664266161)
                  ·
                    refine ⟨18646018898871750498199621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24861358531829000664266161 18646018898871750498199621)
                    ·
                      refine ⟨3496128543538453218412429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18646018898871750498199621 3496128543538453218412429)
                      ·
                        rfl

theorem cell23_6808686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_6808686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808686 prefixEnd_6808686 := by exact prefixLift 6808686
  have htrace : WordTrace (prefixWord ++ tailWord_6808686) baseStart_6808686 baseEnd_6808686 := by
    simpa [prefixWord, tailWord_6808686, baseEnd_6808686] using wordTrace_append hprefix tailTrace_6808686
  have hstable : (prefixWord ++ tailWord_6808686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808686).length < 2 ^ (prefixWord ++ tailWord_6808686).sum := by decide
  have hdescent : baseEnd_6808686 < baseStart_6808686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808689 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 1, 5, 3]
def baseStart_6808689 : Nat := 118140960795 + 6808689 * 2 ^ 59
def prefixEnd_6808689 : Nat := 4983230072969 + 3 ^ 40 * 6808689 * 2
def baseEnd_6808689 : Nat := 3496130083980416706674915

theorem tailTrace_6808689 : CollatzResearch.WordTrace tailWord_6808689 prefixEnd_6808689 3496130083980416706674915 := by
  unfold tailWord_6808689
  simp only [CollatzResearch.WordTrace]
  refine ⟨248333289230290059348565121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165555526153526706232376747 248333289230290059348565121)
  ·
    refine ⟨186249966922717544511423841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248333289230290059348565121 186249966922717544511423841)
    ·
      refine ⟨139687475192038158383567881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186249966922717544511423841 139687475192038158383567881)
      ·
        refine ⟨104765606394028618787675911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139687475192038158383567881 104765606394028618787675911)
        ·
          refine ⟨157148409591042928181513867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104765606394028618787675911 157148409591042928181513867)
          ·
            refine ⟨235722614386564392272270801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157148409591042928181513867 235722614386564392272270801)
            ·
              refine ⟨176791960789923294204203101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235722614386564392272270801 176791960789923294204203101)
              ·
                refine ⟨66296985296221235326576163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176791960789923294204203101 66296985296221235326576163)
                ·
                  refine ⟨99445477944331852989864245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66296985296221235326576163 99445477944331852989864245)
                  ·
                    refine ⟨9323013557281111217799773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99445477944331852989864245 9323013557281111217799773)
                    ·
                      refine ⟨3496130083980416706674915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9323013557281111217799773 3496130083980416706674915)
                      ·
                        rfl

theorem cell23_6808689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_6808689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808689 prefixEnd_6808689 := by exact prefixLift 6808689
  have htrace : WordTrace (prefixWord ++ tailWord_6808689) baseStart_6808689 baseEnd_6808689 := by
    simpa [prefixWord, tailWord_6808689, baseEnd_6808689] using wordTrace_append hprefix tailTrace_6808689
  have hstable : (prefixWord ++ tailWord_6808689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808689).length < 2 ^ (prefixWord ++ tailWord_6808689).sum := by decide
  have hdescent : baseEnd_6808689 < baseStart_6808689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808713 : List Nat := [1, 2, 1, 1, 4, 5, 1, 3, 5]
def baseStart_6808713 : Nat := 118140960795 + 6808713 * 2 ^ 59
def prefixEnd_6808713 : Nat := 4983230072969 + 3 ^ 40 * 6808713 * 2
def baseEnd_6808713 : Nat := 388460267501791623641645

theorem tailTrace_6808713 : CollatzResearch.WordTrace tailWord_6808713 prefixEnd_6808713 388460267501791623641645 := by
  unfold tailWord_6808713
  simp only [CollatzResearch.WordTrace]
  refine ⟨248334164582203111447438793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165556109721468740964959195 248334164582203111447438793)
  ·
    refine ⟨186250623436652333585579095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248334164582203111447438793 186250623436652333585579095)
    ·
      refine ⟨279375935154978500378368643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186250623436652333585579095 279375935154978500378368643)
      ·
        refine ⟨419063902732467750567552965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279375935154978500378368643 419063902732467750567552965)
        ·
          refine ⟨78574481762337703231416181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 419063902732467750567552965 78574481762337703231416181)
          ·
            refine ⟨7366357665219159677945267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78574481762337703231416181 7366357665219159677945267)
            ·
              refine ⟨11049536497828739516917901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7366357665219159677945267 11049536497828739516917901)
              ·
                refine ⟨4143576186685777318844213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11049536497828739516917901 4143576186685777318844213)
                ·
                  refine ⟨388460267501791623641645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4143576186685777318844213 388460267501791623641645)
                  ·
                    rfl

theorem cell23_6808713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 5].length) (baseStart_6808713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808713 prefixEnd_6808713 := by exact prefixLift 6808713
  have htrace : WordTrace (prefixWord ++ tailWord_6808713) baseStart_6808713 baseEnd_6808713 := by
    simpa [prefixWord, tailWord_6808713, baseEnd_6808713] using wordTrace_append hprefix tailTrace_6808713
  have hstable : (prefixWord ++ tailWord_6808713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808713).length < 2 ^ (prefixWord ++ tailWord_6808713).sum := by decide
  have hdescent : baseEnd_6808713 < baseStart_6808713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808730 : List Nat := [3, 1, 1, 5, 1, 2, 3, 2, 5]
def baseStart_6808730 : Nat := 118140960795 + 6808730 * 2 ^ 59
def prefixEnd_6808730 : Nat := 4983230072969 + 3 ^ 40 * 6808730 * 2
def baseEnd_6808730 : Nat := 388461237409694560695803

theorem tailTrace_6808730 : CollatzResearch.WordTrace tailWord_6808730 prefixEnd_6808730 388461237409694560695803 := by
  unfold tailWord_6808730
  simp only [CollatzResearch.WordTrace]
  refine ⟨62083696155785380837701911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165556523082094348900538429 62083696155785380837701911)
  ·
    refine ⟨93125544233678071256552867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62083696155785380837701911 93125544233678071256552867)
    ·
      refine ⟨139688316350517106884829301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93125544233678071256552867 139688316350517106884829301)
      ·
        refine ⟨13095779657860978770452747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139688316350517106884829301 13095779657860978770452747)
        ·
          refine ⟨19643669486791468155679121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13095779657860978770452747 19643669486791468155679121)
          ·
            refine ⟨14732752115093601116759341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19643669486791468155679121 14732752115093601116759341)
            ·
              refine ⟨5524782043160100418784753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14732752115093601116759341 5524782043160100418784753)
              ·
                refine ⟨4143586532370075314088565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5524782043160100418784753 4143586532370075314088565)
                ·
                  refine ⟨388461237409694560695803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4143586532370075314088565 388461237409694560695803)
                  ·
                    rfl

theorem cell23_6808730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 5].length) (baseStart_6808730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808730 prefixEnd_6808730 := by exact prefixLift 6808730
  have htrace : WordTrace (prefixWord ++ tailWord_6808730) baseStart_6808730 baseEnd_6808730 := by
    simpa [prefixWord, tailWord_6808730, baseEnd_6808730] using wordTrace_append hprefix tailTrace_6808730
  have hstable : (prefixWord ++ tailWord_6808730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808730).length < 2 ^ (prefixWord ++ tailWord_6808730).sum := by decide
  have hdescent : baseEnd_6808730 < baseStart_6808730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808773 : List Nat := [1, 3, 1, 1, 1, 1, 3, 7, 1, 4]
def baseStart_6808773 : Nat := 118140960795 + 6808773 * 2 ^ 59
def prefixEnd_6808773 : Nat := 4983230072969 + 3 ^ 40 * 6808773 * 2
def baseEnd_6808773 : Nat := 1165391072118464792674843

theorem tailTrace_6808773 : CollatzResearch.WordTrace tailWord_6808773 prefixEnd_6808773 1165391072118464792674843 := by
  unfold tailWord_6808773
  simp only [CollatzResearch.WordTrace]
  refine ⟨248336352961985741694622973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165557568641323827796415315 248336352961985741694622973)
  ·
    refine ⟨93126132360744653135483615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248336352961985741694622973 93126132360744653135483615)
    ·
      refine ⟨139689198541116979703225423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93126132360744653135483615 139689198541116979703225423)
      ·
        refine ⟨209533797811675469554838135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139689198541116979703225423 209533797811675469554838135)
        ·
          refine ⟨314300696717513204332257203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209533797811675469554838135 314300696717513204332257203)
          ·
            refine ⟨471451045076269806498385805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314300696717513204332257203 471451045076269806498385805)
            ·
              refine ⟨176794141903601177436894677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 471451045076269806498385805 176794141903601177436894677)
              ·
                refine ⟨4143612700865652596177219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 176794141903601177436894677 4143612700865652596177219)
                ·
                  refine ⟨6215419051298478894265829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4143612700865652596177219 6215419051298478894265829)
                  ·
                    refine ⟨1165391072118464792674843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6215419051298478894265829 1165391072118464792674843)
                    ·
                      rfl

theorem cell23_6808773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 1, 4].length) (baseStart_6808773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808773 prefixEnd_6808773 := by exact prefixLift 6808773
  have htrace : WordTrace (prefixWord ++ tailWord_6808773) baseStart_6808773 baseEnd_6808773 := by
    simpa [prefixWord, tailWord_6808773, baseEnd_6808773] using wordTrace_append hprefix tailTrace_6808773
  have hstable : (prefixWord ++ tailWord_6808773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808773).length < 2 ^ (prefixWord ++ tailWord_6808773).sum := by decide
  have hdescent : baseEnd_6808773 < baseStart_6808773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808781 : List Nat := [1, 6, 2, 2, 2, 1, 2, 2, 5]
def baseStart_6808781 : Nat := 118140960795 + 6808781 * 2 ^ 59
def prefixEnd_6808781 : Nat := 4983230072969 + 3 ^ 40 * 6808781 * 2
def baseEnd_6808781 : Nat := 388464147133403371858277

theorem tailTrace_6808781 : CollatzResearch.WordTrace tailWord_6808781 prefixEnd_6808781 388464147133403371858277 := by
  unfold tailWord_6808781
  simp only [CollatzResearch.WordTrace]
  refine ⟨248336644745956759060914197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165557763163971172707276131 248336644745956759060914197)
  ·
    refine ⟨11640780222466723080980353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 248336644745956759060914197 11640780222466723080980353)
    ·
      refine ⟨8730585166850042310735265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11640780222466723080980353 8730585166850042310735265)
      ·
        refine ⟨6547938875137531733051449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8730585166850042310735265 6547938875137531733051449)
        ·
          refine ⟨4910954156353148799788587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6547938875137531733051449 4910954156353148799788587)
          ·
            refine ⟨7366431234529723199682881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4910954156353148799788587 7366431234529723199682881)
            ·
              refine ⟨5524823425897292399762161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7366431234529723199682881 5524823425897292399762161)
              ·
                refine ⟨4143617569422969299821621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5524823425897292399762161 4143617569422969299821621)
                ·
                  refine ⟨388464147133403371858277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4143617569422969299821621 388464147133403371858277)
                  ·
                    rfl

theorem cell23_6808781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_6808781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808781 prefixEnd_6808781 := by exact prefixLift 6808781
  have htrace : WordTrace (prefixWord ++ tailWord_6808781) baseStart_6808781 baseEnd_6808781 := by
    simpa [prefixWord, tailWord_6808781, baseEnd_6808781] using wordTrace_append hprefix tailTrace_6808781
  have hstable : (prefixWord ++ tailWord_6808781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808781).length < 2 ^ (prefixWord ++ tailWord_6808781).sum := by decide
  have hdescent : baseEnd_6808781 < baseStart_6808781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808833 : List Nat := [1, 2, 4, 1, 1, 4, 1, 3, 1, 5]
def baseStart_6808833 : Nat := 118140960795 + 6808833 * 2 ^ 59
def prefixEnd_6808833 : Nat := 4983230072969 + 3 ^ 40 * 6808833 * 2
def baseEnd_6808833 : Nat := 1165401341731554714424751

theorem tailTrace_6808833 : CollatzResearch.WordTrace tailWord_6808833 prefixEnd_6808833 1165401341731554714424751 := by
  unfold tailWord_6808833
  simp only [CollatzResearch.WordTrace]
  refine ⟨248338541341768371941807153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165559027561178914627871435 248338541341768371941807153)
  ·
    refine ⟨186253906006326278956355365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248338541341768371941807153 186253906006326278956355365)
    ·
      refine ⟨34922607376186177304316631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186253906006326278956355365 34922607376186177304316631)
      ·
        refine ⟨52383911064279265956474947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34922607376186177304316631 52383911064279265956474947)
        ·
          refine ⟨78575866596418898934712421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52383911064279265956474947 78575866596418898934712421)
          ·
            refine ⟨14732974986828543550258579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78575866596418898934712421 14732974986828543550258579)
            ·
              refine ⟨22099462480242815325387869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14732974986828543550258579 22099462480242815325387869)
              ·
                refine ⟨8287298430091055747020451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22099462480242815325387869 8287298430091055747020451)
                ·
                  refine ⟨12430947645136583620530677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8287298430091055747020451 12430947645136583620530677)
                  ·
                    refine ⟨1165401341731554714424751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12430947645136583620530677 1165401341731554714424751)
                    ·
                      rfl

theorem cell23_6808833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_6808833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808833 prefixEnd_6808833 := by exact prefixLift 6808833
  have htrace : WordTrace (prefixWord ++ tailWord_6808833) baseStart_6808833 baseEnd_6808833 := by
    simpa [prefixWord, tailWord_6808833, baseEnd_6808833] using wordTrace_append hprefix tailTrace_6808833
  have hstable : (prefixWord ++ tailWord_6808833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808833).length < 2 ^ (prefixWord ++ tailWord_6808833).sum := by decide
  have hdescent : baseEnd_6808833 < baseStart_6808833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808856 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 3, 1, 5]
def baseStart_6808856 : Nat := 118140960795 + 6808856 * 2 ^ 59
def prefixEnd_6808856 : Nat := 4983230072969 + 3 ^ 40 * 6808856 * 2
def baseEnd_6808856 : Nat := 3496215835249717553286647

theorem tailTrace_6808856 : CollatzResearch.WordTrace tailWord_6808856 prefixEnd_6808856 3496215835249717553286647 := by
  unfold tailWord_6808856
  simp only [CollatzResearch.WordTrace]
  refine ⟨124169690110342523434947211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165559586813790031246596281 124169690110342523434947211)
  ·
    refine ⟨186254535165513785152420817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124169690110342523434947211 186254535165513785152420817)
    ·
      refine ⟨139690901374135338864315613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186254535165513785152420817 139690901374135338864315613)
      ·
        refine ⟨52384088015300752074118355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139690901374135338864315613 52384088015300752074118355)
        ·
          refine ⟨78576132022951128111177533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52384088015300752074118355 78576132022951128111177533)
          ·
            refine ⟨29466049508606673041691575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78576132022951128111177533 29466049508606673041691575)
            ·
              refine ⟨44199074262910009562537363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29466049508606673041691575 44199074262910009562537363)
              ·
                refine ⟨66298611394365014343806045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44199074262910009562537363 66298611394365014343806045)
                ·
                  refine ⟨24861979272886880378927267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66298611394365014343806045 24861979272886880378927267)
                  ·
                    refine ⟨37292968909330320568390901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24861979272886880378927267 37292968909330320568390901)
                    ·
                      refine ⟨3496215835249717553286647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37292968909330320568390901 3496215835249717553286647)
                      ·
                        rfl

theorem cell23_6808856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_6808856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808856 prefixEnd_6808856 := by exact prefixLift 6808856
  have htrace : WordTrace (prefixWord ++ tailWord_6808856) baseStart_6808856 baseEnd_6808856 := by
    simpa [prefixWord, tailWord_6808856, baseEnd_6808856] using wordTrace_append hprefix tailTrace_6808856
  have hstable : (prefixWord ++ tailWord_6808856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808856).length < 2 ^ (prefixWord ++ tailWord_6808856).sum := by decide
  have hdescent : baseEnd_6808856 < baseStart_6808856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808859 : List Nat := [1, 1, 1, 1, 1, 1, 5, 12]
def baseStart_6808859 : Nat := 118140960795 + 6808859 * 2 ^ 59
def prefixEnd_6808859 : Nat := 4983230072969 + 3 ^ 40 * 6808859 * 2
def baseEnd_6808859 : Nat := 129489532433025223761079

theorem tailTrace_6808859 : CollatzResearch.WordTrace tailWord_6808859 prefixEnd_6808859 129489532433025223761079 := by
  unfold tailWord_6808859
  simp only [CollatzResearch.WordTrace]
  refine ⟨248339489639674178382253631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165559659759782785588169087 248339489639674178382253631)
  ·
    refine ⟨372509234459511267573380447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248339489639674178382253631 372509234459511267573380447)
    ·
      refine ⟨558763851689266901360070671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372509234459511267573380447 558763851689266901360070671)
      ·
        refine ⟨838145777533900352040106007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558763851689266901360070671 838145777533900352040106007)
        ·
          refine ⟨1257218666300850528060159011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838145777533900352040106007 1257218666300850528060159011)
          ·
            refine ⟨1885827999451275792090238517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257218666300850528060159011 1885827999451275792090238517)
            ·
              refine ⟨176796374948557105508459861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1885827999451275792090238517 176796374948557105508459861)
              ·
                refine ⟨129489532433025223761079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 176796374948557105508459861 129489532433025223761079)
                ·
                  rfl

theorem cell23_6808859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 12].length) (baseStart_6808859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808859 prefixEnd_6808859 := by exact prefixLift 6808859
  have htrace : WordTrace (prefixWord ++ tailWord_6808859) baseStart_6808859 baseEnd_6808859 := by
    simpa [prefixWord, tailWord_6808859, baseEnd_6808859] using wordTrace_append hprefix tailTrace_6808859
  have hstable : (prefixWord ++ tailWord_6808859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808859).length < 2 ^ (prefixWord ++ tailWord_6808859).sum := by decide
  have hdescent : baseEnd_6808859 < baseStart_6808859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808918 : List Nat := [5, 2, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_6808918 : Nat := 118140960795 + 6808918 * 2 ^ 59
def prefixEnd_6808918 : Nat := 4983230072969 + 3 ^ 40 * 6808918 * 2
def baseEnd_6808918 : Nat := 1165415890350098770237121

theorem tailTrace_6808918 : CollatzResearch.WordTrace tailWord_6808918 prefixEnd_6808918 1165415890350098770237121 := by
  unfold tailWord_6808918
  simp only [CollatzResearch.WordTrace]
  refine ⟨15521352596653776966165713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165561094364306954305767605 15521352596653776966165713)
  ·
    refine ⟨11641014447490332724624285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15521352596653776966165713 11641014447490332724624285)
    ·
      refine ⟨4365380417808874771734107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11641014447490332724624285 4365380417808874771734107)
      ·
        refine ⟨6548070626713312157601161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4365380417808874771734107 6548070626713312157601161)
        ·
          refine ⟨4911052970034984118200871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6548070626713312157601161 4911052970034984118200871)
          ·
            refine ⟨7366579455052476177301307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4911052970034984118200871 7366579455052476177301307)
            ·
              refine ⟨11049869182578714265951961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7366579455052476177301307 11049869182578714265951961)
              ·
                refine ⟨8287401886934035699463971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11049869182578714265951961 8287401886934035699463971)
                ·
                  refine ⟨12431102830401053549195957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8287401886934035699463971 12431102830401053549195957)
                  ·
                    refine ⟨1165415890350098770237121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12431102830401053549195957 1165415890350098770237121)
                    ·
                      rfl

theorem cell23_6808918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_6808918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808918 prefixEnd_6808918 := by exact prefixLift 6808918
  have htrace : WordTrace (prefixWord ++ tailWord_6808918) baseStart_6808918 baseEnd_6808918 := by
    simpa [prefixWord, tailWord_6808918, baseEnd_6808918] using wordTrace_append hprefix tailTrace_6808918
  have hstable : (prefixWord ++ tailWord_6808918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808918).length < 2 ^ (prefixWord ++ tailWord_6808918).sum := by decide
  have hdescent : baseEnd_6808918 < baseStart_6808918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808920 : List Nat := [2, 1, 2, 2, 1, 1, 5, 3, 2, 1, 3]
def baseStart_6808920 : Nat := 118140960795 + 6808920 * 2 ^ 59
def prefixEnd_6808920 : Nat := 4983230072969 + 3 ^ 40 * 6808920 * 2
def baseEnd_6808920 : Nat := 3496248698011605302886353

theorem tailTrace_6808920 : CollatzResearch.WordTrace tailWord_6808920 prefixEnd_6808920 3496248698011605302886353 := by
  unfold tailWord_6808920
  simp only [CollatzResearch.WordTrace]
  refine ⟨124170857246226592900112107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165561142994968790533482809 124170857246226592900112107)
  ·
    refine ⟨186256285869339889350168161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124170857246226592900112107 186256285869339889350168161)
    ·
      refine ⟨139692214402004917012626121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186256285869339889350168161 139692214402004917012626121)
      ·
        refine ⟨104769160801503687759469591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139692214402004917012626121 104769160801503687759469591)
        ·
          refine ⟨157153741202255531639204387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104769160801503687759469591 157153741202255531639204387)
          ·
            refine ⟨235730611803383297458806581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157153741202255531639204387 235730611803383297458806581)
            ·
              refine ⟨22099744856567184136763117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235730611803383297458806581 22099744856567184136763117)
              ·
                refine ⟨8287404321212694051286169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22099744856567184136763117 8287404321212694051286169)
                ·
                  refine ⟨6215553240909520538464627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8287404321212694051286169 6215553240909520538464627)
                  ·
                    refine ⟨9323329861364280807696941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6215553240909520538464627 9323329861364280807696941)
                    ·
                      refine ⟨3496248698011605302886353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9323329861364280807696941 3496248698011605302886353)
                      ·
                        rfl

theorem cell23_6808920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_6808920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808920 prefixEnd_6808920 := by exact prefixLift 6808920
  have htrace : WordTrace (prefixWord ++ tailWord_6808920) baseStart_6808920 baseEnd_6808920 := by
    simpa [prefixWord, tailWord_6808920, baseEnd_6808920] using wordTrace_append hprefix tailTrace_6808920
  have hstable : (prefixWord ++ tailWord_6808920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808920).length < 2 ^ (prefixWord ++ tailWord_6808920).sum := by decide
  have hdescent : baseEnd_6808920 < baseStart_6808920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808960 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 4, 2, 2]
def baseStart_6808960 : Nat := 118140960795 + 6808960 * 2 ^ 59
def prefixEnd_6808960 : Nat := 4983230072969 + 3 ^ 40 * 6808960 * 2
def baseEnd_6808960 : Nat := 3496269237237785146386169

theorem tailTrace_6808960 : CollatzResearch.WordTrace tailWord_6808960 prefixEnd_6808960 3496269237237785146386169 := by
  unfold tailWord_6808960
  simp only [CollatzResearch.WordTrace]
  refine ⟨124171586706154136315840167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165562115608205515087786889 124171586706154136315840167)
  ·
    refine ⟨186257380059231204473760251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124171586706154136315840167 186257380059231204473760251)
    ·
      refine ⟨279386070088846806710640377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186257380059231204473760251 279386070088846806710640377)
      ·
        refine ⟨209539552566635105032980283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279386070088846806710640377 209539552566635105032980283)
        ·
          refine ⟨314309328849952657549470425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209539552566635105032980283 314309328849952657549470425)
          ·
            refine ⟨235731996637464493162102819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314309328849952657549470425 235731996637464493162102819)
            ·
              refine ⟨353597994956196739743154229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235731996637464493162102819 353597994956196739743154229)
              ·
                refine ⟨33149812027143444350920709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 353597994956196739743154229 33149812027143444350920709)
                ·
                  refine ⟨6215589755089395815797633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33149812027143444350920709 6215589755089395815797633)
                  ·
                    refine ⟨4661692316317046861848225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6215589755089395815797633 4661692316317046861848225)
                    ·
                      refine ⟨3496269237237785146386169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4661692316317046861848225 3496269237237785146386169)
                      ·
                        rfl

theorem cell23_6808960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 4, 2, 2].length) (baseStart_6808960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808960 prefixEnd_6808960 := by exact prefixLift 6808960
  have htrace : WordTrace (prefixWord ++ tailWord_6808960) baseStart_6808960 baseEnd_6808960 := by
    simpa [prefixWord, tailWord_6808960, baseEnd_6808960] using wordTrace_append hprefix tailTrace_6808960
  have hstable : (prefixWord ++ tailWord_6808960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808960).length < 2 ^ (prefixWord ++ tailWord_6808960).sum := by decide
  have hdescent : baseEnd_6808960 < baseStart_6808960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6808963 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 3]
def baseStart_6808963 : Nat := 118140960795 + 6808963 * 2 ^ 59
def prefixEnd_6808963 : Nat := 4983230072969 + 3 ^ 40 * 6808963 * 2
def baseEnd_6808963 : Nat := 3496270777679748634648655

theorem tailTrace_6808963 : CollatzResearch.WordTrace tailWord_6808963 prefixEnd_6808963 3496270777679748634648655 := by
  unfold tailWord_6808963
  simp only [CollatzResearch.WordTrace]
  refine ⟨248343282831297404144039543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165562188554198269429359695 248343282831297404144039543)
  ·
    refine ⟨372514924246946106216059315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248343282831297404144039543 372514924246946106216059315)
    ·
      refine ⟨558772386370419159324088973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372514924246946106216059315 558772386370419159324088973)
      ·
        refine ⟨209539644888907184746533365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 558772386370419159324088973 209539644888907184746533365)
        ·
          refine ⟨19644341708335048569987503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 209539644888907184746533365 19644341708335048569987503)
          ·
            refine ⟨29466512562502572854981255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19644341708335048569987503 29466512562502572854981255)
            ·
              refine ⟨44199768843753859282471883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29466512562502572854981255 44199768843753859282471883)
              ·
                refine ⟨66299653265630788923707825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44199768843753859282471883 66299653265630788923707825)
                ·
                  refine ⟨49724739949223091692780869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66299653265630788923707825 49724739949223091692780869)
                  ·
                    refine ⟨9323388740479329692396413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49724739949223091692780869 9323388740479329692396413)
                    ·
                      refine ⟨3496270777679748634648655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9323388740479329692396413 3496270777679748634648655)
                      ·
                        rfl

theorem cell23_6808963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_6808963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6808963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6808963 prefixEnd_6808963 := by exact prefixLift 6808963
  have htrace : WordTrace (prefixWord ++ tailWord_6808963) baseStart_6808963 baseEnd_6808963 := by
    simpa [prefixWord, tailWord_6808963, baseEnd_6808963] using wordTrace_append hprefix tailTrace_6808963
  have hstable : (prefixWord ++ tailWord_6808963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6808963).length < 2 ^ (prefixWord ++ tailWord_6808963).sum := by decide
  have hdescent : baseEnd_6808963 < baseStart_6808963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6808963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809073 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 8]
def baseStart_6809073 : Nat := 118140960795 + 6809073 * 2 ^ 59
def prefixEnd_6809073 : Nat := 4983230072969 + 3 ^ 40 * 6809073 * 2
def baseEnd_6809073 : Nat := 388480806727971467141461

theorem tailTrace_6809073 : CollatzResearch.WordTrace tailWord_6809073 prefixEnd_6809073 388480806727971467141461 := by
  unfold tailWord_6809073
  simp only [CollatzResearch.WordTrace]
  refine ⟨248347294860898892930543873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165564863240599261953695915 248347294860898892930543873)
  ·
    refine ⟨186260471145674169697907905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248347294860898892930543873 186260471145674169697907905)
    ·
      refine ⟨139695353359255627273430929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186260471145674169697907905 139695353359255627273430929)
      ·
        refine ⟨104771515019441720455073197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139695353359255627273430929 104771515019441720455073197)
        ·
          refine ⟨39289318132290645170652449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104771515019441720455073197 39289318132290645170652449)
          ·
            refine ⟨29466988599217983877989337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39289318132290645170652449 29466988599217983877989337)
            ·
              refine ⟨22100241449413487908492003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29466988599217983877989337 22100241449413487908492003)
              ·
                refine ⟨33150362174120231862738005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22100241449413487908492003 33150362174120231862738005)
                ·
                  refine ⟨388480806727971467141461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33150362174120231862738005 388480806727971467141461)
                  ·
                    rfl

theorem cell23_6809073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 8].length) (baseStart_6809073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809073 prefixEnd_6809073 := by exact prefixLift 6809073
  have htrace : WordTrace (prefixWord ++ tailWord_6809073) baseStart_6809073 baseEnd_6809073 := by
    simpa [prefixWord, tailWord_6809073, baseEnd_6809073] using wordTrace_append hprefix tailTrace_6809073
  have hstable : (prefixWord ++ tailWord_6809073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809073).length < 2 ^ (prefixWord ++ tailWord_6809073).sum := by decide
  have hdescent : baseEnd_6809073 < baseStart_6809073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809101 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_6809101 : Nat := 118140960795 + 6809101 * 2 ^ 59
def prefixEnd_6809101 : Nat := 4983230072969 + 3 ^ 40 * 6809101 * 2
def baseEnd_6809101 : Nat := 3496341638010069094723021

theorem tailTrace_6809101 : CollatzResearch.WordTrace tailWord_6809101 prefixEnd_6809101 3496341638010069094723021 := by
  unfold tailWord_6809101
  simp only [CollatzResearch.WordTrace]
  refine ⟨248348316104797453712563157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165565544069864969141708771 248348316104797453712563157)
  ·
    refine ⟨5820663658706190321388199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 248348316104797453712563157 5820663658706190321388199)
    ·
      refine ⟨8730995488059285482082299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5820663658706190321388199 8730995488059285482082299)
      ·
        refine ⟨13096493232088928223123449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8730995488059285482082299 13096493232088928223123449)
        ·
          refine ⟨9822369924066696167342587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13096493232088928223123449 9822369924066696167342587)
          ·
            refine ⟨14733554886100044251013881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9822369924066696167342587 14733554886100044251013881)
            ·
              refine ⟨11050166164575033188260411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14733554886100044251013881 11050166164575033188260411)
              ·
                refine ⟨16575249246862549782390617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11050166164575033188260411 16575249246862549782390617)
                ·
                  refine ⟨12431436935146912336792963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16575249246862549782390617 12431436935146912336792963)
                  ·
                    refine ⟨18647155402720368505189445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12431436935146912336792963 18647155402720368505189445)
                    ·
                      refine ⟨3496341638010069094723021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18647155402720368505189445 3496341638010069094723021)
                      ·
                        rfl

theorem cell23_6809101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_6809101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809101 prefixEnd_6809101 := by exact prefixLift 6809101
  have htrace : WordTrace (prefixWord ++ tailWord_6809101) baseStart_6809101 baseEnd_6809101 := by
    simpa [prefixWord, tailWord_6809101, baseEnd_6809101] using wordTrace_append hprefix tailTrace_6809101
  have hstable : (prefixWord ++ tailWord_6809101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809101).length < 2 ^ (prefixWord ++ tailWord_6809101).sum := by decide
  have hdescent : baseEnd_6809101 < baseStart_6809101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809128 : List Nat := [2, 1, 5, 2, 2, 2, 2, 2, 1, 4]
def baseStart_6809128 : Nat := 118140960795 + 6809128 * 2 ^ 59
def prefixEnd_6809128 : Nat := 4983230072969 + 3 ^ 40 * 6809128 * 2
def baseEnd_6809128 : Nat := 1165451833995913496361799

theorem tailTrace_6809128 : CollatzResearch.WordTrace tailWord_6809128 prefixEnd_6809128 1165451833995913496361799 := by
  unfold tailWord_6809128
  simp only [CollatzResearch.WordTrace]
  refine ⟨124174650437849818661898019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165566200583799758215864025 124174650437849818661898019)
  ·
    refine ⟨186261975656774727992847029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124174650437849818661898019 186261975656774727992847029)
    ·
      refine ⟨17462060217822630749329409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186261975656774727992847029 17462060217822630749329409)
      ·
        refine ⟨13096545163366973061997057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17462060217822630749329409 13096545163366973061997057)
        ·
          refine ⟨9822408872525229796497793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13096545163366973061997057 9822408872525229796497793)
          ·
            refine ⟨7366806654393922347373345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9822408872525229796497793 7366806654393922347373345)
            ·
              refine ⟨5525104990795441760530009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7366806654393922347373345 5525104990795441760530009)
              ·
                refine ⟨4143828743096581320397507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5525104990795441760530009 4143828743096581320397507)
                ·
                  refine ⟨6215743114644871980596261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4143828743096581320397507 6215743114644871980596261)
                  ·
                    refine ⟨1165451833995913496361799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6215743114644871980596261 1165451833995913496361799)
                    ·
                      rfl

theorem cell23_6809128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_6809128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809128 prefixEnd_6809128 := by exact prefixLift 6809128
  have htrace : WordTrace (prefixWord ++ tailWord_6809128) baseStart_6809128 baseEnd_6809128 := by
    simpa [prefixWord, tailWord_6809128, baseEnd_6809128] using wordTrace_append hprefix tailTrace_6809128
  have hstable : (prefixWord ++ tailWord_6809128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809128).length < 2 ^ (prefixWord ++ tailWord_6809128).sum := by decide
  have hdescent : baseEnd_6809128 < baseStart_6809128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809180 : List Nat := [2, 2, 4, 1, 2, 2, 10]
def baseStart_6809180 : Nat := 118140960795 + 6809180 * 2 ^ 59
def prefixEnd_6809180 : Nat := 4983230072969 + 3 ^ 40 * 6809180 * 2
def baseEnd_6809180 : Nat := 43165212382491040563397

theorem tailTrace_6809180 : CollatzResearch.WordTrace tailWord_6809180 prefixEnd_6809180 43165212382491040563397 := by
  unfold tailWord_6809180
  simp only [CollatzResearch.WordTrace]
  refine ⟨124175598735755625102344497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165567464981007500136459329 124175598735755625102344497)
  ·
    refine ⟨93131699051816718826758373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124175598735755625102344497 93131699051816718826758373)
    ·
      refine ⟨17462193572215634780017195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93131699051816718826758373 17462193572215634780017195)
      ·
        refine ⟨26193290358323452170025793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17462193572215634780017195 26193290358323452170025793)
        ·
          refine ⟨19644967768742589127519345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26193290358323452170025793 19644967768742589127519345)
          ·
            refine ⟨14733725826556941845639509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19644967768742589127519345 14733725826556941845639509)
            ·
              refine ⟨43165212382491040563397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14733725826556941845639509 43165212382491040563397)
              ·
                rfl

theorem cell23_6809180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 10].length) (baseStart_6809180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809180 prefixEnd_6809180 := by exact prefixLift 6809180
  have htrace : WordTrace (prefixWord ++ tailWord_6809180) baseStart_6809180 baseEnd_6809180 := by
    simpa [prefixWord, tailWord_6809180, baseEnd_6809180] using wordTrace_append hprefix tailTrace_6809180
  have hstable : (prefixWord ++ tailWord_6809180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809180).length < 2 ^ (prefixWord ++ tailWord_6809180).sum := by decide
  have hdescent : baseEnd_6809180 < baseStart_6809180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809183 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 6]
def baseStart_6809183 : Nat := 118140960795 + 6809183 * 2 ^ 59
def prefixEnd_6809183 : Nat := 4983230072969 + 3 ^ 40 * 6809183 * 2
def baseEnd_6809183 : Nat := 3496383743423737773897643

theorem tailTrace_6809183 : CollatzResearch.WordTrace tailWord_6809183 prefixEnd_6809183 3496383743423737773897643 := by
  unfold tailWord_6809183
  simp only [CollatzResearch.WordTrace]
  refine ⟨248351306890500381717048203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165567537927000254478032135 248351306890500381717048203)
  ·
    refine ⟨372526960335750572575572305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248351306890500381717048203 372526960335750572575572305)
    ·
      refine ⟨279395220251812929431679229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372526960335750572575572305 279395220251812929431679229)
      ·
        refine ⟨104773207594429848536879711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279395220251812929431679229 104773207594429848536879711)
        ·
          refine ⟨157159811391644772805319567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104773207594429848536879711 157159811391644772805319567)
          ·
            refine ⟨235739717087467159207979351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157159811391644772805319567 235739717087467159207979351)
            ·
              refine ⟨353609575631200738811969027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235739717087467159207979351 353609575631200738811969027)
              ·
                refine ⟨530414363446801108217953541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353609575631200738811969027 530414363446801108217953541)
                ·
                  refine ⟨99452693146275207790866289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 530414363446801108217953541 99452693146275207790866289)
                  ·
                    refine ⟨74589519859706405843149717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99452693146275207790866289 74589519859706405843149717)
                    ·
                      refine ⟨3496383743423737773897643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74589519859706405843149717 3496383743423737773897643)
                      ·
                        rfl

theorem cell23_6809183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_6809183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809183 prefixEnd_6809183 := by exact prefixLift 6809183
  have htrace : WordTrace (prefixWord ++ tailWord_6809183) baseStart_6809183 baseEnd_6809183 := by
    simpa [prefixWord, tailWord_6809183, baseEnd_6809183] using wordTrace_append hprefix tailTrace_6809183
  have hstable : (prefixWord ++ tailWord_6809183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809183).length < 2 ^ (prefixWord ++ tailWord_6809183).sum := by decide
  have hdescent : baseEnd_6809183 < baseStart_6809183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809191 : List Nat := [1, 1, 5, 1, 1, 1, 4, 4, 1, 2, 2]
def baseStart_6809191 : Nat := 118140960795 + 6809191 * 2 ^ 59
def prefixEnd_6809191 : Nat := 4983230072969 + 3 ^ 40 * 6809191 * 2
def baseEnd_6809191 : Nat := 3496387851268973742597607

theorem tailTrace_6809191 : CollatzResearch.WordTrace tailWord_6809191 prefixEnd_6809191 3496387851268973742597607 := by
  unfold tailWord_6809191
  simp only [CollatzResearch.WordTrace]
  refine ⟨248351598674471399083339427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165567732449647599388892951 248351598674471399083339427)
  ·
    refine ⟨372527398011707098625009141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248351598674471399083339427 372527398011707098625009141)
    ·
      refine ⟨34924443563597540496094607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 372527398011707098625009141 34924443563597540496094607)
      ·
        refine ⟨52386665345396310744141911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34924443563597540496094607 52386665345396310744141911)
        ·
          refine ⟨78579998018094466116212867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52386665345396310744141911 78579998018094466116212867)
          ·
            refine ⟨117869997027141699174319301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78579998018094466116212867 117869997027141699174319301)
            ·
              refine ⟨22100624442589068595184869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117869997027141699174319301 22100624442589068595184869)
              ·
                refine ⟨4143867082985450361597163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22100624442589068595184869 4143867082985450361597163)
                ·
                  refine ⟨6215800624478175542395745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4143867082985450361597163 6215800624478175542395745)
                  ·
                    refine ⟨4661850468358631656796809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6215800624478175542395745 4661850468358631656796809)
                    ·
                      refine ⟨3496387851268973742597607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4661850468358631656796809 3496387851268973742597607)
                      ·
                        rfl

theorem cell23_6809191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_6809191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809191 prefixEnd_6809191 := by exact prefixLift 6809191
  have htrace : WordTrace (prefixWord ++ tailWord_6809191) baseStart_6809191 baseEnd_6809191 := by
    simpa [prefixWord, tailWord_6809191, baseEnd_6809191] using wordTrace_append hprefix tailTrace_6809191
  have hstable : (prefixWord ++ tailWord_6809191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809191).length < 2 ^ (prefixWord ++ tailWord_6809191).sum := by decide
  have hdescent : baseEnd_6809191 < baseStart_6809191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809193 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 1, 9]
def baseStart_6809193 : Nat := 118140960795 + 6809193 * 2 ^ 59
def prefixEnd_6809193 : Nat := 4983230072969 + 3 ^ 40 * 6809193 * 2
def baseEnd_6809193 : Nat := 1165462959410094244924199

theorem tailTrace_6809193 : CollatzResearch.WordTrace tailWord_6809193 prefixEnd_6809193 1165462959410094244924199 := by
  unfold tailWord_6809193
  simp only [CollatzResearch.WordTrace]
  refine ⟨248351671620464153424912233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165567781080309435616608155 248351671620464153424912233)
  ·
    refine ⟨186263753715348115068684175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248351671620464153424912233 186263753715348115068684175)
    ·
      refine ⟨279395630573022172603026263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186263753715348115068684175 279395630573022172603026263)
      ·
        refine ⟨419093445859533258904539395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279395630573022172603026263 419093445859533258904539395)
        ·
          refine ⟨628640168789299888356809093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419093445859533258904539395 628640168789299888356809093)
          ·
            refine ⟨117870031647993729066901705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 628640168789299888356809093 117870031647993729066901705)
            ·
              refine ⟨88402523735995296800176279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117870031647993729066901705 88402523735995296800176279)
              ·
                refine ⟨132603785603992945200264419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88402523735995296800176279 132603785603992945200264419)
                ·
                  refine ⟨198905678405989417800396629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132603785603992945200264419 198905678405989417800396629)
                  ·
                    refine ⟨1165462959410094244924199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 198905678405989417800396629 1165462959410094244924199)
                    ·
                      rfl

theorem cell23_6809193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 9].length) (baseStart_6809193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809193 prefixEnd_6809193 := by exact prefixLift 6809193
  have htrace : WordTrace (prefixWord ++ tailWord_6809193) baseStart_6809193 baseEnd_6809193 := by
    simpa [prefixWord, tailWord_6809193, baseEnd_6809193] using wordTrace_append hprefix tailTrace_6809193
  have hstable : (prefixWord ++ tailWord_6809193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809193).length < 2 ^ (prefixWord ++ tailWord_6809193).sum := by decide
  have hdescent : baseEnd_6809193 < baseStart_6809193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809287 : List Nat := [1, 1, 4, 1, 1, 1, 4, 5, 5]
def baseStart_6809287 : Nat := 118140960795 + 6809287 * 2 ^ 59
def prefixEnd_6809287 : Nat := 4983230072969 + 3 ^ 40 * 6809287 * 2
def baseEnd_6809287 : Nat := 388493016156867262999685

theorem tailTrace_6809287 : CollatzResearch.WordTrace tailWord_6809287 prefixEnd_6809287 388493016156867262999685 := by
  unfold tailWord_6809287
  simp only [CollatzResearch.WordTrace]
  refine ⟨248355100082123607478834115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165570066721415738319222743 248355100082123607478834115)
  ·
    refine ⟨372532650123185411218251173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248355100082123607478834115 372532650123185411218251173)
    ·
      refine ⟨69849871898097264603422095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372532650123185411218251173 69849871898097264603422095)
      ·
        refine ⟨104774807847145896905133143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69849871898097264603422095 104774807847145896905133143)
        ·
          refine ⟨157162211770718845357699715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104774807847145896905133143 157162211770718845357699715)
          ·
            refine ⟨235743317656078268036549573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157162211770718845357699715 235743317656078268036549573)
            ·
              refine ⟨44201872060514675256853045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235743317656078268036549573 44201872060514675256853045)
              ·
                refine ⟨4143925505673250805329973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44201872060514675256853045 4143925505673250805329973)
                ·
                  refine ⟨388493016156867262999685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4143925505673250805329973 388493016156867262999685)
                  ·
                    rfl

theorem cell23_6809287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 5].length) (baseStart_6809287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809287 prefixEnd_6809287 := by exact prefixLift 6809287
  have htrace : WordTrace (prefixWord ++ tailWord_6809287) baseStart_6809287 baseEnd_6809287 := by
    simpa [prefixWord, tailWord_6809287, baseEnd_6809287] using wordTrace_append hprefix tailTrace_6809287
  have hstable : (prefixWord ++ tailWord_6809287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809287).length < 2 ^ (prefixWord ++ tailWord_6809287).sum := by decide
  have hdescent : baseEnd_6809287 < baseStart_6809287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809298 : List Nat := [3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
def baseStart_6809298 : Nat := 118140960795 + 6809298 * 2 ^ 59
def prefixEnd_6809298 : Nat := 4983230072969 + 3 ^ 40 * 6809298 * 2
def baseEnd_6809298 : Nat := 3496442793699004823959615

theorem tailTrace_6809298 : CollatzResearch.WordTrace tailWord_6809298 prefixEnd_6809298 3496442793699004823959615 := by
  unfold tailWord_6809298
  simp only [CollatzResearch.WordTrace]
  refine ⟨62088875321270939089371137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165570334190055837571656365 62088875321270939089371137)
  ·
    refine ⟨46566656490953204317028353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62088875321270939089371137 46566656490953204317028353)
    ·
      refine ⟨34924992368214903237771265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46566656490953204317028353 34924992368214903237771265)
      ·
        refine ⟨26193744276161177428328449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34924992368214903237771265 26193744276161177428328449)
        ·
          refine ⟨19645308207120883071246337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26193744276161177428328449 19645308207120883071246337)
          ·
            refine ⟨14733981155340662303434753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19645308207120883071246337 14733981155340662303434753)
            ·
              refine ⟨11050485866505496727576065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14733981155340662303434753 11050485866505496727576065)
              ·
                refine ⟨8287864399879122545682049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11050485866505496727576065 8287864399879122545682049)
                ·
                  refine ⟨6215898299909341909261537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8287864399879122545682049 6215898299909341909261537)
                  ·
                    refine ⟨4661923724932006431946153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6215898299909341909261537 4661923724932006431946153)
                    ·
                      refine ⟨3496442793699004823959615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4661923724932006431946153 3496442793699004823959615)
                      ·
                        rfl

theorem cell23_6809298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_6809298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809298 prefixEnd_6809298 := by exact prefixLift 6809298
  have htrace : WordTrace (prefixWord ++ tailWord_6809298) baseStart_6809298 baseEnd_6809298 := by
    simpa [prefixWord, tailWord_6809298, baseEnd_6809298] using wordTrace_append hprefix tailTrace_6809298
  have hstable : (prefixWord ++ tailWord_6809298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809298).length < 2 ^ (prefixWord ++ tailWord_6809298).sum := by decide
  have hdescent : baseEnd_6809298 < baseStart_6809298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809334 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_6809334 : Nat := 118140960795 + 6809334 * 2 ^ 59
def prefixEnd_6809334 : Nat := 4983230072969 + 3 ^ 40 * 6809334 * 2
def baseEnd_6809334 : Nat := 1165487093000855561036483

theorem tailTrace_6809334 : CollatzResearch.WordTrace tailWord_6809334 prefixEnd_6809334 1165487093000855561036483 := by
  unfold tailWord_6809334
  simp only [CollatzResearch.WordTrace]
  refine ⟨15522300894559583406612191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165571209541968889670530037 15522300894559583406612191)
  ·
    refine ⟨23283451341839375109918287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15522300894559583406612191 23283451341839375109918287)
    ·
      refine ⟨34925177012759062664877431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23283451341839375109918287 34925177012759062664877431)
      ·
        refine ⟨52387765519138593997316147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34925177012759062664877431 52387765519138593997316147)
        ·
          refine ⟨78581648278707890995974221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52387765519138593997316147 78581648278707890995974221)
          ·
            refine ⟨29468118104515459123490333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78581648278707890995974221 29468118104515459123490333)
            ·
              refine ⟨11050544289193297171308875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29468118104515459123490333 11050544289193297171308875)
              ·
                refine ⟨16575816433789945756963313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11050544289193297171308875 16575816433789945756963313)
                ·
                  refine ⟨12431862325342459317722485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16575816433789945756963313 12431862325342459317722485)
                  ·
                    refine ⟨1165487093000855561036483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12431862325342459317722485 1165487093000855561036483)
                    ·
                      rfl

theorem cell23_6809334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_6809334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809334 prefixEnd_6809334 := by exact prefixLift 6809334
  have htrace : WordTrace (prefixWord ++ tailWord_6809334) baseStart_6809334 baseEnd_6809334 := by
    simpa [prefixWord, tailWord_6809334, baseEnd_6809334] using wordTrace_append hprefix tailTrace_6809334
  have hstable : (prefixWord ++ tailWord_6809334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809334).length < 2 ^ (prefixWord ++ tailWord_6809334).sum := by decide
  have hdescent : baseEnd_6809334 < baseStart_6809334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809354 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 2, 4, 2]
def baseStart_6809354 : Nat := 118140960795 + 6809354 * 2 ^ 59
def prefixEnd_6809354 : Nat := 4983230072969 + 3 ^ 40 * 6809354 * 2
def baseEnd_6809354 : Nat := 3496471548615656604859357

theorem tailTrace_6809354 : CollatzResearch.WordTrace tailWord_6809354 prefixEnd_6809354 3496471548615656604859357 := by
  unfold tailWord_6809354
  simp only [CollatzResearch.WordTrace]
  refine ⟨62089385943220219480380779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165571695848587251947682077 62089385943220219480380779)
  ·
    refine ⟨93134078914830329220571169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62089385943220219480380779 93134078914830329220571169)
    ·
      refine ⟨69850559186122746915428377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93134078914830329220571169 69850559186122746915428377)
      ·
        refine ⟨52387919389592060186571283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69850559186122746915428377 52387919389592060186571283)
        ·
          refine ⟨78581879084388090279856925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52387919389592060186571283 78581879084388090279856925)
          ·
            refine ⟨29468204656645533854946347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78581879084388090279856925 29468204656645533854946347)
            ·
              refine ⟨44202306984968300782419521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29468204656645533854946347 44202306984968300782419521)
              ·
                refine ⟨33151730238726225586814641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44202306984968300782419521 33151730238726225586814641)
                ·
                  refine ⟨24863797679044669190110981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33151730238726225586814641 24863797679044669190110981)
                  ·
                    refine ⟨4661962064820875473145809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24863797679044669190110981 4661962064820875473145809)
                    ·
                      refine ⟨3496471548615656604859357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4661962064820875473145809 3496471548615656604859357)
                      ·
                        rfl

theorem cell23_6809354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_6809354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809354 prefixEnd_6809354 := by exact prefixLift 6809354
  have htrace : WordTrace (prefixWord ++ tailWord_6809354) baseStart_6809354 baseEnd_6809354 := by
    simpa [prefixWord, tailWord_6809354, baseEnd_6809354] using wordTrace_append hprefix tailTrace_6809354
  have hstable : (prefixWord ++ tailWord_6809354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809354).length < 2 ^ (prefixWord ++ tailWord_6809354).sum := by decide
  have hdescent : baseEnd_6809354 < baseStart_6809354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809404 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 5, 1, 3]
def baseStart_6809404 : Nat := 118140960795 + 6809404 * 2 ^ 59
def prefixEnd_6809404 : Nat := 4983230072969 + 3 ^ 40 * 6809404 * 2
def baseEnd_6809404 : Nat := 3496497222648381409234127

theorem tailTrace_6809404 : CollatzResearch.WordTrace tailWord_6809404 prefixEnd_6809404 3496497222648381409234127 := by
  unfold tailWord_6809404
  simp only [CollatzResearch.WordTrace]
  refine ⟨124179683711349868230421633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165572911615133157640562177 124179683711349868230421633)
  ·
    refine ⟨93134762783512401172816225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124179683711349868230421633 93134762783512401172816225)
    ·
      refine ⟨69851072087634300879612169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93134762783512401172816225 69851072087634300879612169)
      ·
        refine ⟨52388304065725725659709127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69851072087634300879612169 52388304065725725659709127)
        ·
          refine ⟨78582456098588588489563691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52388304065725725659709127 78582456098588588489563691)
          ·
            refine ⟨117873684147882882734345537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78582456098588588489563691 117873684147882882734345537)
            ·
              refine ⟨88405263110912162050759153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117873684147882882734345537 88405263110912162050759153)
              ·
                refine ⟨66303947333184121538069365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88405263110912162050759153 66303947333184121538069365)
                ·
                  refine ⟨6215995062486011394194003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66303947333184121538069365 6215995062486011394194003)
                  ·
                    refine ⟨9323992593729017091291005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6215995062486011394194003 9323992593729017091291005)
                    ·
                      refine ⟨3496497222648381409234127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9323992593729017091291005 3496497222648381409234127)
                      ·
                        rfl

theorem cell23_6809404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_6809404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809404 prefixEnd_6809404 := by exact prefixLift 6809404
  have htrace : WordTrace (prefixWord ++ tailWord_6809404) baseStart_6809404 baseEnd_6809404 := by
    simpa [prefixWord, tailWord_6809404, baseEnd_6809404] using wordTrace_append hprefix tailTrace_6809404
  have hstable : (prefixWord ++ tailWord_6809404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809404).length < 2 ^ (prefixWord ++ tailWord_6809404).sum := by decide
  have hdescent : baseEnd_6809404 < baseStart_6809404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809454 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 3, 6]
def baseStart_6809454 : Nat := 118140960795 + 6809454 * 2 ^ 59
def prefixEnd_6809454 : Nat := 4983230072969 + 3 ^ 40 * 6809454 * 2
def baseEnd_6809454 : Nat := 1165507632227035404536299

theorem tailTrace_6809454 : CollatzResearch.WordTrace tailWord_6809454 prefixEnd_6809454 1165507632227035404536299 := by
  unfold tailWord_6809454
  simp only [CollatzResearch.WordTrace]
  refine ⟨31045148884064824375020427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165574127381679063333442277 31045148884064824375020427)
  ·
    refine ⟨46567723326097236562530641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31045148884064824375020427 46567723326097236562530641)
    ·
      refine ⟨34925792494572927421897981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46567723326097236562530641 34925792494572927421897981)
      ·
        refine ⟨13097172185464847783211743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34925792494572927421897981 13097172185464847783211743)
        ·
          refine ⟨19645758278197271674817615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13097172185464847783211743 19645758278197271674817615)
          ·
            refine ⟨29468637417295907512226423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19645758278197271674817615 29468637417295907512226423)
            ·
              refine ⟨44202956125943861268339635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29468637417295907512226423 44202956125943861268339635)
              ·
                refine ⟨66304434188915791902509453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44202956125943861268339635 66304434188915791902509453)
                ·
                  refine ⟨24864162820843421963441045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66304434188915791902509453 24864162820843421963441045)
                  ·
                    refine ⟨1165507632227035404536299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24864162820843421963441045 1165507632227035404536299)
                    ·
                      rfl

theorem cell23_6809454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_6809454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809454 prefixEnd_6809454 := by exact prefixLift 6809454
  have htrace : WordTrace (prefixWord ++ tailWord_6809454) baseStart_6809454 baseEnd_6809454 := by
    simpa [prefixWord, tailWord_6809454, baseEnd_6809454] using wordTrace_append hprefix tailTrace_6809454
  have hstable : (prefixWord ++ tailWord_6809454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809454).length < 2 ^ (prefixWord ++ tailWord_6809454).sum := by decide
  have hdescent : baseEnd_6809454 < baseStart_6809454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809507 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 5]
def baseStart_6809507 : Nat := 118140960795 + 6809507 * 2 ^ 59
def prefixEnd_6809507 : Nat := 4983230072969 + 3 ^ 40 * 6809507 * 2
def baseEnd_6809507 : Nat := 3496550111155794506246153

theorem tailTrace_6809507 : CollatzResearch.WordTrace tailWord_6809507 prefixEnd_6809507 3496550111155794506246153 := by
  unfold tailWord_6809507
  simp only [CollatzResearch.WordTrace]
  refine ⟨248363124141326585051842775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165575416094217723367895183 248363124141326585051842775)
  ·
    refine ⟨372544686211989877577764163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248363124141326585051842775 372544686211989877577764163)
    ·
      refine ⟨558817029317984816366646245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372544686211989877577764163 558817029317984816366646245)
      ·
        refine ⟨104778192997122153068746171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 558817029317984816366646245 104778192997122153068746171)
        ·
          refine ⟨157167289495683229603119257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104778192997122153068746171 157167289495683229603119257)
          ·
            refine ⟨117875467121762422202339443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157167289495683229603119257 117875467121762422202339443)
            ·
              refine ⟨176813200682643633303509165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117875467121762422202339443 176813200682643633303509165)
              ·
                refine ⟨66304950255991362488815937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176813200682643633303509165 66304950255991362488815937)
                ·
                  refine ⟨49728712691993521866611953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66304950255991362488815937 49728712691993521866611953)
                  ·
                    refine ⟨37296534518995141399958965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49728712691993521866611953 37296534518995141399958965)
                    ·
                      refine ⟨3496550111155794506246153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37296534518995141399958965 3496550111155794506246153)
                      ·
                        rfl

theorem cell23_6809507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_6809507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809507 prefixEnd_6809507 := by exact prefixLift 6809507
  have htrace : WordTrace (prefixWord ++ tailWord_6809507) baseStart_6809507 baseEnd_6809507 := by
    simpa [prefixWord, tailWord_6809507, baseEnd_6809507] using wordTrace_append hprefix tailTrace_6809507
  have hstable : (prefixWord ++ tailWord_6809507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809507).length < 2 ^ (prefixWord ++ tailWord_6809507).sum := by decide
  have hdescent : baseEnd_6809507 < baseStart_6809507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809511 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_6809511 : Nat := 118140960795 + 6809511 * 2 ^ 59
def prefixEnd_6809511 : Nat := 4983230072969 + 3 ^ 40 * 6809511 * 2
def baseEnd_6809511 : Nat := 3496552165078412490596135

theorem tailTrace_6809511 : CollatzResearch.WordTrace tailWord_6809511 prefixEnd_6809511 3496552165078412490596135 := by
  unfold tailWord_6809511
  simp only [CollatzResearch.WordTrace]
  refine ⟨248363270033312093734988387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165575513355541395823325591 248363270033312093734988387)
  ·
    refine ⟨372544905049968140602482581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248363270033312093734988387 372544905049968140602482581)
    ·
      refine ⟨17463042424217256590741371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 372544905049968140602482581 17463042424217256590741371)
      ·
        refine ⟨26194563636325884886112057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17463042424217256590741371 26194563636325884886112057)
        ·
          refine ⟨19645922727244413664584043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26194563636325884886112057 19645922727244413664584043)
          ·
            refine ⟨29468884090866620496876065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19645922727244413664584043 29468884090866620496876065)
            ·
              refine ⟨22101663068149965372657049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29468884090866620496876065 22101663068149965372657049)
              ·
                refine ⟨16576247301112474029492787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22101663068149965372657049 16576247301112474029492787)
                ·
                  refine ⟨24864370951668711044239181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16576247301112474029492787 24864370951668711044239181)
                  ·
                    refine ⟨9324139106875766641589693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24864370951668711044239181 9324139106875766641589693)
                    ·
                      refine ⟨3496552165078412490596135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9324139106875766641589693 3496552165078412490596135)
                      ·
                        rfl

theorem cell23_6809511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_6809511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809511 prefixEnd_6809511 := by exact prefixLift 6809511
  have htrace : WordTrace (prefixWord ++ tailWord_6809511) baseStart_6809511 baseEnd_6809511 := by
    simpa [prefixWord, tailWord_6809511, baseEnd_6809511] using wordTrace_append hprefix tailTrace_6809511
  have hstable : (prefixWord ++ tailWord_6809511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809511).length < 2 ^ (prefixWord ++ tailWord_6809511).sum := by decide
  have hdescent : baseEnd_6809511 < baseStart_6809511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809512 : List Nat := [2, 1, 6, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_6809512 : Nat := 118140960795 + 6809512 * 2 ^ 59
def prefixEnd_6809512 : Nat := 4983230072969 + 3 ^ 40 * 6809512 * 2
def baseEnd_6809512 : Nat := 3496552678559066986683631

theorem tailTrace_6809512 : CollatzResearch.WordTrace tailWord_6809512 prefixEnd_6809512 3496552678559066986683631 := by
  unfold tailWord_6809512
  simp only [CollatzResearch.WordTrace]
  refine ⟨124181653253154235452887395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165575537670872313937183193 124181653253154235452887395)
  ·
    refine ⟨186272479879731353179331093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124181653253154235452887395 186272479879731353179331093)
    ·
      refine ⟨8731522494362407180281145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 186272479879731353179331093 8731522494362407180281145)
      ·
        refine ⟨6548641870771805385210859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8731522494362407180281145 6548641870771805385210859)
        ·
          refine ⟨9822962806157708077816289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6548641870771805385210859 9822962806157708077816289)
          ·
            refine ⟨7367222104618281058362217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9822962806157708077816289 7367222104618281058362217)
            ·
              refine ⟨5525416578463710793771663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7367222104618281058362217 5525416578463710793771663)
              ·
                refine ⟨8288124867695566190657495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5525416578463710793771663 8288124867695566190657495)
                ·
                  refine ⟨12432187301543349285986243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8288124867695566190657495 12432187301543349285986243)
                  ·
                    refine ⟨18648280952315023928979365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12432187301543349285986243 18648280952315023928979365)
                    ·
                      refine ⟨3496552678559066986683631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18648280952315023928979365 3496552678559066986683631)
                      ·
                        rfl

theorem cell23_6809512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_6809512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809512 prefixEnd_6809512 := by exact prefixLift 6809512
  have htrace : WordTrace (prefixWord ++ tailWord_6809512) baseStart_6809512 baseEnd_6809512 := by
    simpa [prefixWord, tailWord_6809512, baseEnd_6809512] using wordTrace_append hprefix tailTrace_6809512
  have hstable : (prefixWord ++ tailWord_6809512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809512).length < 2 ^ (prefixWord ++ tailWord_6809512).sum := by decide
  have hdescent : baseEnd_6809512 < baseStart_6809512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809518 : List Nat := [4, 1, 5, 1, 1, 1, 10]
def baseStart_6809518 : Nat := 118140960795 + 6809518 * 2 ^ 59
def prefixEnd_6809518 : Nat := 4983230072969 + 3 ^ 40 * 6809518 * 2
def baseEnd_6809518 : Nat := 43167355054851777323563

theorem tailTrace_6809518 : CollatzResearch.WordTrace tailWord_6809518 prefixEnd_6809518 43167355054851777323563 := by
  unfold tailWord_6809518
  simp only [CollatzResearch.WordTrace]
  refine ⟨31045440668035841741311651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165575683562857822620328805 31045440668035841741311651)
  ·
    refine ⟨46568161002053762611967477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31045440668035841741311651 46568161002053762611967477)
    ·
      refine ⟨4365765093942540244871951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46568161002053762611967477 4365765093942540244871951)
      ·
        refine ⟨6548647640913810367307927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4365765093942540244871951 6548647640913810367307927)
        ·
          refine ⟨9822971461370715550961891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6548647640913810367307927 9822971461370715550961891)
          ·
            refine ⟨14734457192056073326442837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9822971461370715550961891 14734457192056073326442837)
            ·
              refine ⟨43167355054851777323563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14734457192056073326442837 43167355054851777323563)
              ·
                rfl

theorem cell23_6809518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 10].length) (baseStart_6809518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809518 prefixEnd_6809518 := by exact prefixLift 6809518
  have htrace : WordTrace (prefixWord ++ tailWord_6809518) baseStart_6809518 baseEnd_6809518 := by
    simpa [prefixWord, tailWord_6809518, baseEnd_6809518] using wordTrace_append hprefix tailTrace_6809518
  have hstable : (prefixWord ++ tailWord_6809518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809518).length < 2 ^ (prefixWord ++ tailWord_6809518).sum := by decide
  have hdescent : baseEnd_6809518 < baseStart_6809518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809544 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 2, 6]
def baseStart_6809544 : Nat := 118140960795 + 6809544 * 2 ^ 59
def prefixEnd_6809544 : Nat := 4983230072969 + 3 ^ 40 * 6809544 * 2
def baseEnd_6809544 : Nat := 1165523036646670287161161

theorem tailTrace_6809544 : CollatzResearch.WordTrace tailWord_6809544 prefixEnd_6809544 1165523036646670287161161 := by
  unfold tailWord_6809544
  simp only [CollatzResearch.WordTrace]
  refine ⟨124182236821096270185469843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165576315761461693580626457 124182236821096270185469843)
  ·
    refine ⟨186273355231644405278204765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124182236821096270185469843 186273355231644405278204765)
    ·
      refine ⟨69852508211866651979326787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186273355231644405278204765 69852508211866651979326787)
      ·
        refine ⟨104778762317799977968990181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69852508211866651979326787 104778762317799977968990181)
        ·
          refine ⟨19646017934587495869185659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104778762317799977968990181 19646017934587495869185659)
          ·
            refine ⟨29469026901881243803778489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19646017934587495869185659 29469026901881243803778489)
            ·
              refine ⟨22101770176410932852833867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29469026901881243803778489 22101770176410932852833867)
              ·
                refine ⟨33152655264616399279250801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22101770176410932852833867 33152655264616399279250801)
                ·
                  refine ⟨24864491448462299459438101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33152655264616399279250801 24864491448462299459438101)
                  ·
                    refine ⟨1165523036646670287161161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24864491448462299459438101 1165523036646670287161161)
                    ·
                      rfl

theorem cell23_6809544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_6809544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809544 prefixEnd_6809544 := by exact prefixLift 6809544
  have htrace : WordTrace (prefixWord ++ tailWord_6809544) baseStart_6809544 baseEnd_6809544 := by
    simpa [prefixWord, tailWord_6809544, baseEnd_6809544] using wordTrace_append hprefix tailTrace_6809544
  have hstable : (prefixWord ++ tailWord_6809544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809544).length < 2 ^ (prefixWord ++ tailWord_6809544).sum := by decide
  have hdescent : baseEnd_6809544 < baseStart_6809544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809577 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 1, 6, 6]
def baseStart_6809577 : Nat := 118140960795 + 6809577 * 2 ^ 59
def prefixEnd_6809577 : Nat := 4983230072969 + 3 ^ 40 * 6809577 * 2
def baseEnd_6809577 : Nat := 3496586054801609232370831

theorem tailTrace_6809577 : CollatzResearch.WordTrace tailWord_6809577 prefixEnd_6809577 3496586054801609232370831 := by
  unfold tailWord_6809577
  simp only [CollatzResearch.WordTrace]
  refine ⟨248365677251072987006890985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165577118167381991337927323 248365677251072987006890985)
  ·
    refine ⟨186274257938304740255168239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248365677251072987006890985 186274257938304740255168239)
    ·
      refine ⟨279411386907457110382752359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186274257938304740255168239 279411386907457110382752359)
      ·
        refine ⟨419117080361185665574128539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279411386907457110382752359 419117080361185665574128539)
        ·
          refine ⟨628675620541778498361192809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419117080361185665574128539 628675620541778498361192809)
          ·
            refine ⟨471506715406333873770894607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628675620541778498361192809 471506715406333873770894607)
            ·
              refine ⟨707260073109500810656341911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471506715406333873770894607 707260073109500810656341911)
              ·
                refine ⟨1060890109664251215984512867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707260073109500810656341911 1060890109664251215984512867)
                ·
                  refine ⟨1591335164496376823976769301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060890109664251215984512867 1591335164496376823976769301)
                  ·
                    refine ⟨74593835835767663623911061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1591335164496376823976769301 74593835835767663623911061)
                    ·
                      refine ⟨3496586054801609232370831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74593835835767663623911061 3496586054801609232370831)
                      ·
                        rfl

theorem cell23_6809577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_6809577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809577 prefixEnd_6809577 := by exact prefixLift 6809577
  have htrace : WordTrace (prefixWord ++ tailWord_6809577) baseStart_6809577 baseEnd_6809577 := by
    simpa [prefixWord, tailWord_6809577, baseEnd_6809577] using wordTrace_append hprefix tailTrace_6809577
  have hstable : (prefixWord ++ tailWord_6809577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809577).length < 2 ^ (prefixWord ++ tailWord_6809577).sum := by decide
  have hdescent : baseEnd_6809577 < baseStart_6809577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809584 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 3]
def baseStart_6809584 : Nat := 118140960795 + 6809584 * 2 ^ 59
def prefixEnd_6809584 : Nat := 4983230072969 + 3 ^ 40 * 6809584 * 2
def baseEnd_6809584 : Nat := 3496589649166190704983299

theorem tailTrace_6809584 : CollatzResearch.WordTrace tailWord_6809584 prefixEnd_6809584 3496589649166190704983299 := by
  unfold tailWord_6809584
  simp only [CollatzResearch.WordTrace]
  refine ⟨124182966281023813601197903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165577288374698418134930537 124182966281023813601197903)
  ·
    refine ⟨186274449421535720401796855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124182966281023813601197903 186274449421535720401796855)
    ·
      refine ⟨279411674132303580602695283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186274449421535720401796855 279411674132303580602695283)
      ·
        refine ⟨419117511198455370904042925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279411674132303580602695283 419117511198455370904042925)
        ·
          refine ⟨157169066699420764089016097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 419117511198455370904042925 157169066699420764089016097)
          ·
            refine ⟨117876800024565573066762073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157169066699420764089016097 117876800024565573066762073)
            ·
              refine ⟨88407600018424179800071555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117876800024565573066762073 88407600018424179800071555)
              ·
                refine ⟨132611400027636269700107333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88407600018424179800071555 132611400027636269700107333)
                ·
                  refine ⟨24864637505181800568770125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132611400027636269700107333 24864637505181800568770125)
                  ·
                    refine ⟨9324239064443175213288797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24864637505181800568770125 9324239064443175213288797)
                    ·
                      refine ⟨3496589649166190704983299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9324239064443175213288797 3496589649166190704983299)
                      ·
                        rfl

theorem cell23_6809584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 3].length) (baseStart_6809584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809584 prefixEnd_6809584 := by exact prefixLift 6809584
  have htrace : WordTrace (prefixWord ++ tailWord_6809584) baseStart_6809584 baseEnd_6809584 := by
    simpa [prefixWord, tailWord_6809584, baseEnd_6809584] using wordTrace_append hprefix tailTrace_6809584
  have hstable : (prefixWord ++ tailWord_6809584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809584).length < 2 ^ (prefixWord ++ tailWord_6809584).sum := by decide
  have hdescent : baseEnd_6809584 < baseStart_6809584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809614 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_6809614 : Nat := 118140960795 + 6809614 * 2 ^ 59
def prefixEnd_6809614 : Nat := 4983230072969 + 3 ^ 40 * 6809614 * 2
def baseEnd_6809614 : Nat := 3496605053585825587608161

theorem tailTrace_6809614 : CollatzResearch.WordTrace tailWord_6809614 prefixEnd_6809614 3496605053585825587608161 := by
  unfold tailWord_6809614
  simp only [CollatzResearch.WordTrace]
  refine ⟨31045878343992367790748487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165578017834625961550658597 31045878343992367790748487)
  ·
    refine ⟨46568817515988551686122731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31045878343992367790748487 46568817515988551686122731)
    ·
      refine ⟨69853226273982827529184097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46568817515988551686122731 69853226273982827529184097)
      ·
        refine ⟨52389919705487120646888073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69853226273982827529184097 52389919705487120646888073)
        ·
          refine ⟨39292439779115340485166055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52389919705487120646888073 39292439779115340485166055)
          ·
            refine ⟨58938659668673010727749083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39292439779115340485166055 58938659668673010727749083)
            ·
              refine ⟨88407989503009516091623625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58938659668673010727749083 88407989503009516091623625)
              ·
                refine ⟨66305992127257137068717719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88407989503009516091623625 66305992127257137068717719)
                ·
                  refine ⟨99458988190885705603076579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66305992127257137068717719 99458988190885705603076579)
                  ·
                    refine ⟨149188482286328558404614869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99458988190885705603076579 149188482286328558404614869)
                    ·
                      refine ⟨3496605053585825587608161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149188482286328558404614869 3496605053585825587608161)
                      ·
                        rfl

theorem cell23_6809614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_6809614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809614 prefixEnd_6809614 := by exact prefixLift 6809614
  have htrace : WordTrace (prefixWord ++ tailWord_6809614) baseStart_6809614 baseEnd_6809614 := by
    simpa [prefixWord, tailWord_6809614, baseEnd_6809614] using wordTrace_append hprefix tailTrace_6809614
  have hstable : (prefixWord ++ tailWord_6809614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809614).length < 2 ^ (prefixWord ++ tailWord_6809614).sum := by decide
  have hdescent : baseEnd_6809614 < baseStart_6809614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809661 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 1, 4, 3]
def baseStart_6809661 : Nat := 118140960795 + 6809661 * 2 ^ 59
def prefixEnd_6809661 : Nat := 4983230072969 + 3 ^ 40 * 6809661 * 2
def baseEnd_6809661 : Nat := 3496629187176586903720445

theorem tailTrace_6809661 : CollatzResearch.WordTrace tailWord_6809661 prefixEnd_6809661 3496629187176586903720445 := by
  unfold tailWord_6809661
  simp only [CollatzResearch.WordTrace]
  refine ⟨248368740982768669352948837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165579160655179112901965891 248368740982768669352948837)
  ·
    refine ⟨46569138934269125503677907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248368740982768669352948837 46569138934269125503677907)
    ·
      refine ⟨69853708401403688255516861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46569138934269125503677907 69853708401403688255516861)
      ·
        refine ⟨26195140650526383095818823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69853708401403688255516861 26195140650526383095818823)
        ·
          refine ⟨39292710975789574643728235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26195140650526383095818823 39292710975789574643728235)
          ·
            refine ⟨58939066463684361965592353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39292710975789574643728235 58939066463684361965592353)
            ·
              refine ⟨44204299847763271474194265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58939066463684361965592353 44204299847763271474194265)
              ·
                refine ⟨33153224885822453605645699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44204299847763271474194265 33153224885822453605645699)
                ·
                  refine ⟨49729837328733680408468549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33153224885822453605645699 49729837328733680408468549)
                  ·
                    refine ⟨9324344499137565076587853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49729837328733680408468549 9324344499137565076587853)
                    ·
                      refine ⟨3496629187176586903720445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9324344499137565076587853 3496629187176586903720445)
                      ·
                        rfl

theorem cell23_6809661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_6809661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809661 prefixEnd_6809661 := by exact prefixLift 6809661
  have htrace : WordTrace (prefixWord ++ tailWord_6809661) baseStart_6809661 baseEnd_6809661 := by
    simpa [prefixWord, tailWord_6809661, baseEnd_6809661] using wordTrace_append hprefix tailTrace_6809661
  have hstable : (prefixWord ++ tailWord_6809661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809661).length < 2 ^ (prefixWord ++ tailWord_6809661).sum := by decide
  have hdescent : baseEnd_6809661 < baseStart_6809661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809678 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3]
def baseStart_6809678 : Nat := 118140960795 + 6809678 * 2 ^ 59
def prefixEnd_6809678 : Nat := 4983230072969 + 3 ^ 40 * 6809678 * 2
def baseEnd_6809678 : Nat := 3496637916347713337207867

theorem tailTrace_6809678 : CollatzResearch.WordTrace tailWord_6809678 prefixEnd_6809678 3496637916347713337207867 := by
  unfold tailWord_6809678
  simp only [CollatzResearch.WordTrace]
  refine ⟨31046170127963385157039711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165579574015804720837545125 31046170127963385157039711)
  ·
    refine ⟨46569255191945077735559567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31046170127963385157039711 46569255191945077735559567)
    ·
      refine ⟨69853882787917616603339351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46569255191945077735559567 69853882787917616603339351)
      ·
        refine ⟨104780824181876424905009027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69853882787917616603339351 104780824181876424905009027)
        ·
          refine ⟨157171236272814637357513541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104780824181876424905009027 157171236272814637357513541)
          ·
            refine ⟨29469606801152744504533789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157171236272814637357513541 29469606801152744504533789)
            ·
              refine ⟨11051102550432279189200171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29469606801152744504533789 11051102550432279189200171)
              ·
                refine ⟨16576653825648418783800257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11051102550432279189200171 16576653825648418783800257)
                ·
                  refine ⟨12432490369236314087850193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16576653825648418783800257 12432490369236314087850193)
                  ·
                    refine ⟨9324367776927235565887645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12432490369236314087850193 9324367776927235565887645)
                    ·
                      refine ⟨3496637916347713337207867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9324367776927235565887645 3496637916347713337207867)
                      ·
                        rfl

theorem cell23_6809678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_6809678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809678 prefixEnd_6809678 := by exact prefixLift 6809678
  have htrace : WordTrace (prefixWord ++ tailWord_6809678) baseStart_6809678 baseEnd_6809678 := by
    simpa [prefixWord, tailWord_6809678, baseEnd_6809678] using wordTrace_append hprefix tailTrace_6809678
  have hstable : (prefixWord ++ tailWord_6809678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809678).length < 2 ^ (prefixWord ++ tailWord_6809678).sum := by decide
  have hdescent : baseEnd_6809678 < baseStart_6809678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809685 : List Nat := [1, 3, 2, 2, 1, 4, 2, 3, 1, 4]
def baseStart_6809685 : Nat := 118140960795 + 6809685 * 2 ^ 59
def prefixEnd_6809685 : Nat := 4983230072969 + 3 ^ 40 * 6809685 * 2
def baseEnd_6809685 : Nat := 1165547170237431603273445

theorem tailTrace_6809685 : CollatzResearch.WordTrace tailWord_6809685 prefixEnd_6809685 1165547170237431603273445 := by
  unfold tailWord_6809685
  simp only [CollatzResearch.WordTrace]
  refine ⟨248369616334681721451822509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165579744223121147634548339 248369616334681721451822509)
  ·
    refine ⟨93138606125505645544433441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248369616334681721451822509 93138606125505645544433441)
    ·
      refine ⟨69853954594129234158325081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93138606125505645544433441 69853954594129234158325081)
      ·
        refine ⟨52390465945596925618743811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69853954594129234158325081 52390465945596925618743811)
        ·
          refine ⟨78585698918395388428115717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52390465945596925618743811 78585698918395388428115717)
          ·
            refine ⟨14734818547199135330271697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78585698918395388428115717 14734818547199135330271697)
            ·
              refine ⟨11051113910399351497703773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14734818547199135330271697 11051113910399351497703773)
              ·
                refine ⟨4144167716399756811638915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11051113910399351497703773 4144167716399756811638915)
                ·
                  refine ⟨6216251574599635217458373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4144167716399756811638915 6216251574599635217458373)
                  ·
                    refine ⟨1165547170237431603273445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6216251574599635217458373 1165547170237431603273445)
                    ·
                      rfl

theorem cell23_6809685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_6809685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809685 prefixEnd_6809685 := by exact prefixLift 6809685
  have htrace : WordTrace (prefixWord ++ tailWord_6809685) baseStart_6809685 baseEnd_6809685 := by
    simpa [prefixWord, tailWord_6809685, baseEnd_6809685] using wordTrace_append hprefix tailTrace_6809685
  have hstable : (prefixWord ++ tailWord_6809685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809685).length < 2 ^ (prefixWord ++ tailWord_6809685).sum := by decide
  have hdescent : baseEnd_6809685 < baseStart_6809685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809698 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 8]
def baseStart_6809698 : Nat := 118140960795 + 6809698 * 2 ^ 59
def prefixEnd_6809698 : Nat := 4983230072969 + 3 ^ 40 * 6809698 * 2
def baseEnd_6809698 : Nat := 388516465106755917661975

theorem tailTrace_6809698 : CollatzResearch.WordTrace tailWord_6809698 prefixEnd_6809698 388516465106755917661975 := by
  unfold tailWord_6809698
  simp only [CollatzResearch.WordTrace]
  refine ⟨62092522620908656168011437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165580060322423083114697165 62092522620908656168011437)
  ·
    refine ⟨23284695982840746063004289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62092522620908656168011437 23284695982840746063004289)
    ·
      refine ⟨17463521987130559547253217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23284695982840746063004289 17463521987130559547253217)
      ·
        refine ⟨13097641490347919660439913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17463521987130559547253217 13097641490347919660439913)
        ·
          refine ⟨9823231117760939745329935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13097641490347919660439913 9823231117760939745329935)
          ·
            refine ⟨14734846676641409617994903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9823231117760939745329935 14734846676641409617994903)
            ·
              refine ⟨22102270014962114426992355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14734846676641409617994903 22102270014962114426992355)
              ·
                refine ⟨33153405022443171640488533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22102270014962114426992355 33153405022443171640488533)
                ·
                  refine ⟨388516465106755917661975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33153405022443171640488533 388516465106755917661975)
                  ·
                    rfl

theorem cell23_6809698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_6809698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809698 prefixEnd_6809698 := by exact prefixLift 6809698
  have htrace : WordTrace (prefixWord ++ tailWord_6809698) baseStart_6809698 baseEnd_6809698 := by
    simpa [prefixWord, tailWord_6809698, baseEnd_6809698] using wordTrace_append hprefix tailTrace_6809698
  have hstable : (prefixWord ++ tailWord_6809698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809698).length < 2 ^ (prefixWord ++ tailWord_6809698).sum := by decide
  have hdescent : baseEnd_6809698 < baseStart_6809698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809708 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 3]
def baseStart_6809708 : Nat := 118140960795 + 6809708 * 2 ^ 59
def prefixEnd_6809708 : Nat := 4983230072969 + 3 ^ 40 * 6809708 * 2
def baseEnd_6809708 : Nat := 3496653320767348219832729

theorem tailTrace_6809708 : CollatzResearch.WordTrace tailWord_6809708 prefixEnd_6809708 3496653320767348219832729 := by
  unfold tailWord_6809708
  simp only [CollatzResearch.WordTrace]
  refine ⟨124185227606799198189954889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165580303475732264253273185 124185227606799198189954889)
  ·
    refine ⟨93138920705099398642466167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124185227606799198189954889 93138920705099398642466167)
    ·
      refine ⟨139708381057649097963699251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93138920705099398642466167 139708381057649097963699251)
      ·
        refine ⟨209562571586473646945548877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139708381057649097963699251 209562571586473646945548877)
        ·
          refine ⟨78585964344927617604580829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209562571586473646945548877 78585964344927617604580829)
          ·
            refine ⟨29469736629347856601717811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78585964344927617604580829 29469736629347856601717811)
            ·
              refine ⟨44204604944021784902576717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29469736629347856601717811 44204604944021784902576717)
              ·
                refine ⟨16576726854008169338466269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44204604944021784902576717 16576726854008169338466269)
                ·
                  refine ⟨6216272570253063501924851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16576726854008169338466269 6216272570253063501924851)
                  ·
                    refine ⟨9324408855379595252887277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6216272570253063501924851 9324408855379595252887277)
                    ·
                      refine ⟨3496653320767348219832729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9324408855379595252887277 3496653320767348219832729)
                      ·
                        rfl

theorem cell23_6809708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_6809708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809708 prefixEnd_6809708 := by exact prefixLift 6809708
  have htrace : WordTrace (prefixWord ++ tailWord_6809708) baseStart_6809708 baseEnd_6809708 := by
    simpa [prefixWord, tailWord_6809708, baseEnd_6809708] using wordTrace_append hprefix tailTrace_6809708
  have hstable : (prefixWord ++ tailWord_6809708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809708).length < 2 ^ (prefixWord ++ tailWord_6809708).sum := by decide
  have hdescent : baseEnd_6809708 < baseStart_6809708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809759 : List Nat := [1, 1, 2, 6, 1, 2, 3, 2, 1, 1, 3]
def baseStart_6809759 : Nat := 118140960795 + 6809759 * 2 ^ 59
def prefixEnd_6809759 : Nat := 4983230072969 + 3 ^ 40 * 6809759 * 2
def baseEnd_6809759 : Nat := 3496679508280727520294995

theorem tailTrace_6809759 : CollatzResearch.WordTrace tailWord_6809759 prefixEnd_6809759 3496679508280727520294995 := by
  unfold tailWord_6809759
  simp only [CollatzResearch.WordTrace]
  refine ⟨248372315336413632090016331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165581543557609088060010887 248372315336413632090016331)
  ·
    refine ⟨372558473004620448135024497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248372315336413632090016331 372558473004620448135024497)
    ·
      refine ⟨279418854753465336101268373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372558473004620448135024497 279418854753465336101268373)
      ·
        refine ⟨13097758816568687629746955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 279418854753465336101268373 13097758816568687629746955)
        ·
          refine ⟨19646638224853031444620433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13097758816568687629746955 19646638224853031444620433)
          ·
            refine ⟨14734978668639773583465325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19646638224853031444620433 14734978668639773583465325)
            ·
              refine ⟨5525617000739915093799497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14734978668639773583465325 5525617000739915093799497)
              ·
                refine ⟨4144212750554936320349623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5525617000739915093799497 4144212750554936320349623)
                ·
                  refine ⟨6216319125832404480524435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4144212750554936320349623 6216319125832404480524435)
                  ·
                    refine ⟨9324478688748606720786653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6216319125832404480524435 9324478688748606720786653)
                    ·
                      refine ⟨3496679508280727520294995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9324478688748606720786653 3496679508280727520294995)
                      ·
                        rfl

theorem cell23_6809759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_6809759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809759 prefixEnd_6809759 := by exact prefixLift 6809759
  have htrace : WordTrace (prefixWord ++ tailWord_6809759) baseStart_6809759 baseEnd_6809759 := by
    simpa [prefixWord, tailWord_6809759, baseEnd_6809759] using wordTrace_append hprefix tailTrace_6809759
  have hstable : (prefixWord ++ tailWord_6809759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809759).length < 2 ^ (prefixWord ++ tailWord_6809759).sum := by decide
  have hdescent : baseEnd_6809759 < baseStart_6809759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809761 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_6809761 : Nat := 118140960795 + 6809761 * 2 ^ 59
def prefixEnd_6809761 : Nat := 4983230072969 + 3 ^ 40 * 6809761 * 2
def baseEnd_6809761 : Nat := 3496680535242036512469985

theorem tailTrace_6809761 : CollatzResearch.WordTrace tailWord_6809761 prefixEnd_6809761 3496680535242036512469985 := by
  unfold tailWord_6809761
  simp only [CollatzResearch.WordTrace]
  refine ⟨248372388282406386431589137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165581592188270924287726091 248372388282406386431589137)
  ·
    refine ⟨186279291211804789823691853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248372388282406386431589137 186279291211804789823691853)
    ·
      refine ⟨69854734204426796183884445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186279291211804789823691853 69854734204426796183884445)
      ·
        refine ⟨26195525326660048568956667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69854734204426796183884445 26195525326660048568956667)
        ·
          refine ⟨39293287989990072853435001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26195525326660048568956667 39293287989990072853435001)
          ·
            refine ⟨29469965992492554640076251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39293287989990072853435001 29469965992492554640076251)
            ·
              refine ⟨44204948988738831960114377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29469965992492554640076251 44204948988738831960114377)
              ·
                refine ⟨33153711741554123970085783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44204948988738831960114377 33153711741554123970085783)
                ·
                  refine ⟨49730567612331185955128675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33153711741554123970085783 49730567612331185955128675)
                  ·
                    refine ⟨74595851418496778932693013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49730567612331185955128675 74595851418496778932693013)
                    ·
                      refine ⟨3496680535242036512469985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74595851418496778932693013 3496680535242036512469985)
                      ·
                        rfl

theorem cell23_6809761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_6809761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809761 prefixEnd_6809761 := by exact prefixLift 6809761
  have htrace : WordTrace (prefixWord ++ tailWord_6809761) baseStart_6809761 baseEnd_6809761 := by
    simpa [prefixWord, tailWord_6809761, baseEnd_6809761] using wordTrace_append hprefix tailTrace_6809761
  have hstable : (prefixWord ++ tailWord_6809761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809761).length < 2 ^ (prefixWord ++ tailWord_6809761).sum := by decide
  have hdescent : baseEnd_6809761 < baseStart_6809761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809816 : List Nat := [2, 1, 2, 2, 4, 3, 2, 2, 1, 2, 2]
def baseStart_6809816 : Nat := 118140960795 + 6809816 * 2 ^ 59
def prefixEnd_6809816 : Nat := 4983230072969 + 3 ^ 40 * 6809816 * 2
def baseEnd_6809816 : Nat := 3496708776678033797282233

theorem tailTrace_6809816 : CollatzResearch.WordTrace tailWord_6809816 prefixEnd_6809816 3496708776678033797282233 := by
  unfold tailWord_6809816
  simp only [CollatzResearch.WordTrace]
  refine ⟨124187197148603565412420651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165582929531471420549894201 124187197148603565412420651)
  ·
    refine ⟨186280795722905348118630977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124187197148603565412420651 186280795722905348118630977)
    ·
      refine ⟨139710596792179011088973233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186280795722905348118630977 139710596792179011088973233)
      ·
        refine ⟨104782947594134258316729925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139710596792179011088973233 104782947594134258316729925)
        ·
          refine ⟨19646802673900173434386861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104782947594134258316729925 19646802673900173434386861)
          ·
            refine ⟨7367551002712565037895073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19646802673900173434386861 7367551002712565037895073)
            ·
              refine ⟨5525663252034423778421305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7367551002712565037895073 5525663252034423778421305)
              ·
                refine ⟨4144247439025817833815979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5525663252034423778421305 4144247439025817833815979)
                ·
                  refine ⟨6216371158538726750723969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4144247439025817833815979 6216371158538726750723969)
                  ·
                    refine ⟨4662278368904045063042977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6216371158538726750723969 4662278368904045063042977)
                    ·
                      refine ⟨3496708776678033797282233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4662278368904045063042977 3496708776678033797282233)
                      ·
                        rfl

theorem cell23_6809816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_6809816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809816 prefixEnd_6809816 := by exact prefixLift 6809816
  have htrace : WordTrace (prefixWord ++ tailWord_6809816) baseStart_6809816 baseEnd_6809816 := by
    simpa [prefixWord, tailWord_6809816, baseEnd_6809816] using wordTrace_append hprefix tailTrace_6809816
  have hstable : (prefixWord ++ tailWord_6809816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809816).length < 2 ^ (prefixWord ++ tailWord_6809816).sum := by decide
  have hdescent : baseEnd_6809816 < baseStart_6809816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809841 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 4, 1, 5]
def baseStart_6809841 : Nat := 118140960795 + 6809841 * 2 ^ 59
def prefixEnd_6809841 : Nat := 4983230072969 + 3 ^ 40 * 6809841 * 2
def baseEnd_6809841 : Nat := 3496721613694396199469617

theorem tailTrace_6809841 : CollatzResearch.WordTrace tailWord_6809841 prefixEnd_6809841 3496721613694396199469617 := by
  unfold tailWord_6809841
  simp only [CollatzResearch.WordTrace]
  refine ⟨248375306122116560094501377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165583537414744373396334251 248375306122116560094501377)
  ·
    refine ⟨186281479591587420070876033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248375306122116560094501377 186281479591587420070876033)
    ·
      refine ⟨139711109693690565053157025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186281479591587420070876033 139711109693690565053157025)
      ·
        refine ⟨104783332270267923789867769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139711109693690565053157025 104783332270267923789867769)
        ·
          refine ⟨78587499202700942842400827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104783332270267923789867769 78587499202700942842400827)
          ·
            refine ⟨117881248804051414263601241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78587499202700942842400827 117881248804051414263601241)
            ·
              refine ⟨88410936603038560697700931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117881248804051414263601241 88410936603038560697700931)
              ·
                refine ⟨132616404904557841046551397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88410936603038560697700931 132616404904557841046551397)
                ·
                  refine ⟨24865575919604595196228387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132616404904557841046551397 24865575919604595196228387)
                  ·
                    refine ⟨37298363879406892794342581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24865575919604595196228387 37298363879406892794342581)
                    ·
                      refine ⟨3496721613694396199469617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37298363879406892794342581 3496721613694396199469617)
                      ·
                        rfl

theorem cell23_6809841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_6809841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809841 prefixEnd_6809841 := by exact prefixLift 6809841
  have htrace : WordTrace (prefixWord ++ tailWord_6809841) baseStart_6809841 baseEnd_6809841 := by
    simpa [prefixWord, tailWord_6809841, baseEnd_6809841] using wordTrace_append hprefix tailTrace_6809841
  have hstable : (prefixWord ++ tailWord_6809841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809841).length < 2 ^ (prefixWord ++ tailWord_6809841).sum := by decide
  have hdescent : baseEnd_6809841 < baseStart_6809841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809855 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 4, 2, 2]
def baseStart_6809855 : Nat := 118140960795 + 6809855 * 2 ^ 59
def prefixEnd_6809855 : Nat := 4983230072969 + 3 ^ 40 * 6809855 * 2
def baseEnd_6809855 : Nat := 3496728802423559144694553

theorem tailTrace_6809855 : CollatzResearch.WordTrace tailWord_6809855 prefixEnd_6809855 3496728802423559144694553 := by
  unfold tailWord_6809855
  simp only [CollatzResearch.WordTrace]
  refine ⟨248375816744065840485511019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165583877829377226990340679 248375816744065840485511019)
  ·
    refine ⟨372563725116098760728266529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248375816744065840485511019 372563725116098760728266529)
    ·
      refine ⟨279422793837074070546199897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372563725116098760728266529 279422793837074070546199897)
      ·
        refine ⟨209567095377805552909649923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279422793837074070546199897 209567095377805552909649923)
        ·
          refine ⟨314350643066708329364474885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209567095377805552909649923 314350643066708329364474885)
          ·
            refine ⟨58940745575007811755839041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 314350643066708329364474885 58940745575007811755839041)
            ·
              refine ⟨44205559181255858816879281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58940745575007811755839041 44205559181255858816879281)
              ·
                refine ⟨33154169385941894112659461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44205559181255858816879281 33154169385941894112659461)
                ·
                  refine ⟨6216406759864105146123649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33154169385941894112659461 6216406759864105146123649)
                  ·
                    refine ⟨4662305069898078859592737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6216406759864105146123649 4662305069898078859592737)
                    ·
                      refine ⟨3496728802423559144694553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4662305069898078859592737 3496728802423559144694553)
                      ·
                        rfl

theorem cell23_6809855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 2, 2].length) (baseStart_6809855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809855 prefixEnd_6809855 := by exact prefixLift 6809855
  have htrace : WordTrace (prefixWord ++ tailWord_6809855) baseStart_6809855 baseEnd_6809855 := by
    simpa [prefixWord, tailWord_6809855, baseEnd_6809855] using wordTrace_append hprefix tailTrace_6809855
  have hstable : (prefixWord ++ tailWord_6809855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809855).length < 2 ^ (prefixWord ++ tailWord_6809855).sum := by decide
  have hdescent : baseEnd_6809855 < baseStart_6809855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809891 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 3, 7]
def baseStart_6809891 : Nat := 118140960795 + 6809891 * 2 ^ 59
def prefixEnd_6809891 : Nat := 4983230072969 + 3 ^ 40 * 6809891 * 2
def baseEnd_6809891 : Nat := 1165582429242373667948129

theorem tailTrace_6809891 : CollatzResearch.WordTrace tailWord_6809891 prefixEnd_6809891 1165582429242373667948129 := by
  unfold tailWord_6809891
  simp only [CollatzResearch.WordTrace]
  refine ⟨248377129771935418633821527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165584753181290279089214351 248377129771935418633821527)
  ·
    refine ⟨372565694657903127950732291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248377129771935418633821527 372565694657903127950732291)
    ·
      refine ⟨558848541986854691926098437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372565694657903127950732291 558848541986854691926098437)
      ·
        refine ⟨104784101622535254736143457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 558848541986854691926098437 104784101622535254736143457)
        ·
          refine ⟨78588076216901441052107593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104784101622535254736143457 78588076216901441052107593)
          ·
            refine ⟨58941057162676080789080695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78588076216901441052107593 58941057162676080789080695)
            ·
              refine ⟨88411585744014121183621043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58941057162676080789080695 88411585744014121183621043)
              ·
                refine ⟨132617378616021181775431565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88411585744014121183621043 132617378616021181775431565)
                ·
                  refine ⟨49731516981007943165786837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132617378616021181775431565 49731516981007943165786837)
                  ·
                    refine ⟨1165582429242373667948129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49731516981007943165786837 1165582429242373667948129)
                    ·
                      rfl

theorem cell23_6809891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 7].length) (baseStart_6809891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809891 prefixEnd_6809891 := by exact prefixLift 6809891
  have htrace : WordTrace (prefixWord ++ tailWord_6809891) baseStart_6809891 baseEnd_6809891 := by
    simpa [prefixWord, tailWord_6809891, baseEnd_6809891] using wordTrace_append hprefix tailTrace_6809891
  have hstable : (prefixWord ++ tailWord_6809891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809891).length < 2 ^ (prefixWord ++ tailWord_6809891).sum := by decide
  have hdescent : baseEnd_6809891 < baseStart_6809891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809928 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_6809928 : Nat := 118140960795 + 6809928 * 2 ^ 59
def prefixEnd_6809928 : Nat := 4983230072969 + 3 ^ 40 * 6809928 * 2
def baseEnd_6809928 : Nat := 3496766286511337359081717

theorem tailTrace_6809928 : CollatzResearch.WordTrace tailWord_6809928 prefixEnd_6809928 3496766286511337359081717 := by
  unfold tailWord_6809928
  simp only [CollatzResearch.WordTrace]
  refine ⟨124189239636400686976459219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165585652848534249301945625 124189239636400686976459219)
  ·
    refine ⟨186283859454601030464688829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124189239636400686976459219 186283859454601030464688829)
    ·
      refine ⟨69856447295475386424258311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186283859454601030464688829 69856447295475386424258311)
      ·
        refine ⟨104784670943213079636387467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69856447295475386424258311 104784670943213079636387467)
        ·
          refine ⟨157177006414819619454581201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104784670943213079636387467 157177006414819619454581201)
          ·
            refine ⟨117882754811114714590935901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157177006414819619454581201 117882754811114714590935901)
            ·
              refine ⟨44206033054168017971600963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117882754811114714590935901 44206033054168017971600963)
              ·
                refine ⟨66309049581252026957401445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44206033054168017971600963 66309049581252026957401445)
                ·
                  refine ⟨12432946796484755054512771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66309049581252026957401445 12432946796484755054512771)
                  ·
                    refine ⟨18649420194727132581769157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12432946796484755054512771 18649420194727132581769157)
                    ·
                      refine ⟨3496766286511337359081717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18649420194727132581769157 3496766286511337359081717)
                      ·
                        rfl

theorem cell23_6809928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_6809928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809928 prefixEnd_6809928 := by exact prefixLift 6809928
  have htrace : WordTrace (prefixWord ++ tailWord_6809928) baseStart_6809928 baseEnd_6809928 := by
    simpa [prefixWord, tailWord_6809928, baseEnd_6809928] using wordTrace_append hprefix tailTrace_6809928
  have hstable : (prefixWord ++ tailWord_6809928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809928).length < 2 ^ (prefixWord ++ tailWord_6809928).sum := by decide
  have hdescent : baseEnd_6809928 < baseStart_6809928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809931 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 5]
def baseStart_6809931 : Nat := 118140960795 + 6809931 * 2 ^ 59
def prefixEnd_6809931 : Nat := 4983230072969 + 3 ^ 40 * 6809931 * 2
def baseEnd_6809931 : Nat := 3496767826953300847344203

theorem tailTrace_6809931 : CollatzResearch.WordTrace tailWord_6809931 prefixEnd_6809931 3496767826953300847344203 := by
  unfold tailWord_6809931
  simp only [CollatzResearch.WordTrace]
  refine ⟨248378588691790505465277647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165585725794527003643518431 248378588691790505465277647)
  ·
    refine ⟨372567883037685758197916471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248378588691790505465277647 372567883037685758197916471)
    ·
      refine ⟨558851824556528637296874707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372567883037685758197916471 558851824556528637296874707)
      ·
        refine ⟨838277736834792955945312061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558851824556528637296874707 838277736834792955945312061)
        ·
          refine ⟨314354151313047358479492023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 838277736834792955945312061 314354151313047358479492023)
          ·
            refine ⟨471531226969571037719238035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314354151313047358479492023 471531226969571037719238035)
            ·
              refine ⟨707296840454356556578857053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471531226969571037719238035 707296840454356556578857053)
              ·
                refine ⟨265236315170383708717071395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 707296840454356556578857053 265236315170383708717071395)
                ·
                  refine ⟨397854472755575563075607093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265236315170383708717071395 397854472755575563075607093)
                  ·
                    refine ⟨37298856820835209038338165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 397854472755575563075607093 37298856820835209038338165)
                    ·
                      refine ⟨3496767826953300847344203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37298856820835209038338165 3496767826953300847344203)
                      ·
                        rfl

theorem cell23_6809931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 5].length) (baseStart_6809931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809931 prefixEnd_6809931 := by exact prefixLift 6809931
  have htrace : WordTrace (prefixWord ++ tailWord_6809931) baseStart_6809931 baseEnd_6809931 := by
    simpa [prefixWord, tailWord_6809931, baseEnd_6809931] using wordTrace_append hprefix tailTrace_6809931
  have hstable : (prefixWord ++ tailWord_6809931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809931).length < 2 ^ (prefixWord ++ tailWord_6809931).sum := by decide
  have hdescent : baseEnd_6809931 < baseStart_6809931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809962 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_6809962 : Nat := 118140960795 + 6809962 * 2 ^ 59
def prefixEnd_6809962 : Nat := 4983230072969 + 3 ^ 40 * 6809962 * 2
def baseEnd_6809962 : Nat := 3496783744853590226056561

theorem tailTrace_6809962 : CollatzResearch.WordTrace tailWord_6809962 prefixEnd_6809962 3496783744853590226056561 := by
  unfold tailWord_6809962
  simp only [CollatzResearch.WordTrace]
  refine ⟨62094929838669549439914035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165586479569785465173104093 62094929838669549439914035)
  ·
    refine ⟨93142394758004324159871053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62094929838669549439914035 93142394758004324159871053)
    ·
      refine ⟨34928398034251621559951645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93142394758004324159871053 34928398034251621559951645)
      ·
        refine ⟨13098149262844358084981867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34928398034251621559951645 13098149262844358084981867)
        ·
          refine ⟨19647223894266537127472801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13098149262844358084981867 19647223894266537127472801)
          ·
            refine ⟨14735417920699902845604601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19647223894266537127472801 14735417920699902845604601)
            ·
              refine ⟨11051563440524927134203451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14735417920699902845604601 11051563440524927134203451)
              ·
                refine ⟨16577345160787390701305177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11051563440524927134203451 16577345160787390701305177)
                ·
                  refine ⟨12433008870590543025978883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16577345160787390701305177 12433008870590543025978883)
                  ·
                    refine ⟨18649513305885814538968325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12433008870590543025978883 18649513305885814538968325)
                    ·
                      refine ⟨3496783744853590226056561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18649513305885814538968325 3496783744853590226056561)
                      ·
                        rfl

theorem cell23_6809962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_6809962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809962 prefixEnd_6809962 := by exact prefixLift 6809962
  have htrace : WordTrace (prefixWord ++ tailWord_6809962) baseStart_6809962 baseEnd_6809962 := by
    simpa [prefixWord, tailWord_6809962, baseEnd_6809962] using wordTrace_append hprefix tailTrace_6809962
  have hstable : (prefixWord ++ tailWord_6809962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809962).length < 2 ^ (prefixWord ++ tailWord_6809962).sum := by decide
  have hdescent : baseEnd_6809962 < baseStart_6809962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809985 : List Nat := [1, 2, 4, 3, 1, 1, 1, 4, 6]
def baseStart_6809985 : Nat := 118140960795 + 6809985 * 2 ^ 59
def prefixEnd_6809985 : Nat := 4983230072969 + 3 ^ 40 * 6809985 * 2
def baseEnd_6809985 : Nat := 388532839434293737340995

theorem tailTrace_6809985 : CollatzResearch.WordTrace tailWord_6809985 prefixEnd_6809985 388532839434293737340995 := by
  unfold tailWord_6809985
  simp only [CollatzResearch.WordTrace]
  refine ⟨248380558233594872687743409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165587038822396581791828939 248380558233594872687743409)
  ·
    refine ⟨186285418675196154515807557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248380558233594872687743409 186285418675196154515807557)
    ·
      refine ⟨34928516001599278971713917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186285418675196154515807557 34928516001599278971713917)
      ·
        refine ⟨13098193500599729614392719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34928516001599278971713917 13098193500599729614392719)
        ·
          refine ⟨19647290250899594421589079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13098193500599729614392719 19647290250899594421589079)
          ·
            refine ⟨29470935376349391632383619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19647290250899594421589079 29470935376349391632383619)
            ·
              refine ⟨44206403064524087448575429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29470935376349391632383619 44206403064524087448575429)
              ·
                refine ⟨8288700574598266396607893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44206403064524087448575429 8288700574598266396607893)
                ·
                  refine ⟨388532839434293737340995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8288700574598266396607893 388532839434293737340995)
                  ·
                    rfl

theorem cell23_6809985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 6].length) (baseStart_6809985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809985 prefixEnd_6809985 := by exact prefixLift 6809985
  have htrace : WordTrace (prefixWord ++ tailWord_6809985) baseStart_6809985 baseEnd_6809985 := by
    simpa [prefixWord, tailWord_6809985, baseEnd_6809985] using wordTrace_append hprefix tailTrace_6809985
  have hstable : (prefixWord ++ tailWord_6809985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809985).length < 2 ^ (prefixWord ++ tailWord_6809985).sum := by decide
  have hdescent : baseEnd_6809985 < baseStart_6809985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6809988 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_6809988 : Nat := 118140960795 + 6809988 * 2 ^ 59
def prefixEnd_6809988 : Nat := 4983230072969 + 3 ^ 40 * 6809988 * 2
def baseEnd_6809988 : Nat := 3496797095350607124331441

theorem tailTrace_6809988 : CollatzResearch.WordTrace tailWord_6809988 prefixEnd_6809988 3496797095350607124331441 := by
  unfold tailWord_6809988
  simp only [CollatzResearch.WordTrace]
  refine ⟨124190333826292002100051309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165587111768389336133401745 124190333826292002100051309)
  ·
    refine ⟨46571375184859500787519241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124190333826292002100051309 46571375184859500787519241)
    ·
      refine ⟨34928531388644625590639431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46571375184859500787519241 34928531388644625590639431)
      ·
        refine ⟨52392797082966938385959147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34928531388644625590639431 52392797082966938385959147)
        ·
          refine ⟨78589195624450407578938721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52392797082966938385959147 78589195624450407578938721)
          ·
            refine ⟨58941896718337805684204041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78589195624450407578938721 58941896718337805684204041)
            ·
              refine ⟨44206422538753354263153031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58941896718337805684204041 44206422538753354263153031)
              ·
                refine ⟨66309633808130031394729547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44206422538753354263153031 66309633808130031394729547)
                ·
                  refine ⟨99464450712195047092094321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66309633808130031394729547 99464450712195047092094321)
                  ·
                    refine ⟨74598338034146285319070741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99464450712195047092094321 74598338034146285319070741)
                    ·
                      refine ⟨3496797095350607124331441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74598338034146285319070741 3496797095350607124331441)
                      ·
                        rfl

theorem cell23_6809988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_6809988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6809988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6809988 prefixEnd_6809988 := by exact prefixLift 6809988
  have htrace : WordTrace (prefixWord ++ tailWord_6809988) baseStart_6809988 baseEnd_6809988 := by
    simpa [prefixWord, tailWord_6809988, baseEnd_6809988] using wordTrace_append hprefix tailTrace_6809988
  have hstable : (prefixWord ++ tailWord_6809988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6809988).length < 2 ^ (prefixWord ++ tailWord_6809988).sum := by decide
  have hdescent : baseEnd_6809988 < baseStart_6809988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6809988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810005 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 1, 5, 2]
def baseStart_6810005 : Nat := 118140960795 + 6810005 * 2 ^ 59
def prefixEnd_6810005 : Nat := 4983230072969 + 3 ^ 40 * 6810005 * 2
def baseEnd_6810005 : Nat := 3496805824521733557818863

theorem tailTrace_6810005 : CollatzResearch.WordTrace tailWord_6810005 prefixEnd_6810005 3496805824521733557818863 := by
  unfold tailWord_6810005
  simp only [CollatzResearch.WordTrace]
  refine ⟨248381287693522416103471469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165587525129014944068980979 248381287693522416103471469)
  ·
    refine ⟨93142982885070906038801801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248381287693522416103471469 93142982885070906038801801)
    ·
      refine ⟨69857237163803179529101351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93142982885070906038801801 69857237163803179529101351)
      ·
        refine ⟨104785855745704769293652027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69857237163803179529101351 104785855745704769293652027)
        ·
          refine ⟨157178783618557153940478041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104785855745704769293652027 157178783618557153940478041)
          ·
            refine ⟨117884087713917865455358531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157178783618557153940478041 117884087713917865455358531)
            ·
              refine ⟨176826131570876798183037797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117884087713917865455358531 176826131570876798183037797)
              ·
                refine ⟨33154899669539399659319587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176826131570876798183037797 33154899669539399659319587)
                ·
                  refine ⟨49732349504309099488979381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33154899669539399659319587 49732349504309099488979381)
                  ·
                    refine ⟨4662407766028978077091817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49732349504309099488979381 4662407766028978077091817)
                    ·
                      refine ⟨3496805824521733557818863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4662407766028978077091817 3496805824521733557818863)
                      ·
                        rfl

theorem cell23_6810005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_6810005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810005 prefixEnd_6810005 := by exact prefixLift 6810005
  have htrace : WordTrace (prefixWord ++ tailWord_6810005) baseStart_6810005 baseEnd_6810005 := by
    simpa [prefixWord, tailWord_6810005, baseEnd_6810005] using wordTrace_append hprefix tailTrace_6810005
  have hstable : (prefixWord ++ tailWord_6810005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810005).length < 2 ^ (prefixWord ++ tailWord_6810005).sum := by decide
  have hdescent : baseEnd_6810005 < baseStart_6810005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810015 : List Nat := [1, 1, 2, 5, 1, 1, 2, 4, 1, 5]
def baseStart_6810015 : Nat := 118140960795 + 6810015 * 2 ^ 59
def prefixEnd_6810015 : Nat := 4983230072969 + 3 ^ 40 * 6810015 * 2
def baseEnd_6810015 : Nat := 1165603653109426172897939

theorem tailTrace_6810015 : CollatzResearch.WordTrace tailWord_6810015 prefixEnd_6810015 1165603653109426172897939 := by
  unfold tailWord_6810015
  simp only [CollatzResearch.WordTrace]
  refine ⟨248381652423486187811335499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165587768282324125207556999 248381652423486187811335499)
  ·
    refine ⟨372572478635229281717003249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248381652423486187811335499 372572478635229281717003249)
    ·
      refine ⟨279429358976421961287752437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372572478635229281717003249 279429358976421961287752437)
      ·
        refine ⟨26196502404039558870726791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279429358976421961287752437 26196502404039558870726791)
        ·
          refine ⟨39294753606059338306090187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26196502404039558870726791 39294753606059338306090187)
          ·
            refine ⟨58942130409089007459135281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39294753606059338306090187 58942130409089007459135281)
            ·
              refine ⟨44206597806816755594351461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58942130409089007459135281 44206597806816755594351461)
              ·
                refine ⟨8288737088778141673940899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44206597806816755594351461 8288737088778141673940899)
                ·
                  refine ⟨12433105633167212510911349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8288737088778141673940899 12433105633167212510911349)
                  ·
                    refine ⟨1165603653109426172897939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12433105633167212510911349 1165603653109426172897939)
                    ·
                      rfl

theorem cell23_6810015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 5].length) (baseStart_6810015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810015 prefixEnd_6810015 := by exact prefixLift 6810015
  have htrace : WordTrace (prefixWord ++ tailWord_6810015) baseStart_6810015 baseEnd_6810015 := by
    simpa [prefixWord, tailWord_6810015, baseEnd_6810015] using wordTrace_append hprefix tailTrace_6810015
  have hstable : (prefixWord ++ tailWord_6810015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810015).length < 2 ^ (prefixWord ++ tailWord_6810015).sum := by decide
  have hdescent : baseEnd_6810015 < baseStart_6810015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810036 : List Nat := [2, 5, 2, 2, 1, 2, 1, 2, 6]
def baseStart_6810036 : Nat := 118140960795 + 6810036 * 2 ^ 59
def prefixEnd_6810036 : Nat := 4983230072969 + 3 ^ 40 * 6810036 * 2
def baseEnd_6810036 : Nat := 388535749158002548503469

theorem tailTrace_6810036 : CollatzResearch.WordTrace tailWord_6810036 prefixEnd_6810036 388535749158002548503469 := by
  unfold tailWord_6810036
  simp only [CollatzResearch.WordTrace]
  refine ⟨124191209178205054198924981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165588278904273405598566641 124191209178205054198924981)
  ·
    refine ⟨11642925860456723831149217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124191209178205054198924981 11642925860456723831149217)
    ·
      refine ⟨8732194395342542873361913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11642925860456723831149217 8732194395342542873361913)
      ·
        refine ⟨6549145796506907155021435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8732194395342542873361913 6549145796506907155021435)
        ·
          refine ⟨9823718694760360732532153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6549145796506907155021435 9823718694760360732532153)
          ·
            refine ⟨7367789021070270549399115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9823718694760360732532153 7367789021070270549399115)
            ·
              refine ⟨11051683531605405824098673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7367789021070270549399115 11051683531605405824098673)
              ·
                refine ⟨8288762648704054368074005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11051683531605405824098673 8288762648704054368074005)
                ·
                  refine ⟨388535749158002548503469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8288762648704054368074005 388535749158002548503469)
                  ·
                    rfl

theorem cell23_6810036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_6810036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810036 prefixEnd_6810036 := by exact prefixLift 6810036
  have htrace : WordTrace (prefixWord ++ tailWord_6810036) baseStart_6810036 baseEnd_6810036 := by
    simpa [prefixWord, tailWord_6810036, baseEnd_6810036] using wordTrace_append hprefix tailTrace_6810036
  have hstable : (prefixWord ++ tailWord_6810036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810036).length < 2 ^ (prefixWord ++ tailWord_6810036).sum := by decide
  have hdescent : baseEnd_6810036 < baseStart_6810036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810048 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 6]
def baseStart_6810048 : Nat := 118140960795 + 6810048 * 2 ^ 59
def prefixEnd_6810048 : Nat := 4983230072969 + 3 ^ 40 * 6810048 * 2
def baseEnd_6810048 : Nat := 3496827904189876889581165

theorem tailTrace_6810048 : CollatzResearch.WordTrace tailWord_6810048 prefixEnd_6810048 3496827904189876889581165 := by
  unfold tailWord_6810048
  simp only [CollatzResearch.WordTrace]
  refine ⟨124191428016183317223643399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165588570688244422964857865 124191428016183317223643399)
  ·
    refine ⟨186287142024274975835465099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124191428016183317223643399 186287142024274975835465099)
    ·
      refine ⟨279430713036412463753197649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186287142024274975835465099 279430713036412463753197649)
      ·
        refine ⟨209573034777309347814898237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279430713036412463753197649 209573034777309347814898237)
        ·
          refine ⟨78589888041491005430586839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209573034777309347814898237 78589888041491005430586839)
          ·
            refine ⟨117884832062236508145880259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78589888041491005430586839 117884832062236508145880259)
            ·
              refine ⟨176827248093354762218820389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117884832062236508145880259 176827248093354762218820389)
              ·
                refine ⟨33155109017504017916028823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176827248093354762218820389 33155109017504017916028823)
                ·
                  refine ⟨49732663526256026874043235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33155109017504017916028823 49732663526256026874043235)
                  ·
                    refine ⟨74598995289384040311064853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49732663526256026874043235 74598995289384040311064853)
                    ·
                      refine ⟨3496827904189876889581165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74598995289384040311064853 3496827904189876889581165)
                      ·
                        rfl

theorem cell23_6810048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_6810048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810048 prefixEnd_6810048 := by exact prefixLift 6810048
  have htrace : WordTrace (prefixWord ++ tailWord_6810048) baseStart_6810048 baseEnd_6810048 := by
    simpa [prefixWord, tailWord_6810048, baseEnd_6810048] using wordTrace_append hprefix tailTrace_6810048
  have hstable : (prefixWord ++ tailWord_6810048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810048).length < 2 ^ (prefixWord ++ tailWord_6810048).sum := by decide
  have hdescent : baseEnd_6810048 < baseStart_6810048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810055 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_6810055 : Nat := 118140960795 + 6810055 * 2 ^ 59
def prefixEnd_6810055 : Nat := 4983230072969 + 3 ^ 40 * 6810055 * 2
def baseEnd_6810055 : Nat := 3496831498554458362193633

theorem tailTrace_6810055 : CollatzResearch.WordTrace tailWord_6810055 prefixEnd_6810055 3496831498554458362193633 := by
  unfold tailWord_6810055
  simp only [CollatzResearch.WordTrace]
  refine ⟨248383111343341274642791619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165588740895560849761861079 248383111343341274642791619)
  ·
    refine ⟨372574667015011911964187429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248383111343341274642791619 372574667015011911964187429)
    ·
      refine ⟨69857750065314733493285143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372574667015011911964187429 69857750065314733493285143)
      ·
        refine ⟨104786625097972100239927715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69857750065314733493285143 104786625097972100239927715)
        ·
          refine ⟨157179937646958150359891573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104786625097972100239927715 157179937646958150359891573)
          ·
            refine ⟨14735619154402326596239835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157179937646958150359891573 14735619154402326596239835)
            ·
              refine ⟨22103428731603489894359753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14735619154402326596239835 22103428731603489894359753)
              ·
                refine ⟨16577571548702617420769815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22103428731603489894359753 16577571548702617420769815)
                ·
                  refine ⟨24866357323053926131154723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16577571548702617420769815 24866357323053926131154723)
                  ·
                    refine ⟨37299535984580889196732085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24866357323053926131154723 37299535984580889196732085)
                    ·
                      refine ⟨3496831498554458362193633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37299535984580889196732085 3496831498554458362193633)
                      ·
                        rfl

theorem cell23_6810055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_6810055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810055 prefixEnd_6810055 := by exact prefixLift 6810055
  have htrace : WordTrace (prefixWord ++ tailWord_6810055) baseStart_6810055 baseEnd_6810055 := by
    simpa [prefixWord, tailWord_6810055, baseEnd_6810055] using wordTrace_append hprefix tailTrace_6810055
  have hstable : (prefixWord ++ tailWord_6810055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810055).length < 2 ^ (prefixWord ++ tailWord_6810055).sum := by decide
  have hdescent : baseEnd_6810055 < baseStart_6810055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810058 : List Nat := [3, 1, 2, 1, 2, 2, 2, 10]
def baseStart_6810058 : Nat := 118140960795 + 6810058 * 2 ^ 59
def prefixEnd_6810058 : Nat := 4983230072969 + 3 ^ 40 * 6810058 * 2
def baseEnd_6810058 : Nat := 129512334777645253720597

theorem tailTrace_6810058 : CollatzResearch.WordTrace tailWord_6810058 prefixEnd_6810058 129512334777645253720597 := by
  unfold tailWord_6810058
  simp only [CollatzResearch.WordTrace]
  refine ⟨62095805190582601538787707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165588813841553604103433885 62095805190582601538787707)
  ·
    refine ⟨93143707785873902308181561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62095805190582601538787707 93143707785873902308181561)
    ·
      refine ⟨69857780839405426731136171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93143707785873902308181561 69857780839405426731136171)
      ·
        refine ⟨104786671259108140096704257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69857780839405426731136171 104786671259108140096704257)
        ·
          refine ⟨78590003444331105072528193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104786671259108140096704257 78590003444331105072528193)
          ·
            refine ⟨58942502583248328804396145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78590003444331105072528193 58942502583248328804396145)
            ·
              refine ⟨44206876937436246603297109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58942502583248328804396145 44206876937436246603297109)
              ·
                refine ⟨129512334777645253720597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44206876937436246603297109 129512334777645253720597)
                ·
                  rfl

theorem cell23_6810058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 10].length) (baseStart_6810058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810058 prefixEnd_6810058 := by exact prefixLift 6810058
  have htrace : WordTrace (prefixWord ++ tailWord_6810058) baseStart_6810058 baseEnd_6810058 := by
    simpa [prefixWord, tailWord_6810058, baseEnd_6810058] using wordTrace_append hprefix tailTrace_6810058
  have hstable : (prefixWord ++ tailWord_6810058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810058).length < 2 ^ (prefixWord ++ tailWord_6810058).sum := by decide
  have hdescent : baseEnd_6810058 < baseStart_6810058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810069 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 3, 2, 2]
def baseStart_6810069 : Nat := 118140960795 + 6810069 * 2 ^ 59
def prefixEnd_6810069 : Nat := 4983230072969 + 3 ^ 40 * 6810069 * 2
def baseEnd_6810069 : Nat := 3496838687283621307418569

theorem tailTrace_6810069 : CollatzResearch.WordTrace tailWord_6810069 prefixEnd_6810069 3496838687283621307418569 := by
  unfold tailWord_6810069
  simp only [CollatzResearch.WordTrace]
  refine ⟨248383621965290555033801261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165589081310193703355867507 248383621965290555033801261)
  ·
    refine ⟨93143858236983958137675473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248383621965290555033801261 93143858236983958137675473)
    ·
      refine ⟨69857893677737968603256605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93143858236983958137675473 69857893677737968603256605)
      ·
        refine ⟨26196710129151738226221227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69857893677737968603256605 26196710129151738226221227)
        ·
          refine ⟨39295065193727607339331841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26196710129151738226221227 39295065193727607339331841)
          ·
            refine ⟨29471298895295705504498881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39295065193727607339331841 29471298895295705504498881)
            ·
              refine ⟨22103474171471779128374161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29471298895295705504498881 22103474171471779128374161)
              ·
                refine ⟨16577605628603834346280621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22103474171471779128374161 16577605628603834346280621)
                ·
                  refine ⟨6216602110726437879855233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16577605628603834346280621 6216602110726437879855233)
                  ·
                    refine ⟨4662451583044828409891425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6216602110726437879855233 4662451583044828409891425)
                    ·
                      refine ⟨3496838687283621307418569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4662451583044828409891425 3496838687283621307418569)
                      ·
                        rfl

theorem cell23_6810069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_6810069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810069 prefixEnd_6810069 := by exact prefixLift 6810069
  have htrace : WordTrace (prefixWord ++ tailWord_6810069) baseStart_6810069 baseEnd_6810069 := by
    simpa [prefixWord, tailWord_6810069, baseEnd_6810069] using wordTrace_append hprefix tailTrace_6810069
  have hstable : (prefixWord ++ tailWord_6810069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810069).length < 2 ^ (prefixWord ++ tailWord_6810069).sum := by decide
  have hdescent : baseEnd_6810069 < baseStart_6810069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810145 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_6810145 : Nat := 118140960795 + 6810145 * 2 ^ 59
def prefixEnd_6810145 : Nat := 4983230072969 + 3 ^ 40 * 6810145 * 2
def baseEnd_6810145 : Nat := 3496877711813363010068219

theorem tailTrace_6810145 : CollatzResearch.WordTrace tailWord_6810145 prefixEnd_6810145 3496877711813363010068219 := by
  unfold tailWord_6810145
  simp only [CollatzResearch.WordTrace]
  refine ⟨248386393913015220013567889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165590929275343480009045259 248386393913015220013567889)
  ·
    refine ⟨186289795434761415010175917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248386393913015220013567889 186289795434761415010175917)
    ·
      refine ⟨69858673288035530628815969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186289795434761415010175917 69858673288035530628815969)
      ·
        refine ⟨52394004966026647971611977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69858673288035530628815969 52394004966026647971611977)
        ·
          refine ⟨39295503724519985978708983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52394004966026647971611977 39295503724519985978708983)
          ·
            refine ⟨58943255586779978968063475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39295503724519985978708983 58943255586779978968063475)
            ·
              refine ⟨88414883380169968452095213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58943255586779978968063475 88414883380169968452095213)
              ·
                refine ⟨33155581267563738169535705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88414883380169968452095213 33155581267563738169535705)
                ·
                  refine ⟨24866685950672803627151779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33155581267563738169535705 24866685950672803627151779)
                  ·
                    refine ⟨37300028926009205440727669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24866685950672803627151779 37300028926009205440727669)
                    ·
                      refine ⟨3496877711813363010068219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37300028926009205440727669 3496877711813363010068219)
                      ·
                        rfl

theorem cell23_6810145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_6810145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810145 prefixEnd_6810145 := by exact prefixLift 6810145
  have htrace : WordTrace (prefixWord ++ tailWord_6810145) baseStart_6810145 baseEnd_6810145 := by
    simpa [prefixWord, tailWord_6810145, baseEnd_6810145] using wordTrace_append hprefix tailTrace_6810145
  have hstable : (prefixWord ++ tailWord_6810145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810145).length < 2 ^ (prefixWord ++ tailWord_6810145).sum := by decide
  have hdescent : baseEnd_6810145 < baseStart_6810145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810165 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 7]
def baseStart_6810165 : Nat := 118140960795 + 6810165 * 2 ^ 59
def prefixEnd_6810165 : Nat := 4983230072969 + 3 ^ 40 * 6810165 * 2
def baseEnd_6810165 : Nat := 388543109047383659090903

theorem tailTrace_6810165 : CollatzResearch.WordTrace tailWord_6810165 prefixEnd_6810165 388543109047383659090903 := by
  unfold tailWord_6810165
  simp only [CollatzResearch.WordTrace]
  refine ⟨248387123372942763429295949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165591415581961842286197299 248387123372942763429295949)
  ·
    refine ⟨93145171264853536285985981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248387123372942763429295949 93145171264853536285985981)
    ·
      refine ⟨34929439224320076107244743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93145171264853536285985981 34929439224320076107244743)
      ·
        refine ⟨52394158836480114160867115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34929439224320076107244743 52394158836480114160867115)
        ·
          refine ⟨78591238254720171241300673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52394158836480114160867115 78591238254720171241300673)
          ·
            refine ⟨58943428691040128430975505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78591238254720171241300673 58943428691040128430975505)
            ·
              refine ⟨44207571518280096323231629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58943428691040128430975505 44207571518280096323231629)
              ·
                refine ⟨16577839319355036121211861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44207571518280096323231629 16577839319355036121211861)
                ·
                  refine ⟨388543109047383659090903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16577839319355036121211861 388543109047383659090903)
                  ·
                    rfl

theorem cell23_6810165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 7].length) (baseStart_6810165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810165 prefixEnd_6810165 := by exact prefixLift 6810165
  have htrace : WordTrace (prefixWord ++ tailWord_6810165) baseStart_6810165 baseEnd_6810165 := by
    simpa [prefixWord, tailWord_6810165, baseEnd_6810165] using wordTrace_append hprefix tailTrace_6810165
  have hstable : (prefixWord ++ tailWord_6810165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810165).length < 2 ^ (prefixWord ++ tailWord_6810165).sum := by decide
  have hdescent : baseEnd_6810165 < baseStart_6810165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810172 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_6810172 : Nat := 118140960795 + 6810172 * 2 ^ 59
def prefixEnd_6810172 : Nat := 4983230072969 + 3 ^ 40 * 6810172 * 2
def baseEnd_6810172 : Nat := 3496891575791034404430595

theorem tailTrace_6810172 : CollatzResearch.WordTrace tailWord_6810172 prefixEnd_6810172 3496891575791034404430595 := by
  unfold tailWord_6810172
  simp only [CollatzResearch.WordTrace]
  refine ⟨124193689341958701812400385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165591585789278269083200513 124193689341958701812400385)
  ·
    refine ⟨93145267006469026359300289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124193689341958701812400385 93145267006469026359300289)
    ·
      refine ⟨69858950254851769769475217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93145267006469026359300289 69858950254851769769475217)
      ·
        refine ⟨52394212691138827327106413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69858950254851769769475217 52394212691138827327106413)
        ·
          refine ⟨19647829759177060247664905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52394212691138827327106413 19647829759177060247664905)
          ·
            refine ⟨14735872319382795185748679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19647829759177060247664905 14735872319382795185748679)
            ·
              refine ⟨22103808479074192778623019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14735872319382795185748679 22103808479074192778623019)
              ·
                refine ⟨33155712718611289167934529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22103808479074192778623019 33155712718611289167934529)
                ·
                  refine ⟨24866784538958466875950897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33155712718611289167934529 24866784538958466875950897)
                  ·
                    refine ⟨18650088404218850156963173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24866784538958466875950897 18650088404218850156963173)
                    ·
                      refine ⟨3496891575791034404430595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18650088404218850156963173 3496891575791034404430595)
                      ·
                        rfl

theorem cell23_6810172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_6810172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810172 prefixEnd_6810172 := by exact prefixLift 6810172
  have htrace : WordTrace (prefixWord ++ tailWord_6810172) baseStart_6810172 baseEnd_6810172 := by
    simpa [prefixWord, tailWord_6810172, baseEnd_6810172] using wordTrace_append hprefix tailTrace_6810172
  have hstable : (prefixWord ++ tailWord_6810172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810172).length < 2 ^ (prefixWord ++ tailWord_6810172).sum := by decide
  have hdescent : baseEnd_6810172 < baseStart_6810172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810266 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4]
def baseStart_6810266 : Nat := 118140960795 + 6810266 * 2 ^ 59
def prefixEnd_6810266 : Nat := 4983230072969 + 3 ^ 40 * 6810266 * 2
def baseEnd_6810266 : Nat := 3496939842972557036655163

theorem tailTrace_6810266 : CollatzResearch.WordTrace tailWord_6810266 prefixEnd_6810266 3496939842972557036655163 := by
  unfold tailWord_6810266
  simp only [CollatzResearch.WordTrace]
  refine ⟨62097701786394214419680663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165593871430384571785815101 62097701786394214419680663)
  ·
    refine ⟨93146552679591321629520995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62097701786394214419680663 93146552679591321629520995)
    ·
      refine ⟨139719829019386982444281493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93146552679591321629520995 139719829019386982444281493)
      ·
        refine ⟨6549366985283764802075695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139719829019386982444281493 6549366985283764802075695)
        ·
          refine ⟨9824050477925647203113543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6549366985283764802075695 9824050477925647203113543)
          ·
            refine ⟨14736075716888470804670315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9824050477925647203113543 14736075716888470804670315)
            ·
              refine ⟨22104113575332706207005473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14736075716888470804670315 22104113575332706207005473)
              ·
                refine ⟨16578085181499529655254105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22104113575332706207005473 16578085181499529655254105)
                ·
                  refine ⟨12433563886124647241440579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16578085181499529655254105 12433563886124647241440579)
                  ·
                    refine ⟨18650345829186970862160869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12433563886124647241440579 18650345829186970862160869)
                    ·
                      refine ⟨3496939842972557036655163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18650345829186970862160869 3496939842972557036655163)
                      ·
                        rfl

theorem cell23_6810266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_6810266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810266 prefixEnd_6810266 := by exact prefixLift 6810266
  have htrace : WordTrace (prefixWord ++ tailWord_6810266) baseStart_6810266 baseEnd_6810266 := by
    simpa [prefixWord, tailWord_6810266, baseEnd_6810266] using wordTrace_append hprefix tailTrace_6810266
  have hstable : (prefixWord ++ tailWord_6810266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810266).length < 2 ^ (prefixWord ++ tailWord_6810266).sum := by decide
  have hdescent : baseEnd_6810266 < baseStart_6810266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810275 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 6]
def baseStart_6810275 : Nat := 118140960795 + 6810275 * 2 ^ 59
def prefixEnd_6810275 : Nat := 4983230072969 + 3 ^ 40 * 6810275 * 2
def baseEnd_6810275 : Nat := 3496944464298447501442621

theorem tailTrace_6810275 : CollatzResearch.WordTrace tailWord_6810275 prefixEnd_6810275 3496944464298447501442621 := by
  unfold tailWord_6810275
  simp only [CollatzResearch.WordTrace]
  refine ⟨248391135402544252215800279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165594090268362834810533519 248391135402544252215800279)
  ·
    refine ⟨372586703103816378323700419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248391135402544252215800279 372586703103816378323700419)
    ·
      refine ⟨558880054655724567485550629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372586703103816378323700419 558880054655724567485550629)
      ·
        refine ⟨104790010247948356403540743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 558880054655724567485550629 104790010247948356403540743)
        ·
          refine ⟨157185015371922534605311115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104790010247948356403540743 157185015371922534605311115)
          ·
            refine ⟨235777523057883801907966673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157185015371922534605311115 235777523057883801907966673)
            ·
              refine ⟨176833142293412851430975005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235777523057883801907966673 176833142293412851430975005)
              ·
                refine ⟨66312428360029819286615627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176833142293412851430975005 66312428360029819286615627)
                ·
                  refine ⟨99468642540044728929923441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66312428360029819286615627 99468642540044728929923441)
                  ·
                    refine ⟨74601481905033546697442581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99468642540044728929923441 74601481905033546697442581)
                    ·
                      refine ⟨3496944464298447501442621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74601481905033546697442581 3496944464298447501442621)
                      ·
                        rfl

theorem cell23_6810275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_6810275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810275 prefixEnd_6810275 := by exact prefixLift 6810275
  have htrace : WordTrace (prefixWord ++ tailWord_6810275) baseStart_6810275 baseEnd_6810275 := by
    simpa [prefixWord, tailWord_6810275, baseEnd_6810275] using wordTrace_append hprefix tailTrace_6810275
  have hstable : (prefixWord ++ tailWord_6810275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810275).length < 2 ^ (prefixWord ++ tailWord_6810275).sum := by decide
  have hdescent : baseEnd_6810275 < baseStart_6810275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810339 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 4]
def baseStart_6810339 : Nat := 118140960795 + 6810339 * 2 ^ 59
def prefixEnd_6810339 : Nat := 4983230072969 + 3 ^ 40 * 6810339 * 2
def baseEnd_6810339 : Nat := 3496977327060335251042327

theorem tailTrace_6810339 : CollatzResearch.WordTrace tailWord_6810339 prefixEnd_6810339 3496977327060335251042327 := by
  unfold tailWord_6810339
  simp only [CollatzResearch.WordTrace]
  refine ⟨248393469674312391146130071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165595646449541594097420047 248393469674312391146130071)
  ·
    refine ⟨372590204511468586719195107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248393469674312391146130071 372590204511468586719195107)
    ·
      refine ⟨558885306767202880078792661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372590204511468586719195107 558885306767202880078792661)
      ·
        refine ⟨13098874377356317501846703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 558885306767202880078792661 13098874377356317501846703)
        ·
          refine ⟨19648311566034476252770055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13098874377356317501846703 19648311566034476252770055)
          ·
            refine ⟨29472467349051714379155083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19648311566034476252770055 29472467349051714379155083)
            ·
              refine ⟨44208701023577571568732625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29472467349051714379155083 44208701023577571568732625)
              ·
                refine ⟨33156525767683178676549469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44208701023577571568732625 33156525767683178676549469)
                ·
                  refine ⟨12433697162881192003706051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33156525767683178676549469 12433697162881192003706051)
                  ·
                    refine ⟨18650545744321788005559077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12433697162881192003706051 18650545744321788005559077)
                    ·
                      refine ⟨3496977327060335251042327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18650545744321788005559077 3496977327060335251042327)
                      ·
                        rfl

theorem cell23_6810339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_6810339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810339 prefixEnd_6810339 := by exact prefixLift 6810339
  have htrace : WordTrace (prefixWord ++ tailWord_6810339) baseStart_6810339 baseEnd_6810339 := by
    simpa [prefixWord, tailWord_6810339, baseEnd_6810339] using wordTrace_append hprefix tailTrace_6810339
  have hstable : (prefixWord ++ tailWord_6810339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810339).length < 2 ^ (prefixWord ++ tailWord_6810339).sum := by decide
  have hdescent : baseEnd_6810339 < baseStart_6810339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810349 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_6810349 : Nat := 118140960795 + 6810349 * 2 ^ 59
def prefixEnd_6810349 : Nat := 4983230072969 + 3 ^ 40 * 6810349 * 2
def baseEnd_6810349 : Nat := 1165660820622293403972427

theorem tailTrace_6810349 : CollatzResearch.WordTrace tailWord_6810349 prefixEnd_6810349 1165660820622293403972427 := by
  unfold tailWord_6810349
  simp only [CollatzResearch.WordTrace]
  refine ⟨248393834404276162853994101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165595889602850775235996067 248393834404276162853994101)
  ·
    refine ⟨23286921975400890267561947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 248393834404276162853994101 23286921975400890267561947)
    ·
      refine ⟨34930382963101335401342921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23286921975400890267561947 34930382963101335401342921)
      ·
        refine ⟨26197787222326001551007191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34930382963101335401342921 26197787222326001551007191)
        ·
          refine ⟨39296680833489002326510787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26197787222326001551007191 39296680833489002326510787)
          ·
            refine ⟨58945021250233503489766181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39296680833489002326510787 58945021250233503489766181)
            ·
              refine ⟨11052191484418781904331159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58945021250233503489766181 11052191484418781904331159)
              ·
                refine ⟨16578287226628172856496739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11052191484418781904331159 16578287226628172856496739)
                ·
                  refine ⟨24867430839942259284745109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16578287226628172856496739 24867430839942259284745109)
                  ·
                    refine ⟨1165660820622293403972427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24867430839942259284745109 1165660820622293403972427)
                    ·
                      rfl

theorem cell23_6810349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_6810349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810349 prefixEnd_6810349 := by exact prefixLift 6810349
  have htrace : WordTrace (prefixWord ++ tailWord_6810349) baseStart_6810349 baseEnd_6810349 := by
    simpa [prefixWord, tailWord_6810349, baseEnd_6810349] using wordTrace_append hprefix tailTrace_6810349
  have hstable : (prefixWord ++ tailWord_6810349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810349).length < 2 ^ (prefixWord ++ tailWord_6810349).sum := by decide
  have hdescent : baseEnd_6810349 < baseStart_6810349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810359 : List Nat := [1, 1, 3, 1, 1, 1, 3, 6, 1, 2, 3]
def baseStart_6810359 : Nat := 118140960795 + 6810359 * 2 ^ 59
def prefixEnd_6810359 : Nat := 4983230072969 + 3 ^ 40 * 6810359 * 2
def baseEnd_6810359 : Nat := 3496987596673425172792235

theorem tailTrace_6810359 : CollatzResearch.WordTrace tailWord_6810359 prefixEnd_6810359 3496987596673425172792235 := by
  unfold tailWord_6810359
  simp only [CollatzResearch.WordTrace]
  refine ⟨248394199134239934561858131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165596132756159956374572087 248394199134239934561858131)
  ·
    refine ⟨372591298701359901842787197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248394199134239934561858131 372591298701359901842787197)
    ·
      refine ⟨139721737013009963191045199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372591298701359901842787197 139721737013009963191045199)
      ·
        refine ⟨209582605519514944786567799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139721737013009963191045199 209582605519514944786567799)
        ·
          refine ⟨314373908279272417179851699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209582605519514944786567799 314373908279272417179851699)
          ·
            refine ⟨471560862418908625769777549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314373908279272417179851699 471560862418908625769777549)
            ·
              refine ⟨176835323407090734663666581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 471560862418908625769777549 176835323407090734663666581)
              ·
                refine ⟨8289155784707378187359371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 176835323407090734663666581 8289155784707378187359371)
                ·
                  refine ⟨12433733677061067281039057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8289155784707378187359371 12433733677061067281039057)
                  ·
                    refine ⟨9325300257795800460779293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12433733677061067281039057 9325300257795800460779293)
                    ·
                      refine ⟨3496987596673425172792235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9325300257795800460779293 3496987596673425172792235)
                      ·
                        rfl

theorem cell23_6810359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_6810359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810359 prefixEnd_6810359 := by exact prefixLift 6810359
  have htrace : WordTrace (prefixWord ++ tailWord_6810359) baseStart_6810359 baseEnd_6810359 := by
    simpa [prefixWord, tailWord_6810359, baseEnd_6810359] using wordTrace_append hprefix tailTrace_6810359
  have hstable : (prefixWord ++ tailWord_6810359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810359).length < 2 ^ (prefixWord ++ tailWord_6810359).sum := by decide
  have hdescent : baseEnd_6810359 < baseStart_6810359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810376 : List Nat := [2, 1, 3, 2, 2, 3, 1, 3, 1, 2, 3]
def baseStart_6810376 : Nat := 118140960795 + 6810376 * 2 ^ 59
def prefixEnd_6810376 : Nat := 4983230072969 + 3 ^ 40 * 6810376 * 2
def baseEnd_6810376 : Nat := 3496996325844551606279657

theorem tailTrace_6810376 : CollatzResearch.WordTrace tailWord_6810376 prefixEnd_6810376 3496996325844551606279657 := by
  unfold tailWord_6810376
  simp only [CollatzResearch.WordTrace]
  refine ⟨124197409587589173232613491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165596546116785564310151321 124197409587589173232613491)
  ·
    refine ⟨186296114381383759848920237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124197409587589173232613491 186296114381383759848920237)
    ·
      refine ⟨69861042893018909943345089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186296114381383759848920237 69861042893018909943345089)
      ·
        refine ⟨52395782169764182457508817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69861042893018909943345089 52395782169764182457508817)
        ·
          refine ⟨39296836627323136843131613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52395782169764182457508817 39296836627323136843131613)
          ·
            refine ⟨14736313735246176316174355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39296836627323136843131613 14736313735246176316174355)
            ·
              refine ⟨22104470602869264474261533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14736313735246176316174355 22104470602869264474261533)
              ·
                refine ⟨8289176476075974177848075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22104470602869264474261533 8289176476075974177848075)
                ·
                  refine ⟨12433764714113961266772113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8289176476075974177848075 12433764714113961266772113)
                  ·
                    refine ⟨9325323535585470950079085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12433764714113961266772113 9325323535585470950079085)
                    ·
                      refine ⟨3496996325844551606279657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9325323535585470950079085 3496996325844551606279657)
                      ·
                        rfl

theorem cell23_6810376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_6810376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810376 prefixEnd_6810376 := by exact prefixLift 6810376
  have htrace : WordTrace (prefixWord ++ tailWord_6810376) baseStart_6810376 baseEnd_6810376 := by
    simpa [prefixWord, tailWord_6810376, baseEnd_6810376] using wordTrace_append hprefix tailTrace_6810376
  have hstable : (prefixWord ++ tailWord_6810376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810376).length < 2 ^ (prefixWord ++ tailWord_6810376).sum := by decide
  have hdescent : baseEnd_6810376 < baseStart_6810376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810382 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_6810382 : Nat := 118140960795 + 6810382 * 2 ^ 59
def prefixEnd_6810382 : Nat := 4983230072969 + 3 ^ 40 * 6810382 * 2
def baseEnd_6810382 : Nat := 3496999406728478582804629

theorem tailTrace_6810382 : CollatzResearch.WordTrace tailWord_6810382 prefixEnd_6810382 3496999406728478582804629 := by
  unfold tailWord_6810382
  simp only [CollatzResearch.WordTrace]
  refine ⟨31049379751644576186243175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165596692008771072993296933 31049379751644576186243175)
  ·
    refine ⟨46574069627466864279364763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31049379751644576186243175 46574069627466864279364763)
    ·
      refine ⟨69861104441200296419047145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46574069627466864279364763 69861104441200296419047145)
      ·
        refine ⟨52395828330900222314285359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69861104441200296419047145 52395828330900222314285359)
        ·
          refine ⟨78593742496350333471428039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52395828330900222314285359 78593742496350333471428039)
          ·
            refine ⟨117890613744525500207142059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78593742496350333471428039 117890613744525500207142059)
            ·
              refine ⟨176835920616788250310713089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117890613744525500207142059 176835920616788250310713089)
              ·
                refine ⟨132626940462591187733034817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176835920616788250310713089 132626940462591187733034817)
                ·
                  refine ⟨99470205346943390799776113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132626940462591187733034817 99470205346943390799776113)
                  ·
                    refine ⟨74602654010207543099832085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99470205346943390799776113 74602654010207543099832085)
                    ·
                      refine ⟨3496999406728478582804629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74602654010207543099832085 3496999406728478582804629)
                      ·
                        rfl

theorem cell23_6810382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_6810382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810382 prefixEnd_6810382 := by exact prefixLift 6810382
  have htrace : WordTrace (prefixWord ++ tailWord_6810382) baseStart_6810382 baseEnd_6810382 := by
    simpa [prefixWord, tailWord_6810382, baseEnd_6810382] using wordTrace_append hprefix tailTrace_6810382
  have hstable : (prefixWord ++ tailWord_6810382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810382).length < 2 ^ (prefixWord ++ tailWord_6810382).sum := by decide
  have hdescent : baseEnd_6810382 < baseStart_6810382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810410 : List Nat := [3, 1, 4, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_6810410 : Nat := 118140960795 + 6810410 * 2 ^ 59
def prefixEnd_6810410 : Nat := 4983230072969 + 3 ^ 40 * 6810410 * 2
def baseEnd_6810410 : Nat := 3497013784186804473254501

theorem tailTrace_6810410 : CollatzResearch.WordTrace tailWord_6810410 prefixEnd_6810410 3497013784186804473254501 := by
  unfold tailWord_6810410
  simp only [CollatzResearch.WordTrace]
  refine ⟨62099014814263792567991171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165597372838036780181309789 62099014814263792567991171)
  ·
    refine ⟨93148522221395688851986757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62099014814263792567991171 93148522221395688851986757)
    ·
      refine ⟨17465347916511691659747517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93148522221395688851986757 17465347916511691659747517)
      ·
        refine ⟨6549505468691884372405319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17465347916511691659747517 6549505468691884372405319)
        ·
          refine ⟨9824258203037826558607979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6549505468691884372405319 9824258203037826558607979)
          ·
            refine ⟨14736387304556739837911969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9824258203037826558607979 14736387304556739837911969)
            ·
              refine ⟨11052290478417554878433977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14736387304556739837911969 11052290478417554878433977)
              ·
                refine ⟨8289217858813166158825483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11052290478417554878433977 8289217858813166158825483)
                ·
                  refine ⟨12433826788219749238238225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8289217858813166158825483 12433826788219749238238225)
                  ·
                    refine ⟨9325370091164811928678669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12433826788219749238238225 9325370091164811928678669)
                    ·
                      refine ⟨3497013784186804473254501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9325370091164811928678669 3497013784186804473254501)
                      ·
                        rfl

theorem cell23_6810410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_6810410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810410 prefixEnd_6810410 := by exact prefixLift 6810410
  have htrace : WordTrace (prefixWord ++ tailWord_6810410) baseStart_6810410 baseEnd_6810410 := by
    simpa [prefixWord, tailWord_6810410, baseEnd_6810410] using wordTrace_append hprefix tailTrace_6810410
  have hstable : (prefixWord ++ tailWord_6810410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810410).length < 2 ^ (prefixWord ++ tailWord_6810410).sum := by decide
  have hdescent : baseEnd_6810410 < baseStart_6810410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810442 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_6810442 : Nat := 118140960795 + 6810442 * 2 ^ 59
def prefixEnd_6810442 : Nat := 4983230072969 + 3 ^ 40 * 6810442 * 2
def baseEnd_6810442 : Nat := 3497030215567748348054353

theorem tailTrace_6810442 : CollatzResearch.WordTrace tailWord_6810442 prefixEnd_6810442 3497030215567748348054353 := by
  unfold tailWord_6810442
  simp only [CollatzResearch.WordTrace]
  refine ⟨62099306598234809934282395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165598150928626159824753053 62099306598234809934282395)
  ·
    refine ⟨93148959897352214901423593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62099306598234809934282395 93148959897352214901423593)
    ·
      refine ⟨69861719923014161176067695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93148959897352214901423593 69861719923014161176067695)
      ·
        refine ⟨104792579884521241764101543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69861719923014161176067695 104792579884521241764101543)
        ·
          refine ⟨157188869826781862646152315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104792579884521241764101543 157188869826781862646152315)
          ·
            refine ⟨235783304740172793969228473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157188869826781862646152315 235783304740172793969228473)
            ·
              refine ⟨176837478555129595476921355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235783304740172793969228473 176837478555129595476921355)
              ·
                refine ⟨265256217832694393215382033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176837478555129595476921355 265256217832694393215382033)
                ·
                  refine ⟨198942163374520794911536525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265256217832694393215382033 198942163374520794911536525)
                  ·
                    refine ⟨74603311265445298091826197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 198942163374520794911536525 74603311265445298091826197)
                    ·
                      refine ⟨3497030215567748348054353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74603311265445298091826197 3497030215567748348054353)
                      ·
                        rfl

theorem cell23_6810442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_6810442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810442 prefixEnd_6810442 := by exact prefixLift 6810442
  have htrace : WordTrace (prefixWord ++ tailWord_6810442) baseStart_6810442 baseEnd_6810442 := by
    simpa [prefixWord, tailWord_6810442, baseEnd_6810442] using wordTrace_append hprefix tailTrace_6810442
  have hstable : (prefixWord ++ tailWord_6810442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810442).length < 2 ^ (prefixWord ++ tailWord_6810442).sum := by decide
  have hdescent : baseEnd_6810442 < baseStart_6810442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810463 : List Nat := [1, 1, 2, 3, 1, 3, 3, 3, 2, 2, 2]
def baseStart_6810463 : Nat := 118140960795 + 6810463 * 2 ^ 59
def prefixEnd_6810463 : Nat := 4983230072969 + 3 ^ 40 * 6810463 * 2
def baseEnd_6810463 : Nat := 3497040998661492765891757

theorem tailTrace_6810463 : CollatzResearch.WordTrace tailWord_6810463 prefixEnd_6810463 3497040998661492765891757 := by
  unfold tailWord_6810463
  simp only [CollatzResearch.WordTrace]
  refine ⟨248397992325863160323644043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165598661550575440215762695 248397992325863160323644043)
  ·
    refine ⟨372596988488794740485466065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248397992325863160323644043 372596988488794740485466065)
    ·
      refine ⟨279447741366596055364099549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372596988488794740485466065 279447741366596055364099549)
      ·
        refine ⟨104792903012473520761537331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279447741366596055364099549 104792903012473520761537331)
        ·
          refine ⟨157189354518710281142305997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104792903012473520761537331 157189354518710281142305997)
          ·
            refine ⟨58946007944516355428364749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157189354518710281142305997 58946007944516355428364749)
            ·
              refine ⟨22104752979193633285636781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58946007944516355428364749 22104752979193633285636781)
              ·
                refine ⟨8289282367197612482113793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22104752979193633285636781 8289282367197612482113793)
                ·
                  refine ⟨6216961775398209361585345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8289282367197612482113793 6216961775398209361585345)
                  ·
                    refine ⟨4662721331548657021189009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6216961775398209361585345 4662721331548657021189009)
                    ·
                      refine ⟨3497040998661492765891757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4662721331548657021189009 3497040998661492765891757)
                      ·
                        rfl

theorem cell23_6810463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_6810463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810463 prefixEnd_6810463 := by exact prefixLift 6810463
  have htrace : WordTrace (prefixWord ++ tailWord_6810463) baseStart_6810463 baseEnd_6810463 := by
    simpa [prefixWord, tailWord_6810463, baseEnd_6810463] using wordTrace_append hprefix tailTrace_6810463
  have hstable : (prefixWord ++ tailWord_6810463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810463).length < 2 ^ (prefixWord ++ tailWord_6810463).sum := by decide
  have hdescent : baseEnd_6810463 < baseStart_6810463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810499 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 2, 5]
def baseStart_6810499 : Nat := 118140960795 + 6810499 * 2 ^ 59
def prefixEnd_6810499 : Nat := 4983230072969 + 3 ^ 40 * 6810499 * 2
def baseEnd_6810499 : Nat := 1165686494655018208347197

theorem tailTrace_6810499 : CollatzResearch.WordTrace tailWord_6810499 prefixEnd_6810499 1165686494655018208347197 := by
  unfold tailWord_6810499
  simp only [CollatzResearch.WordTrace]
  refine ⟨248399305353732738471954551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165599536902488492314636367 248399305353732738471954551)
  ·
    refine ⟨372598958030599107707931827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248399305353732738471954551 372598958030599107707931827)
    ·
      refine ⟨558898437045898661561897741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372598958030599107707931827 558898437045898661561897741)
      ·
        refine ⟨209586913892211998085711653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 558898437045898661561897741 209586913892211998085711653)
        ·
          refine ⟨39297546354789749641070935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209586913892211998085711653 39297546354789749641070935)
          ·
            refine ⟨58946319532184624461606403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39297546354789749641070935 58946319532184624461606403)
            ·
              refine ⟨88419479298276936692409605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58946319532184624461606403 88419479298276936692409605)
              ·
                refine ⟨16578652368426925629826801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88419479298276936692409605 16578652368426925629826801)
                ·
                  refine ⟨12433989276320194222370101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16578652368426925629826801 12433989276320194222370101)
                  ·
                    refine ⟨1165686494655018208347197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12433989276320194222370101 1165686494655018208347197)
                    ·
                      rfl

theorem cell23_6810499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 5].length) (baseStart_6810499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810499 prefixEnd_6810499 := by exact prefixLift 6810499
  have htrace : WordTrace (prefixWord ++ tailWord_6810499) baseStart_6810499 baseEnd_6810499 := by
    simpa [prefixWord, tailWord_6810499, baseEnd_6810499] using wordTrace_append hprefix tailTrace_6810499
  have hstable : (prefixWord ++ tailWord_6810499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810499).length < 2 ^ (prefixWord ++ tailWord_6810499).sum := by decide
  have hdescent : baseEnd_6810499 < baseStart_6810499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810503 : List Nat := [1, 1, 4, 2, 3, 1, 4, 2, 5]
def baseStart_6810503 : Nat := 118140960795 + 6810503 * 2 ^ 59
def prefixEnd_6810503 : Nat := 4983230072969 + 3 ^ 40 * 6810503 * 2
def baseEnd_6810503 : Nat := 388562393098630289932397

theorem tailTrace_6810503 : CollatzResearch.WordTrace tailWord_6810503 prefixEnd_6810503 388562393098630289932397 := by
  unfold tailWord_6810503
  simp only [CollatzResearch.WordTrace]
  refine ⟨248399451245718247155100163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165599634163812164770066775 248399451245718247155100163)
  ·
    refine ⟨372599176868577370732650245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248399451245718247155100163 372599176868577370732650245)
    ·
      refine ⟨69862345662858257012371921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372599176868577370732650245 69862345662858257012371921)
      ·
        refine ⟨52396759247143692759278941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69862345662858257012371921 52396759247143692759278941)
        ·
          refine ⟨19648784717678884784729603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52396759247143692759278941 19648784717678884784729603)
          ·
            refine ⟨29473177076518327177094405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19648784717678884784729603 29473177076518327177094405)
            ·
              refine ⟨5526220701847186345705201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29473177076518327177094405 5526220701847186345705201)
              ·
                refine ⟨4144665526385389759278901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5526220701847186345705201 4144665526385389759278901)
                ·
                  refine ⟨388562393098630289932397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4144665526385389759278901 388562393098630289932397)
                  ·
                    rfl

theorem cell23_6810503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 5].length) (baseStart_6810503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810503 prefixEnd_6810503 := by exact prefixLift 6810503
  have htrace : WordTrace (prefixWord ++ tailWord_6810503) baseStart_6810503 baseEnd_6810503 := by
    simpa [prefixWord, tailWord_6810503, baseEnd_6810503] using wordTrace_append hprefix tailTrace_6810503
  have hstable : (prefixWord ++ tailWord_6810503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810503).length < 2 ^ (prefixWord ++ tailWord_6810503).sum := by decide
  have hdescent : baseEnd_6810503 < baseStart_6810503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810519 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 4]
def baseStart_6810519 : Nat := 118140960795 + 6810519 * 2 ^ 59
def prefixEnd_6810519 : Nat := 4983230072969 + 3 ^ 40 * 6810519 * 2
def baseEnd_6810519 : Nat := 3497069753578144546791499

theorem tailTrace_6810519 : CollatzResearch.WordTrace tailWord_6810519 prefixEnd_6810519 3497069753578144546791499 := by
  unfold tailWord_6810519
  simp only [CollatzResearch.WordTrace]
  refine ⟨248400034813660281887682611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165600023209106854591788407 248400034813660281887682611)
  ·
    refine ⟨372600052220490422831523917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248400034813660281887682611 372600052220490422831523917)
    ·
      refine ⟨139725019582683908561821469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372600052220490422831523917 139725019582683908561821469)
      ·
        refine ⟨52396882343506465710683051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139725019582683908561821469 52396882343506465710683051)
        ·
          refine ⟨78595323515259698566024577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52396882343506465710683051 78595323515259698566024577)
          ·
            refine ⟨58946492636444773924518433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78595323515259698566024577 58946492636444773924518433)
            ·
              refine ⟨44209869477333580443388825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58946492636444773924518433 44209869477333580443388825)
              ·
                refine ⟨33157402108000185332541619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44209869477333580443388825 33157402108000185332541619)
                ·
                  refine ⟨49736103162000277998812429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33157402108000185332541619 49736103162000277998812429)
                  ·
                    refine ⟨18651038685750104249554661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49736103162000277998812429 18651038685750104249554661)
                    ·
                      refine ⟨3497069753578144546791499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18651038685750104249554661 3497069753578144546791499)
                      ·
                        rfl

theorem cell23_6810519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_6810519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810519 prefixEnd_6810519 := by exact prefixLift 6810519
  have htrace : WordTrace (prefixWord ++ tailWord_6810519) baseStart_6810519 baseEnd_6810519 := by
    simpa [prefixWord, tailWord_6810519, baseEnd_6810519] using wordTrace_append hprefix tailTrace_6810519
  have hstable : (prefixWord ++ tailWord_6810519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810519).length < 2 ^ (prefixWord ++ tailWord_6810519).sum := by decide
  have hdescent : baseEnd_6810519 < baseStart_6810519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810539 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 3]
def baseStart_6810539 : Nat := 118140960795 + 6810539 * 2 ^ 59
def prefixEnd_6810539 : Nat := 4983230072969 + 3 ^ 40 * 6810539 * 2
def baseEnd_6810539 : Nat := 3497080023191234468541407

theorem tailTrace_6810539 : CollatzResearch.WordTrace tailWord_6810539 prefixEnd_6810539 3497080023191234468541407 := by
  unfold tailWord_6810539
  simp only [CollatzResearch.WordTrace]
  refine ⟨248400764273587825303410671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165600509515725216868940447 248400764273587825303410671)
  ·
    refine ⟨372601146410381737955116007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248400764273587825303410671 372601146410381737955116007)
    ·
      refine ⟨558901719615572606932674011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372601146410381737955116007 558901719615572606932674011)
      ·
        refine ⟨838352579423358910399011017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558901719615572606932674011 838352579423358910399011017)
        ·
          refine ⟨628764434567519182799258263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 838352579423358910399011017 628764434567519182799258263)
          ·
            refine ⟨943146651851278774198887395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628764434567519182799258263 943146651851278774198887395)
            ·
              refine ⟨1414719977776918161298331093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943146651851278774198887395 1414719977776918161298331093)
              ·
                refine ⟨33157499479146519405429635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1414719977776918161298331093 33157499479146519405429635)
                ·
                  refine ⟨49736249218719779108144453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33157499479146519405429635 49736249218719779108144453)
                  ·
                    refine ⟨9325546728509958582777085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49736249218719779108144453 9325546728509958582777085)
                    ·
                      refine ⟨3497080023191234468541407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9325546728509958582777085 3497080023191234468541407)
                      ·
                        rfl

theorem cell23_6810539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 3].length) (baseStart_6810539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810539 prefixEnd_6810539 := by exact prefixLift 6810539
  have htrace : WordTrace (prefixWord ++ tailWord_6810539) baseStart_6810539 baseEnd_6810539 := by
    simpa [prefixWord, tailWord_6810539, baseEnd_6810539] using wordTrace_append hprefix tailTrace_6810539
  have hstable : (prefixWord ++ tailWord_6810539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810539).length < 2 ^ (prefixWord ++ tailWord_6810539).sum := by decide
  have hdescent : baseEnd_6810539 < baseStart_6810539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810549 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_6810549 : Nat := 118140960795 + 6810549 * 2 ^ 59
def prefixEnd_6810549 : Nat := 4983230072969 + 3 ^ 40 * 6810549 * 2
def baseEnd_6810549 : Nat := 3497085157997779429416361

theorem tailTrace_6810549 : CollatzResearch.WordTrace tailWord_6810549 prefixEnd_6810549 3497085157997779429416361 := by
  unfold tailWord_6810549
  simp only [CollatzResearch.WordTrace]
  refine ⟨248401129003551597011274701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165600752669034398007516467 248401129003551597011274701)
  ·
    refine ⟨93150423376331848879228013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248401129003551597011274701 93150423376331848879228013)
    ·
      refine ⟨34931408766124443329710505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93150423376331848879228013 34931408766124443329710505)
      ·
        refine ⟨26198556574593332497282879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34931408766124443329710505 26198556574593332497282879)
        ·
          refine ⟨39297834861889998745924319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26198556574593332497282879 39297834861889998745924319)
          ·
            refine ⟨58946752292834998118886479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39297834861889998745924319 58946752292834998118886479)
            ·
              refine ⟨88420128439252497178329719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58946752292834998118886479 88420128439252497178329719)
              ·
                refine ⟨132630192658878745767494579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88420128439252497178329719 132630192658878745767494579)
                ·
                  refine ⟨198945288988318118651241869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132630192658878745767494579 198945288988318118651241869)
                  ·
                    refine ⟨74604483370619294494215701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 198945288988318118651241869 74604483370619294494215701)
                    ·
                      refine ⟨3497085157997779429416361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74604483370619294494215701 3497085157997779429416361)
                      ·
                        rfl

theorem cell23_6810549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_6810549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810549 prefixEnd_6810549 := by exact prefixLift 6810549
  have htrace : WordTrace (prefixWord ++ tailWord_6810549) baseStart_6810549 baseEnd_6810549 := by
    simpa [prefixWord, tailWord_6810549, baseEnd_6810549] using wordTrace_append hprefix tailTrace_6810549
  have hstable : (prefixWord ++ tailWord_6810549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810549).length < 2 ^ (prefixWord ++ tailWord_6810549).sum := by decide
  have hdescent : baseEnd_6810549 < baseStart_6810549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810559 : List Nat := [1, 1, 2, 2, 2, 1, 2, 6, 6]
def baseStart_6810559 : Nat := 118140960795 + 6810559 * 2 ^ 59
def prefixEnd_6810559 : Nat := 4983230072969 + 3 ^ 40 * 6810559 * 2
def baseEnd_6810559 : Nat := 388565588089369376699035

theorem tailTrace_6810559 : CollatzResearch.WordTrace tailWord_6810559 prefixEnd_6810559 388565588089369376699035 := by
  unfold tailWord_6810559
  simp only [CollatzResearch.WordTrace]
  refine ⟨248401493733515368719138731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165600995822343579146092487 248401493733515368719138731)
  ·
    refine ⟨372602240600273053078708097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248401493733515368719138731 372602240600273053078708097)
    ·
      refine ⟨279451680450204789809031073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372602240600273053078708097 279451680450204789809031073)
      ·
        refine ⟨209588760337653592356773305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279451680450204789809031073 209588760337653592356773305)
        ·
          refine ⟨157191570253240194267579979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209588760337653592356773305 157191570253240194267579979)
          ·
            refine ⟨235787355379860291401369969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157191570253240194267579979 235787355379860291401369969)
            ·
              refine ⟨176840516534895218551027477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235787355379860291401369969 176840516534895218551027477)
              ·
                refine ⟨8289399212573213369579413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 176840516534895218551027477 8289399212573213369579413)
                ·
                  refine ⟨388565588089369376699035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8289399212573213369579413 388565588089369376699035)
                  ·
                    rfl

theorem cell23_6810559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 6].length) (baseStart_6810559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810559 prefixEnd_6810559 := by exact prefixLift 6810559
  have htrace : WordTrace (prefixWord ++ tailWord_6810559) baseStart_6810559 baseEnd_6810559 := by
    simpa [prefixWord, tailWord_6810559, baseEnd_6810559] using wordTrace_append hprefix tailTrace_6810559
  have hstable : (prefixWord ++ tailWord_6810559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810559).length < 2 ^ (prefixWord ++ tailWord_6810559).sum := by decide
  have hdescent : baseEnd_6810559 < baseStart_6810559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810569 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 4, 5, 3]
def baseStart_6810569 : Nat := 118140960795 + 6810569 * 2 ^ 59
def prefixEnd_6810569 : Nat := 4983230072969 + 3 ^ 40 * 6810569 * 2
def baseEnd_6810569 : Nat := 3497095427610869351166269

theorem tailTrace_6810569 : CollatzResearch.WordTrace tailWord_6810569 prefixEnd_6810569 3497095427610869351166269 := by
  unfold tailWord_6810569
  simp only [CollatzResearch.WordTrace]
  refine ⟨248401858463479140427002761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165601238975652760284668507 248401858463479140427002761)
  ·
    refine ⟨186301393847609355320252071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248401858463479140427002761 186301393847609355320252071)
    ·
      refine ⟨279452090771414032980378107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186301393847609355320252071 279452090771414032980378107)
      ·
        refine ⟨419178136157121049470567161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279452090771414032980378107 419178136157121049470567161)
        ·
          refine ⟨314383602117840787102925371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419178136157121049470567161 314383602117840787102925371)
          ·
            refine ⟨471575403176761180654388057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314383602117840787102925371 471575403176761180654388057)
            ·
              refine ⟨353681552382570885490791043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471575403176761180654388057 353681552382570885490791043)
              ·
                refine ⟨530522328573856328236186565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353681552382570885490791043 530522328573856328236186565)
                ·
                  refine ⟨99472936607598061544284981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 530522328573856328236186565 99472936607598061544284981)
                  ·
                    refine ⟨9325587806962318269776717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99472936607598061544284981 9325587806962318269776717)
                    ·
                      refine ⟨3497095427610869351166269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9325587806962318269776717 3497095427610869351166269)
                      ·
                        rfl

theorem cell23_6810569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 5, 3].length) (baseStart_6810569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810569 prefixEnd_6810569 := by exact prefixLift 6810569
  have htrace : WordTrace (prefixWord ++ tailWord_6810569) baseStart_6810569 baseEnd_6810569 := by
    simpa [prefixWord, tailWord_6810569, baseEnd_6810569] using wordTrace_append hprefix tailTrace_6810569
  have hstable : (prefixWord ++ tailWord_6810569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810569).length < 2 ^ (prefixWord ++ tailWord_6810569).sum := by decide
  have hdescent : baseEnd_6810569 < baseStart_6810569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810620 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 3, 1, 3]
def baseStart_6810620 : Nat := 118140960795 + 6810620 * 2 ^ 59
def prefixEnd_6810620 : Nat := 4983230072969 + 3 ^ 40 * 6810620 * 2
def baseEnd_6810620 : Nat := 3497121615124248651628535

theorem tailTrace_6810620 : CollatzResearch.WordTrace tailWord_6810620 prefixEnd_6810620 3497121615124248651628535 := by
  unfold tailWord_6810620
  simp only [CollatzResearch.WordTrace]
  refine ⟨124201859293147188068554657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165602479057529584091406209 124201859293147188068554657)
  ·
    refine ⟨93151394469860391051415993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124201859293147188068554657 93151394469860391051415993)
    ·
      refine ⟨69863545852395293288561995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93151394469860391051415993 69863545852395293288561995)
      ·
        refine ⟨104795318778592939932842993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69863545852395293288561995 104795318778592939932842993)
        ·
          refine ⟨78596489083944704949632245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104795318778592939932842993 78596489083944704949632245)
          ·
            refine ⟨7368420851619816089028023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78596489083944704949632245 7368420851619816089028023)
            ·
              refine ⟨11052631277429724133542035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7368420851619816089028023 11052631277429724133542035)
              ·
                refine ⟨16578946916144586200313053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11052631277429724133542035 16578946916144586200313053)
                ·
                  refine ⟨6217105093554219825117395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16578946916144586200313053 6217105093554219825117395)
                  ·
                    refine ⟨9325657640331329737676093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6217105093554219825117395 9325657640331329737676093)
                    ·
                      refine ⟨3497121615124248651628535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9325657640331329737676093 3497121615124248651628535)
                      ·
                        rfl

theorem cell23_6810620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_6810620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810620 prefixEnd_6810620 := by exact prefixLift 6810620
  have htrace : WordTrace (prefixWord ++ tailWord_6810620) baseStart_6810620 baseEnd_6810620 := by
    simpa [prefixWord, tailWord_6810620, baseEnd_6810620] using wordTrace_append hprefix tailTrace_6810620
  have hstable : (prefixWord ++ tailWord_6810620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810620).length < 2 ^ (prefixWord ++ tailWord_6810620).sum := by decide
  have hdescent : baseEnd_6810620 < baseStart_6810620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810643 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 5, 2, 2]
def baseStart_6810643 : Nat := 118140960795 + 6810643 * 2 ^ 59
def prefixEnd_6810643 : Nat := 4983230072969 + 3 ^ 40 * 6810643 * 2
def baseEnd_6810643 : Nat := 3497133425179302061640929

theorem tailTrace_6810643 : CollatzResearch.WordTrace tailWord_6810643 prefixEnd_6810643 3497133425179302061640929 := by
  unfold tailWord_6810643
  simp only [CollatzResearch.WordTrace]
  refine ⟨248404557465211051065196583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165603038310140700710131055 248404557465211051065196583)
  ·
    refine ⟨372606836197816576597794875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248404557465211051065196583 372606836197816576597794875)
    ·
      refine ⟨558910254296724864896692313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372606836197816576597794875 558910254296724864896692313)
      ·
        refine ⟨419182690722543648672519235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558910254296724864896692313 419182690722543648672519235)
        ·
          refine ⟨628774036083815473008778853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419182690722543648672519235 628774036083815473008778853)
          ·
            refine ⟨117895131765715401189146035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 628774036083815473008778853 117895131765715401189146035)
            ·
              refine ⟨176842697648573101783719053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117895131765715401189146035 176842697648573101783719053)
              ·
                refine ⟨66316011618214913168894645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176842697648573101783719053 66316011618214913168894645)
                ·
                  refine ⟨6217126089207648109583873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66316011618214913168894645 6217126089207648109583873)
                  ·
                    refine ⟨4662844566905736082187905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6217126089207648109583873 4662844566905736082187905)
                    ·
                      refine ⟨3497133425179302061640929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4662844566905736082187905 3497133425179302061640929)
                      ·
                        rfl

theorem cell23_6810643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 2, 2].length) (baseStart_6810643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810643 prefixEnd_6810643 := by exact prefixLift 6810643
  have htrace : WordTrace (prefixWord ++ tailWord_6810643) baseStart_6810643 baseEnd_6810643 := by
    simpa [prefixWord, tailWord_6810643, baseEnd_6810643] using wordTrace_append hprefix tailTrace_6810643
  have hstable : (prefixWord ++ tailWord_6810643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810643).length < 2 ^ (prefixWord ++ tailWord_6810643).sum := by decide
  have hdescent : baseEnd_6810643 < baseStart_6810643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810649 : List Nat := [1, 2, 1, 2, 1, 1, 6, 9]
def baseStart_6810649 : Nat := 118140960795 + 6810649 * 2 ^ 59
def prefixEnd_6810649 : Nat := 4983230072969 + 3 ^ 40 * 6810649 * 2
def baseEnd_6810649 : Nat := 129523574298638112524663

theorem tailTrace_6810649 : CollatzResearch.WordTrace tailWord_6810649 prefixEnd_6810649 129523574298638112524663 := by
  unfold tailWord_6810649
  simp only [CollatzResearch.WordTrace]
  refine ⟨248404776303189314089915001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165603184202126209393276667 248404776303189314089915001)
  ·
    refine ⟨186303582227391985567436251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248404776303189314089915001 186303582227391985567436251)
    ·
      refine ⟨279455373341087978351154377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186303582227391985567436251 279455373341087978351154377)
      ·
        refine ⟨209591530005815983763365783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279455373341087978351154377 209591530005815983763365783)
        ·
          refine ⟨314387295008723975645048675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209591530005815983763365783 314387295008723975645048675)
          ·
            refine ⟨471580942513085963467573013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314387295008723975645048675 471580942513085963467573013)
            ·
              refine ⟨22105356680300904537542485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 471580942513085963467573013 22105356680300904537542485)
              ·
                refine ⟨129523574298638112524663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22105356680300904537542485 129523574298638112524663)
                ·
                  rfl

theorem cell23_6810649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 9].length) (baseStart_6810649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810649 prefixEnd_6810649 := by exact prefixLift 6810649
  have htrace : WordTrace (prefixWord ++ tailWord_6810649) baseStart_6810649 baseEnd_6810649 := by
    simpa [prefixWord, tailWord_6810649, baseEnd_6810649] using wordTrace_append hprefix tailTrace_6810649
  have hstable : (prefixWord ++ tailWord_6810649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810649).length < 2 ^ (prefixWord ++ tailWord_6810649).sum := by decide
  have hdescent : baseEnd_6810649 < baseStart_6810649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810653 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 1, 6]
def baseStart_6810653 : Nat := 118140960795 + 6810653 * 2 ^ 59
def prefixEnd_6810653 : Nat := 4983230072969 + 3 ^ 40 * 6810653 * 2
def baseEnd_6810653 : Nat := 1165712853328615674171961

theorem tailTrace_6810653 : CollatzResearch.WordTrace tailWord_6810653 prefixEnd_6810653 1165712853328615674171961 := by
  unfold tailWord_6810653
  simp only [CollatzResearch.WordTrace]
  refine ⟨248404922195174822773060613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165603281463449881848707075 248404922195174822773060613)
  ·
    refine ⟨46575922911595279269948865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248404922195174822773060613 46575922911595279269948865)
    ·
      refine ⟨34931942183696459452461649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46575922911595279269948865 34931942183696459452461649)
      ·
        refine ⟨26198956637772344589346237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34931942183696459452461649 26198956637772344589346237)
        ·
          refine ⟨9824608739164629221004839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26198956637772344589346237 9824608739164629221004839)
          ·
            refine ⟨14736913108746943831507259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9824608739164629221004839 14736913108746943831507259)
            ·
              refine ⟨22105369663120415747260889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14736913108746943831507259 22105369663120415747260889)
              ·
                refine ⟨16579027247340311810445667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22105369663120415747260889 16579027247340311810445667)
                ·
                  refine ⟨24868540871010467715668501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16579027247340311810445667 24868540871010467715668501)
                  ·
                    refine ⟨1165712853328615674171961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24868540871010467715668501 1165712853328615674171961)
                    ·
                      rfl

theorem cell23_6810653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_6810653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810653 prefixEnd_6810653 := by exact prefixLift 6810653
  have htrace : WordTrace (prefixWord ++ tailWord_6810653) baseStart_6810653 baseEnd_6810653 := by
    simpa [prefixWord, tailWord_6810653, baseEnd_6810653] using wordTrace_append hprefix tailTrace_6810653
  have hstable : (prefixWord ++ tailWord_6810653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810653).length < 2 ^ (prefixWord ++ tailWord_6810653).sum := by decide
  have hdescent : baseEnd_6810653 < baseStart_6810653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810666 : List Nat := [3, 1, 4, 1, 3, 11]
def baseStart_6810666 : Nat := 118140960795 + 6810666 * 2 ^ 59
def prefixEnd_6810666 : Nat := 4983230072969 + 3 ^ 40 * 6810666 * 2
def baseEnd_6810666 : Nat := 14391544177919158319561

theorem tailTrace_6810666 : CollatzResearch.WordTrace tailWord_6810666 prefixEnd_6810666 14391544177919158319561 := by
  unfold tailWord_6810666
  simp only [CollatzResearch.WordTrace]
  refine ⟨62101349086031931498320963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165603597562751817328855901 62101349086031931498320963)
  ·
    refine ⟨93152023629047897247481445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62101349086031931498320963 93152023629047897247481445)
    ·
      refine ⟨17466004430446480733902771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93152023629047897247481445 17466004430446480733902771)
      ·
        refine ⟨26199006645669721100854157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17466004430446480733902771 26199006645669721100854157)
        ·
          refine ⟨9824627492126145412820309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26199006645669721100854157 9824627492126145412820309)
          ·
            refine ⟨14391544177919158319561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9824627492126145412820309 14391544177919158319561)
            ·
              rfl

theorem cell23_6810666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 11].length) (baseStart_6810666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810666 prefixEnd_6810666 := by exact prefixLift 6810666
  have htrace : WordTrace (prefixWord ++ tailWord_6810666) baseStart_6810666 baseEnd_6810666 := by
    simpa [prefixWord, tailWord_6810666, baseEnd_6810666] using wordTrace_append hprefix tailTrace_6810666
  have hstable : (prefixWord ++ tailWord_6810666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810666).length < 2 ^ (prefixWord ++ tailWord_6810666).sum := by decide
  have hdescent : baseEnd_6810666 < baseStart_6810666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810670 : List Nat := [4, 1, 3, 1, 1, 1, 4, 2, 2, 4]
def baseStart_6810670 : Nat := 118140960795 + 6810670 * 2 ^ 59
def prefixEnd_6810670 : Nat := 4983230072969 + 3 ^ 40 * 6810670 * 2
def baseEnd_6810670 : Nat := 1165715763052324485334435

theorem tailTrace_6810670 : CollatzResearch.WordTrace tailWord_6810670 prefixEnd_6810670 1165715763052324485334435 := by
  unfold tailWord_6810670
  simp only [CollatzResearch.WordTrace]
  refine ⟨31050692779514154334553683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165603694824075489784286309 31050692779514154334553683)
  ·
    refine ⟨46576039169271231501830525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31050692779514154334553683 46576039169271231501830525)
    ·
      refine ⟨17466014688476711813186447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46576039169271231501830525 17466014688476711813186447)
      ·
        refine ⟨26199022032715067719779671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17466014688476711813186447 26199022032715067719779671)
        ·
          refine ⟨39298533049072601579669507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26199022032715067719779671 39298533049072601579669507)
          ·
            refine ⟨58947799573608902369504261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39298533049072601579669507 58947799573608902369504261)
            ·
              refine ⟨11052712420051669194282049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58947799573608902369504261 11052712420051669194282049)
              ·
                refine ⟨8289534315038751895711537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11052712420051669194282049 8289534315038751895711537)
                ·
                  refine ⟨6217150736279063921783653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8289534315038751895711537 6217150736279063921783653)
                  ·
                    refine ⟨1165715763052324485334435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6217150736279063921783653 1165715763052324485334435)
                    ·
                      rfl

theorem cell23_6810670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_6810670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810670 prefixEnd_6810670 := by exact prefixLift 6810670
  have htrace : WordTrace (prefixWord ++ tailWord_6810670) baseStart_6810670 baseEnd_6810670 := by
    simpa [prefixWord, tailWord_6810670, baseEnd_6810670] using wordTrace_append hprefix tailTrace_6810670
  have hstable : (prefixWord ++ tailWord_6810670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810670).length < 2 ^ (prefixWord ++ tailWord_6810670).sum := by decide
  have hdescent : baseEnd_6810670 < baseStart_6810670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810694 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_6810694 : Nat := 118140960795 + 6810694 * 2 ^ 59
def prefixEnd_6810694 : Nat := 4983230072969 + 3 ^ 40 * 6810694 * 2
def baseEnd_6810694 : Nat := 3497159612692681362103195

theorem tailTrace_6810694 : CollatzResearch.WordTrace tailWord_6810694 prefixEnd_6810694 3497159612692681362103195 := by
  unfold tailWord_6810694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7762700549625821461728223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 165604278392017524516868757 7762700549625821461728223)
  ·
    refine ⟨11644050824438732192592335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7762700549625821461728223 11644050824438732192592335)
    ·
      refine ⟨17466076236658098288888503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11644050824438732192592335 17466076236658098288888503)
      ·
        refine ⟨26199114354987147433332755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17466076236658098288888503 26199114354987147433332755)
        ·
          refine ⟨39298671532480721149999133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26199114354987147433332755 39298671532480721149999133)
          ·
            refine ⟨14737001824680270431249675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39298671532480721149999133 14737001824680270431249675)
            ·
              refine ⟨22105502737020405646874513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14737001824680270431249675 22105502737020405646874513)
              ·
                refine ⟨16579127052765304235155885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22105502737020405646874513 16579127052765304235155885)
                ·
                  refine ⟨6217172644786989088183457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16579127052765304235155885 6217172644786989088183457)
                  ·
                    refine ⟨4662879483590241816137593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6217172644786989088183457 4662879483590241816137593)
                    ·
                      refine ⟨3497159612692681362103195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4662879483590241816137593 3497159612692681362103195)
                      ·
                        rfl

theorem cell23_6810694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_6810694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810694 prefixEnd_6810694 := by exact prefixLift 6810694
  have htrace : WordTrace (prefixWord ++ tailWord_6810694) baseStart_6810694 baseEnd_6810694 := by
    simpa [prefixWord, tailWord_6810694, baseEnd_6810694] using wordTrace_append hprefix tailTrace_6810694
  have hstable : (prefixWord ++ tailWord_6810694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810694).length < 2 ^ (prefixWord ++ tailWord_6810694).sum := by decide
  have hdescent : baseEnd_6810694 < baseStart_6810694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810699 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 10]
def baseStart_6810699 : Nat := 118140960795 + 6810699 * 2 ^ 59
def prefixEnd_6810699 : Nat := 4983230072969 + 3 ^ 40 * 6810699 * 2
def baseEnd_6810699 : Nat := 3497162180095953842540671

theorem tailTrace_6810699 : CollatzResearch.WordTrace tailWord_6810699 prefixEnd_6810699 3497162180095953842540671 := by
  unfold tailWord_6810699
  simp only [CollatzResearch.WordTrace]
  refine ⟨248406599953008172629235151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165604399968672115086156767 248406599953008172629235151)
  ·
    refine ⟨372609899929512258943852727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248406599953008172629235151 372609899929512258943852727)
    ·
      refine ⟨558914849894268388415779091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372609899929512258943852727 558914849894268388415779091)
      ·
        refine ⟨838372274841402582623668637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558914849894268388415779091 838372274841402582623668637)
        ·
          refine ⟨314389603065525968483875739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 838372274841402582623668637 314389603065525968483875739)
          ·
            refine ⟨471584404598288952725813609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314389603065525968483875739 471584404598288952725813609)
            ·
              refine ⟨353688303448716714544360207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471584404598288952725813609 353688303448716714544360207)
              ·
                refine ⟨530532455173075071816540311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353688303448716714544360207 530532455173075071816540311)
                ·
                  refine ⟨795798682759612607724810467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530532455173075071816540311 795798682759612607724810467)
                  ·
                    refine ⟨1193698024139418911587215701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 795798682759612607724810467 1193698024139418911587215701)
                    ·
                      refine ⟨3497162180095953842540671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1193698024139418911587215701 3497162180095953842540671)
                      ·
                        rfl

theorem cell23_6810699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 10].length) (baseStart_6810699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810699 prefixEnd_6810699 := by exact prefixLift 6810699
  have htrace : WordTrace (prefixWord ++ tailWord_6810699) baseStart_6810699 baseEnd_6810699 := by
    simpa [prefixWord, tailWord_6810699, baseEnd_6810699] using wordTrace_append hprefix tailTrace_6810699
  have hstable : (prefixWord ++ tailWord_6810699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810699).length < 2 ^ (prefixWord ++ tailWord_6810699).sum := by decide
  have hdescent : baseEnd_6810699 < baseStart_6810699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810720 : List Nat := [2, 1, 1, 3, 2, 2, 3, 3, 1, 3, 2]
def baseStart_6810720 : Nat := 118140960795 + 6810720 * 2 ^ 59
def prefixEnd_6810720 : Nat := 4983230072969 + 3 ^ 40 * 6810720 * 2
def baseEnd_6810720 : Nat := 3497172963189698260378075

theorem tailTrace_6810720 : CollatzResearch.WordTrace tailWord_6810720 prefixEnd_6810720 3497172963189698260378075 := by
  unfold tailWord_6810720
  simp only [CollatzResearch.WordTrace]
  refine ⟨124203682942966046607874807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165604910590621395477166409 124203682942966046607874807)
  ·
    refine ⟨186305524414449069911812211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124203682942966046607874807 186305524414449069911812211)
    ·
      refine ⟨279458286621673604867718317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186305524414449069911812211 279458286621673604867718317)
      ·
        refine ⟨104796857483127601825394369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279458286621673604867718317 104796857483127601825394369)
        ·
          refine ⟨78597643112345701369045777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104796857483127601825394369 78597643112345701369045777)
          ·
            refine ⟨58948232334259276026784333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78597643112345701369045777 58948232334259276026784333)
            ·
              refine ⟨22105587125347228510044125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58948232334259276026784333 22105587125347228510044125)
              ·
                refine ⟨8289595172005210691266547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22105587125347228510044125 8289595172005210691266547)
                ·
                  refine ⟨12434392758007816036899821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8289595172005210691266547 12434392758007816036899821)
                  ·
                    refine ⟨4662897284252931013837433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12434392758007816036899821 4662897284252931013837433)
                    ·
                      refine ⟨3497172963189698260378075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4662897284252931013837433 3497172963189698260378075)
                      ·
                        rfl

theorem cell23_6810720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_6810720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810720 prefixEnd_6810720 := by exact prefixLift 6810720
  have htrace : WordTrace (prefixWord ++ tailWord_6810720) baseStart_6810720 baseEnd_6810720 := by
    simpa [prefixWord, tailWord_6810720, baseEnd_6810720] using wordTrace_append hprefix tailTrace_6810720
  have hstable : (prefixWord ++ tailWord_6810720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810720).length < 2 ^ (prefixWord ++ tailWord_6810720).sum := by decide
  have hdescent : baseEnd_6810720 < baseStart_6810720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810727 : List Nat := [1, 1, 5, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_6810727 : Nat := 118140960795 + 6810727 * 2 ^ 59
def prefixEnd_6810727 : Nat := 4983230072969 + 3 ^ 40 * 6810727 * 2
def baseEnd_6810727 : Nat := 3497176557554279732990543

theorem tailTrace_6810727 : CollatzResearch.WordTrace tailWord_6810727 prefixEnd_6810727 3497176557554279732990543 := by
  unfold tailWord_6810727
  simp only [CollatzResearch.WordTrace]
  refine ⟨248407621196906733411254435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165605080797937822274169623 248407621196906733411254435)
  ·
    refine ⟨372611431795360100116881653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248407621196906733411254435 372611431795360100116881653)
    ·
      refine ⟨34932321730815009385957655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 372611431795360100116881653 34932321730815009385957655)
      ·
        refine ⟨52398482596222514078936483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34932321730815009385957655 52398482596222514078936483)
        ·
          refine ⟨78597723894333771118404725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52398482596222514078936483 78597723894333771118404725)
          ·
            refine ⟨7368536615093791042350443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78597723894333771118404725 7368536615093791042350443)
            ·
              refine ⟨11052804922640686563525665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7368536615093791042350443 11052804922640686563525665)
              ·
                refine ⟨8289603691980514922644249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11052804922640686563525665 8289603691980514922644249)
                ·
                  refine ⟨6217202768985386191983187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8289603691980514922644249 6217202768985386191983187)
                  ·
                    refine ⟨9325804153478079287974781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6217202768985386191983187 9325804153478079287974781)
                    ·
                      refine ⟨3497176557554279732990543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9325804153478079287974781 3497176557554279732990543)
                      ·
                        rfl

theorem cell23_6810727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_6810727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810727 prefixEnd_6810727 := by exact prefixLift 6810727
  have htrace : WordTrace (prefixWord ++ tailWord_6810727) baseStart_6810727 baseEnd_6810727 := by
    simpa [prefixWord, tailWord_6810727, baseEnd_6810727] using wordTrace_append hprefix tailTrace_6810727
  have hstable : (prefixWord ++ tailWord_6810727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810727).length < 2 ^ (prefixWord ++ tailWord_6810727).sum := by decide
  have hdescent : baseEnd_6810727 < baseStart_6810727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810773 : List Nat := [1, 3, 2, 1, 1, 1, 2, 7, 5]
def baseStart_6810773 : Nat := 118140960795 + 6810773 * 2 ^ 59
def prefixEnd_6810773 : Nat := 4983230072969 + 3 ^ 40 * 6810773 * 2
def baseEnd_6810773 : Nat := 388577797518265172557259

theorem tailTrace_6810773 : CollatzResearch.WordTrace tailWord_6810773 prefixEnd_6810773 388577797518265172557259 := by
  unfold tailWord_6810773
  simp only [CollatzResearch.WordTrace]
  refine ⟨248409298954740083267428973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165606199303160055511619315 248409298954740083267428973)
  ·
    refine ⟨93153487108027531225285865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248409298954740083267428973 93153487108027531225285865)
    ·
      refine ⟨69865115331020648418964399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93153487108027531225285865 69865115331020648418964399)
      ·
        refine ⟨104797672996530972628446599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69865115331020648418964399 104797672996530972628446599)
        ·
          refine ⟨157196509494796458942669899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104797672996530972628446599 157196509494796458942669899)
          ·
            refine ⟨235794764242194688414004849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157196509494796458942669899 235794764242194688414004849)
            ·
              refine ⟨176846073181646016310503637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235794764242194688414004849 176846073181646016310503637)
              ·
                refine ⟨4144829840194828507277429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 176846073181646016310503637 4144829840194828507277429)
                ·
                  refine ⟨388577797518265172557259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4144829840194828507277429 388577797518265172557259)
                  ·
                    rfl

theorem cell23_6810773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 5].length) (baseStart_6810773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810773 prefixEnd_6810773 := by exact prefixLift 6810773
  have htrace : WordTrace (prefixWord ++ tailWord_6810773) baseStart_6810773 baseEnd_6810773 := by
    simpa [prefixWord, tailWord_6810773, baseEnd_6810773] using wordTrace_append hprefix tailTrace_6810773
  have hstable : (prefixWord ++ tailWord_6810773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810773).length < 2 ^ (prefixWord ++ tailWord_6810773).sum := by decide
  have hdescent : baseEnd_6810773 < baseStart_6810773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810801 : List Nat := [1, 2, 2, 5, 1, 3, 2, 1, 2, 2, 2]
def baseStart_6810801 : Nat := 118140960795 + 6810801 * 2 ^ 59
def prefixEnd_6810801 : Nat := 4983230072969 + 3 ^ 40 * 6810801 * 2
def baseEnd_6810801 : Nat := 3497214555122712443465203

theorem tailTrace_6810801 : CollatzResearch.WordTrace tailWord_6810801 prefixEnd_6810801 3497214555122712443465203 := by
  unfold tailWord_6810801
  simp only [CollatzResearch.WordTrace]
  refine ⟨248410320198638644049448257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165606880132425762699632171 248410320198638644049448257)
  ·
    refine ⟨186307740148978983037086193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248410320198638644049448257 186307740148978983037086193)
    ·
      refine ⟨139730805111734237277814645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186307740148978983037086193 139730805111734237277814645)
      ·
        refine ⟨13099762979225084744795123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139730805111734237277814645 13099762979225084744795123)
        ·
          refine ⟨19649644468837627117192685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13099762979225084744795123 19649644468837627117192685)
          ·
            refine ⟨7368616675814110168947257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19649644468837627117192685 7368616675814110168947257)
            ·
              refine ⟨5526462506860582626710443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7368616675814110168947257 5526462506860582626710443)
              ·
                refine ⟨8289693760290873940065665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5526462506860582626710443 8289693760290873940065665)
                ·
                  refine ⟨6217270320218155455049249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8289693760290873940065665 6217270320218155455049249)
                  ·
                    refine ⟨4662952740163616591286937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6217270320218155455049249 4662952740163616591286937)
                    ·
                      refine ⟨3497214555122712443465203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4662952740163616591286937 3497214555122712443465203)
                      ·
                        rfl

theorem cell23_6810801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_6810801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810801 prefixEnd_6810801 := by exact prefixLift 6810801
  have htrace : WordTrace (prefixWord ++ tailWord_6810801) baseStart_6810801 baseEnd_6810801 := by
    simpa [prefixWord, tailWord_6810801, baseEnd_6810801] using wordTrace_append hprefix tailTrace_6810801
  have hstable : (prefixWord ++ tailWord_6810801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810801).length < 2 ^ (prefixWord ++ tailWord_6810801).sum := by decide
  have hdescent : baseEnd_6810801 < baseStart_6810801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810884 : List Nat := [2, 3, 2, 2, 2, 2, 2, 3, 1, 4]
def baseStart_6810884 : Nat := 118140960795 + 6810884 * 2 ^ 59
def prefixEnd_6810884 : Nat := 4983230072969 + 3 ^ 40 * 6810884 * 2
def baseEnd_6810884 : Nat := 1165752391339011872909107

theorem tailTrace_6810884 : CollatzResearch.WordTrace tailWord_6810884 prefixEnd_6810884 1165752391339011872909107 := by
  unfold tailWord_6810884
  simp only [CollatzResearch.WordTrace]
  refine ⟨124206673728668974612359853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165608898304891966149813137 124206673728668974612359853)
  ·
    refine ⟨46577502648250865479634945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124206673728668974612359853 46577502648250865479634945)
    ·
      refine ⟨34933126986188149109726209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46577502648250865479634945 34933126986188149109726209)
      ·
        refine ⟨26199845239641111832294657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34933126986188149109726209 26199845239641111832294657)
        ·
          refine ⟨19649883929730833874220993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26199845239641111832294657 19649883929730833874220993)
          ·
            refine ⟨14737412947298125405665745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19649883929730833874220993 14737412947298125405665745)
            ·
              refine ⟨11053059710473594054249309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14737412947298125405665745 11053059710473594054249309)
              ·
                refine ⟨4144897391427597770343491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11053059710473594054249309 4144897391427597770343491)
                ·
                  refine ⟨6217346087141396655515237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4144897391427597770343491 6217346087141396655515237)
                  ·
                    refine ⟨1165752391339011872909107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6217346087141396655515237 1165752391339011872909107)
                    ·
                      rfl

theorem cell23_6810884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_6810884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810884 prefixEnd_6810884 := by exact prefixLift 6810884
  have htrace : WordTrace (prefixWord ++ tailWord_6810884) baseStart_6810884 baseEnd_6810884 := by
    simpa [prefixWord, tailWord_6810884, baseEnd_6810884] using wordTrace_append hprefix tailTrace_6810884
  have hstable : (prefixWord ++ tailWord_6810884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810884).length < 2 ^ (prefixWord ++ tailWord_6810884).sum := by decide
  have hdescent : baseEnd_6810884 < baseStart_6810884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810890 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3]
def baseStart_6810890 : Nat := 118140960795 + 6810890 * 2 ^ 59
def prefixEnd_6810890 : Nat := 4983230072969 + 3 ^ 40 * 6810890 * 2
def baseEnd_6810890 : Nat := 3497260254900962595252293

theorem tailTrace_6810890 : CollatzResearch.WordTrace tailWord_6810890 prefixEnd_6810890 3497260254900962595252293 := by
  unfold tailWord_6810890
  simp only [CollatzResearch.WordTrace]
  refine ⟨62103391573829053062359531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165609044196877474832958749 62103391573829053062359531)
  ·
    refine ⟨93155087360743579593539297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62103391573829053062359531 93155087360743579593539297)
    ·
      refine ⟨69866315520557684695154473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93155087360743579593539297 69866315520557684695154473)
      ·
        refine ⟨52399736640418263521365855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69866315520557684695154473 52399736640418263521365855)
        ·
          refine ⟨78599604960627395282048783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52399736640418263521365855 78599604960627395282048783)
          ·
            refine ⟨117899407440941092923073175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78599604960627395282048783 117899407440941092923073175)
            ·
              refine ⟨176849111161411639384609763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117899407440941092923073175 176849111161411639384609763)
              ·
                refine ⟨265273666742117459076914645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176849111161411639384609763 265273666742117459076914645)
                ·
                  refine ⟨6217351564268377947115187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 265273666742117459076914645 6217351564268377947115187)
                  ·
                    refine ⟨9326027346402566920672781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6217351564268377947115187 9326027346402566920672781)
                    ·
                      refine ⟨3497260254900962595252293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9326027346402566920672781 3497260254900962595252293)
                      ·
                        rfl

theorem cell23_6810890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_6810890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810890 prefixEnd_6810890 := by exact prefixLift 6810890
  have htrace : WordTrace (prefixWord ++ tailWord_6810890) baseStart_6810890 baseEnd_6810890 := by
    simpa [prefixWord, tailWord_6810890, baseEnd_6810890] using wordTrace_append hprefix tailTrace_6810890
  have hstable : (prefixWord ++ tailWord_6810890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810890).length < 2 ^ (prefixWord ++ tailWord_6810890).sum := by decide
  have hdescent : baseEnd_6810890 < baseStart_6810890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810940 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 4, 4]
def baseStart_6810940 : Nat := 118140960795 + 6810940 * 2 ^ 59
def prefixEnd_6810940 : Nat := 4983230072969 + 3 ^ 40 * 6810940 * 2
def baseEnd_6810940 : Nat := 1165761976311229133209021

theorem tailTrace_6810940 : CollatzResearch.WordTrace tailWord_6810940 prefixEnd_6810940 1165761976311229133209021 := by
  unfold tailWord_6810940
  simp only [CollatzResearch.WordTrace]
  refine ⟨124207694972567535394379137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165610259963423380525838849 124207694972567535394379137)
  ·
    refine ⟨93155771229425651545784353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124207694972567535394379137 93155771229425651545784353)
    ·
      refine ⟨69866828422069238659338265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93155771229425651545784353 69866828422069238659338265)
      ·
        refine ⟨52400121316551928994503699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69866828422069238659338265 52400121316551928994503699)
        ·
          refine ⟨78600181974827893491755549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52400121316551928994503699 78600181974827893491755549)
          ·
            refine ⟨29475068240560460059408331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78600181974827893491755549 29475068240560460059408331)
            ·
              refine ⟨44212602360840690089112497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29475068240560460059408331 44212602360840690089112497)
              ·
                refine ⟨33159451770630517566834373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44212602360840690089112497 33159451770630517566834373)
                ·
                  refine ⟨6217397206993222043781445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33159451770630517566834373 6217397206993222043781445)
                  ·
                    refine ⟨1165761976311229133209021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6217397206993222043781445 1165761976311229133209021)
                    ·
                      rfl

theorem cell23_6810940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_6810940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810940 prefixEnd_6810940 := by exact prefixLift 6810940
  have htrace : WordTrace (prefixWord ++ tailWord_6810940) baseStart_6810940 baseEnd_6810940 := by
    simpa [prefixWord, tailWord_6810940, baseEnd_6810940] using wordTrace_append hprefix tailTrace_6810940
  have hstable : (prefixWord ++ tailWord_6810940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810940).length < 2 ^ (prefixWord ++ tailWord_6810940).sum := by decide
  have hdescent : baseEnd_6810940 < baseStart_6810940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6810993 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 1, 4, 5]
def baseStart_6810993 : Nat := 118140960795 + 6810993 * 2 ^ 59
def prefixEnd_6810993 : Nat := 4983230072969 + 3 ^ 40 * 6810993 * 2
def baseEnd_6810993 : Nat := 3497313143408375692264319

theorem tailTrace_6810993 : CollatzResearch.WordTrace tailWord_6810993 prefixEnd_6810993 3497313143408375692264319 := by
  unfold tailWord_6810993
  simp only [CollatzResearch.WordTrace]
  refine ⟨248417323013943060840437633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165611548675962040560291755 248417323013943060840437633)
  ·
    refine ⟨186312992260457295630328225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248417323013943060840437633 186312992260457295630328225)
    ·
      refine ⟨139734744195342971722746169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186312992260457295630328225 139734744195342971722746169)
      ·
        refine ⟨104801058146507228792059627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139734744195342971722746169 104801058146507228792059627)
        ·
          refine ⟨157201587219760843188089441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104801058146507228792059627 157201587219760843188089441)
          ·
            refine ⟨117901190414820632391067081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157201587219760843188089441 117901190414820632391067081)
            ·
              refine ⟨88425892811115474293300311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117901190414820632391067081 88425892811115474293300311)
              ·
                refine ⟨132638839216673211439950467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88425892811115474293300311 132638839216673211439950467)
                ·
                  refine ⟨198958258825009817159925701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132638839216673211439950467 198958258825009817159925701)
                  ·
                    refine ⟨37304673529689340717486069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 198958258825009817159925701 37304673529689340717486069)
                    ·
                      refine ⟨3497313143408375692264319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37304673529689340717486069 3497313143408375692264319)
                      ·
                        rfl

theorem cell23_6810993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_6810993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6810993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6810993 prefixEnd_6810993 := by exact prefixLift 6810993
  have htrace : WordTrace (prefixWord ++ tailWord_6810993) baseStart_6810993 baseEnd_6810993 := by
    simpa [prefixWord, tailWord_6810993, baseEnd_6810993] using wordTrace_append hprefix tailTrace_6810993
  have hstable : (prefixWord ++ tailWord_6810993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6810993).length < 2 ^ (prefixWord ++ tailWord_6810993).sum := by decide
  have hdescent : baseEnd_6810993 < baseStart_6810993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6810993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811040 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 3]
def baseStart_6811040 : Nat := 118140960795 + 6811040 * 2 ^ 59
def prefixEnd_6811040 : Nat := 4983230072969 + 3 ^ 40 * 6811040 * 2
def baseEnd_6811040 : Nat := 3497337276999137008376603

theorem tailTrace_6811040 : CollatzResearch.WordTrace tailWord_6811040 prefixEnd_6811040 3497337276999137008376603 := by
  unfold tailWord_6811040
  simp only [CollatzResearch.WordTrace]
  refine ⟨124209518622386393933699287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165612691496515191911599049 124209518622386393933699287)
  ·
    refine ⟨186314277933579590900548931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124209518622386393933699287 186314277933579590900548931)
    ·
      refine ⟨279471416900369386350823397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186314277933579590900548931 279471416900369386350823397)
      ·
        refine ⟨52400890668819259940779387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279471416900369386350823397 52400890668819259940779387)
        ·
          refine ⟨78601336003228889911169081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52400890668819259940779387 78601336003228889911169081)
          ·
            refine ⟨58951002002421667433376811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78601336003228889911169081 58951002002421667433376811)
            ·
              refine ⟨88426503003632501150065217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58951002002421667433376811 88426503003632501150065217)
              ·
                refine ⟨66319877252724375862548913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88426503003632501150065217 66319877252724375862548913)
                ·
                  refine ⟨49739907939543281896911685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66319877252724375862548913 49739907939543281896911685)
                  ·
                    refine ⟨9326232738664365355670941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49739907939543281896911685 9326232738664365355670941)
                    ·
                      refine ⟨3497337276999137008376603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9326232738664365355670941 3497337276999137008376603)
                      ·
                        rfl

theorem cell23_6811040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_6811040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811040 prefixEnd_6811040 := by exact prefixLift 6811040
  have htrace : WordTrace (prefixWord ++ tailWord_6811040) baseStart_6811040 baseEnd_6811040 := by
    simpa [prefixWord, tailWord_6811040, baseEnd_6811040] using wordTrace_append hprefix tailTrace_6811040
  have hstable : (prefixWord ++ tailWord_6811040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811040).length < 2 ^ (prefixWord ++ tailWord_6811040).sum := by decide
  have hdescent : baseEnd_6811040 < baseStart_6811040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811127 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 2, 4, 2]
def baseStart_6811127 : Nat := 118140960795 + 6811127 * 2 ^ 59
def prefixEnd_6811127 : Nat := 4983230072969 + 3 ^ 40 * 6811127 * 2
def baseEnd_6811127 : Nat := 3497381949816078167988703

theorem tailTrace_6811127 : CollatzResearch.WordTrace tailWord_6811127 prefixEnd_6811127 3497381949816078167988703 := by
  unfold tailWord_6811127
  simp only [CollatzResearch.WordTrace]
  refine ⟨248422210395457601725815635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165614806930305067817210423 248422210395457601725815635)
  ·
    refine ⟨372633315593186402588723453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248422210395457601725815635 372633315593186402588723453)
    ·
      refine ⟨139737493347444900970771295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372633315593186402588723453 139737493347444900970771295)
      ·
        refine ⟨209606240021167351456156943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139737493347444900970771295 209606240021167351456156943)
        ·
          refine ⟨314409360031751027184235415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209606240021167351456156943 314409360031751027184235415)
          ·
            refine ⟨471614040047626540776353123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314409360031751027184235415 471614040047626540776353123)
            ·
              refine ⟨707421060071439811164529685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471614040047626540776353123 707421060071439811164529685)
              ·
                refine ⟨33160362190848741148337329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 707421060071439811164529685 33160362190848741148337329)
                ·
                  refine ⟨24870271643136555861252997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33160362190848741148337329 24870271643136555861252997)
                  ·
                    refine ⟨4663175933088104223984937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24870271643136555861252997 4663175933088104223984937)
                    ·
                      refine ⟨3497381949816078167988703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4663175933088104223984937 3497381949816078167988703)
                      ·
                        rfl

theorem cell23_6811127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 4, 2].length) (baseStart_6811127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811127 prefixEnd_6811127 := by exact prefixLift 6811127
  have htrace : WordTrace (prefixWord ++ tailWord_6811127) baseStart_6811127 baseEnd_6811127 := by
    simpa [prefixWord, tailWord_6811127, baseEnd_6811127] using wordTrace_append hprefix tailTrace_6811127
  have hstable : (prefixWord ++ tailWord_6811127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811127).length < 2 ^ (prefixWord ++ tailWord_6811127).sum := by decide
  have hdescent : baseEnd_6811127 < baseStart_6811127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811164 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_6811164 : Nat := 118140960795 + 6811164 * 2 ^ 59
def prefixEnd_6811164 : Nat := 4983230072969 + 3 ^ 40 * 6811164 * 2
def baseEnd_6811164 : Nat := 3497400948600294523226033

theorem tailTrace_6811164 : CollatzResearch.WordTrace tailWord_6811164 prefixEnd_6811164 3497400948600294523226033 := by
  unfold tailWord_6811164
  simp only [CollatzResearch.WordTrace]
  refine ⟨124211779948161778522456273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165615706597549038029941697 124211779948161778522456273)
  ·
    refine ⟨93158834961121333891842205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124211779948161778522456273 93158834961121333891842205)
    ·
      refine ⟨34934563110420500209440827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93158834961121333891842205 34934563110420500209440827)
      ·
        refine ⟨52401844665630750314161241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34934563110420500209440827 52401844665630750314161241)
        ·
          refine ⟨39301383499223062735620931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52401844665630750314161241 39301383499223062735620931)
          ·
            refine ⟨58952075248834594103431397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39301383499223062735620931 58952075248834594103431397)
            ·
              refine ⟨11053514109156486394393387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58952075248834594103431397 11053514109156486394393387)
              ·
                refine ⟨16580271163734729591590081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11053514109156486394393387 16580271163734729591590081)
                ·
                  refine ⟨12435203372801047193692561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16580271163734729591590081 12435203372801047193692561)
                  ·
                    refine ⟨9326402529600785395269421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12435203372801047193692561 9326402529600785395269421)
                    ·
                      refine ⟨3497400948600294523226033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9326402529600785395269421 3497400948600294523226033)
                      ·
                        rfl

theorem cell23_6811164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_6811164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811164 prefixEnd_6811164 := by exact prefixLift 6811164
  have htrace : WordTrace (prefixWord ++ tailWord_6811164) baseStart_6811164 baseEnd_6811164 := by
    simpa [prefixWord, tailWord_6811164, baseEnd_6811164] using wordTrace_append hprefix tailTrace_6811164
  have hstable : (prefixWord ++ tailWord_6811164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811164).length < 2 ^ (prefixWord ++ tailWord_6811164).sum := by decide
  have hdescent : baseEnd_6811164 < baseStart_6811164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811194 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3]
def baseStart_6811194 : Nat := 118140960795 + 6811194 * 2 ^ 59
def prefixEnd_6811194 : Nat := 4983230072969 + 3 ^ 40 * 6811194 * 2
def baseEnd_6811194 : Nat := 3497416353019929405850895

theorem tailTrace_6811194 : CollatzResearch.WordTrace tailWord_6811194 prefixEnd_6811194 3497416353019929405850895 := by
  unfold tailWord_6811194
  simp only [CollatzResearch.WordTrace]
  refine ⟨62106163521553718042126159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165616436057476581445669757 62106163521553718042126159)
  ·
    refine ⟨93159245282330577063189239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62106163521553718042126159 93159245282330577063189239)
    ·
      refine ⟨139738867923495865594783859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93159245282330577063189239 139738867923495865594783859)
      ·
        refine ⟨209608301885243798392175789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139738867923495865594783859 209608301885243798392175789)
        ·
          refine ⟨78603113206966424397065921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209608301885243798392175789 78603113206966424397065921)
          ·
            refine ⟨58952334905224818297799441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78603113206966424397065921 58952334905224818297799441)
            ·
              refine ⟨44214251178918613723349581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58952334905224818297799441 44214251178918613723349581)
              ·
                refine ⟨16580344192094480146256093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44214251178918613723349581 16580344192094480146256093)
                ·
                  refine ⟨6217629072035430054846035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16580344192094480146256093 6217629072035430054846035)
                  ·
                    refine ⟨9326443608053145082269053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6217629072035430054846035 9326443608053145082269053)
                    ·
                      refine ⟨3497416353019929405850895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9326443608053145082269053 3497416353019929405850895)
                      ·
                        rfl

theorem cell23_6811194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_6811194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811194 prefixEnd_6811194 := by exact prefixLift 6811194
  have htrace : WordTrace (prefixWord ++ tailWord_6811194) baseStart_6811194 baseEnd_6811194 := by
    simpa [prefixWord, tailWord_6811194, baseEnd_6811194] using wordTrace_append hprefix tailTrace_6811194
  have hstable : (prefixWord ++ tailWord_6811194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811194).length < 2 ^ (prefixWord ++ tailWord_6811194).sum := by decide
  have hdescent : baseEnd_6811194 < baseStart_6811194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811217 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 3, 1, 4]
def baseStart_6811217 : Nat := 118140960795 + 6811217 * 2 ^ 59
def prefixEnd_6811217 : Nat := 4983230072969 + 3 ^ 40 * 6811217 * 2
def baseEnd_6811217 : Nat := 3497428163074982815863289

theorem tailTrace_6811217 : CollatzResearch.WordTrace tailWord_6811217 prefixEnd_6811217 3497428163074982815863289 := by
  unfold tailWord_6811217
  simp only [CollatzResearch.WordTrace]
  refine ⟨248425492965131547096591905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165616995310087698064394603 248425492965131547096591905)
  ·
    refine ⟨186319119723848660322443929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248425492965131547096591905 186319119723848660322443929)
    ·
      refine ⟨139739339792886495241832947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186319119723848660322443929 139739339792886495241832947)
      ·
        refine ⟨209609009689329742862749421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139739339792886495241832947 209609009689329742862749421)
        ·
          refine ⟨78603378633498653573531033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209609009689329742862749421 78603378633498653573531033)
          ·
            refine ⟨58952533975123990180148275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78603378633498653573531033 58952533975123990180148275)
            ·
              refine ⟨88428800962685985270222413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58952533975123990180148275 88428800962685985270222413)
              ·
                refine ⟨33160800361007244476333405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88428800962685985270222413 33160800361007244476333405)
                ·
                  refine ⟨12435300135377716678625027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33160800361007244476333405 12435300135377716678625027)
                  ·
                    refine ⟨18652950203066575017937541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12435300135377716678625027 18652950203066575017937541)
                    ·
                      refine ⟨3497428163074982815863289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18652950203066575017937541 3497428163074982815863289)
                      ·
                        rfl

theorem cell23_6811217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_6811217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811217 prefixEnd_6811217 := by exact prefixLift 6811217
  have htrace : WordTrace (prefixWord ++ tailWord_6811217) baseStart_6811217 baseEnd_6811217 := by
    simpa [prefixWord, tailWord_6811217, baseEnd_6811217] using wordTrace_append hprefix tailTrace_6811217
  have hstable : (prefixWord ++ tailWord_6811217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811217).length < 2 ^ (prefixWord ++ tailWord_6811217).sum := by decide
  have hdescent : baseEnd_6811217 < baseStart_6811217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811222 : List Nat := [5, 2, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_6811222 : Nat := 118140960795 + 6811222 * 2 ^ 59
def prefixEnd_6811222 : Nat := 4983230072969 + 3 ^ 40 * 6811222 * 2
def baseEnd_6811222 : Nat := 1165810243492751765433589

theorem tailTrace_6811222 : CollatzResearch.WordTrace tailWord_6811222 prefixEnd_6811222 1165810243492751765433589 := by
  unfold tailWord_6811222
  simp only [CollatzResearch.WordTrace]
  refine ⟨15526604708132089559407745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165617116886742288633682613 15526604708132089559407745)
  ·
    refine ⟨11644953531099067169555809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15526604708132089559407745 11644953531099067169555809)
    ·
      refine ⟨8733715148324300377166857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11644953531099067169555809 8733715148324300377166857)
      ·
        refine ⟨6550286361243225282875143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8733715148324300377166857 6550286361243225282875143)
        ·
          refine ⟨9825429541864837924312715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6550286361243225282875143 9825429541864837924312715)
          ·
            refine ⟨14738144312797256886469073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9825429541864837924312715 14738144312797256886469073)
            ·
              refine ⟨11053608234597942664851805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14738144312797256886469073 11053608234597942664851805)
              ·
                refine ⟨4145103087974228499319427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11053608234597942664851805 4145103087974228499319427)
                ·
                  refine ⟨6217654631961342748979141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4145103087974228499319427 6217654631961342748979141)
                  ·
                    refine ⟨1165810243492751765433589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6217654631961342748979141 1165810243492751765433589)
                    ·
                      rfl

theorem cell23_6811222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_6811222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811222 prefixEnd_6811222 := by exact prefixLift 6811222
  have htrace : WordTrace (prefixWord ++ tailWord_6811222) baseStart_6811222 baseEnd_6811222 := by
    simpa [prefixWord, tailWord_6811222, baseEnd_6811222] using wordTrace_append hprefix tailTrace_6811222
  have hstable : (prefixWord ++ tailWord_6811222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811222).length < 2 ^ (prefixWord ++ tailWord_6811222).sum := by decide
  have hdescent : baseEnd_6811222 < baseStart_6811222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811228 : List Nat := [2, 2, 4, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_6811228 : Nat := 118140960795 + 6811228 * 2 ^ 59
def prefixEnd_6811228 : Nat := 4983230072969 + 3 ^ 40 * 6811228 * 2
def baseEnd_6811228 : Nat := 3497433811362182272825739

theorem tailTrace_6811228 : CollatzResearch.WordTrace tailWord_6811228 prefixEnd_6811228 3497433811362182272825739 := by
  unfold tailWord_6811228
  simp only [CollatzResearch.WordTrace]
  refine ⟨124212947084045847987621169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165617262778727797316828225 124212947084045847987621169)
  ·
    refine ⟨93159710313034385990715877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124212947084045847987621169 93159710313034385990715877)
    ·
      refine ⟨17467445683693947373259227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93159710313034385990715877 17467445683693947373259227)
      ·
        refine ⟨26201168525540921059888841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17467445683693947373259227 26201168525540921059888841)
        ·
          refine ⟨19650876394155690794916631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26201168525540921059888841 19650876394155690794916631)
          ·
            refine ⟨29476314591233536192374947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19650876394155690794916631 29476314591233536192374947)
            ·
              refine ⟨44214471886850304288562421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29476314591233536192374947 44214471886850304288562421)
              ·
                refine ⟨4145106739392216027052727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44214471886850304288562421 4145106739392216027052727)
                ·
                  refine ⟨6217660109088324040579091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4145106739392216027052727 6217660109088324040579091)
                  ·
                    refine ⟨9326490163632486060868637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6217660109088324040579091 9326490163632486060868637)
                    ·
                      refine ⟨3497433811362182272825739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9326490163632486060868637 3497433811362182272825739)
                      ·
                        rfl

theorem cell23_6811228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_6811228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811228 prefixEnd_6811228 := by exact prefixLift 6811228
  have htrace : WordTrace (prefixWord ++ tailWord_6811228) baseStart_6811228 baseEnd_6811228 := by
    simpa [prefixWord, tailWord_6811228, baseEnd_6811228] using wordTrace_append hprefix tailTrace_6811228
  have hstable : (prefixWord ++ tailWord_6811228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811228).length < 2 ^ (prefixWord ++ tailWord_6811228).sum := by decide
  have hdescent : baseEnd_6811228 < baseStart_6811228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811254 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_6811254 : Nat := 118140960795 + 6811254 * 2 ^ 59
def prefixEnd_6811254 : Nat := 4983230072969 + 3 ^ 40 * 6811254 * 2
def baseEnd_6811254 : Nat := 3497447161859199171100619

theorem tailTrace_6811254 : CollatzResearch.WordTrace tailWord_6811254 prefixEnd_6811254 3497447161859199171100619 := by
  unfold tailWord_6811254
  simp only [CollatzResearch.WordTrace]
  refine ⟨15526677654124843900980551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165617894977331668277125877 15526677654124843900980551)
  ·
    refine ⟨23290016481187265851470827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15526677654124843900980551 23290016481187265851470827)
    ·
      refine ⟨34935024721780898777206241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23290016481187265851470827 34935024721780898777206241)
      ·
        refine ⟨26201268541335674082904681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34935024721780898777206241 26201268541335674082904681)
        ·
          refine ⟨19650951406001755562178511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26201268541335674082904681 19650951406001755562178511)
          ·
            refine ⟨29476427109002633343267767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19650951406001755562178511 29476427109002633343267767)
            ·
              refine ⟨44214640663503950014901651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29476427109002633343267767 44214640663503950014901651)
              ·
                refine ⟨66321960995255925022352477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44214640663503950014901651 66321960995255925022352477)
                ·
                  refine ⟨24870735373220971883382179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66321960995255925022352477 24870735373220971883382179)
                  ·
                    refine ⟨37306103059831457825073269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24870735373220971883382179 37306103059831457825073269)
                    ·
                      refine ⟨3497447161859199171100619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37306103059831457825073269 3497447161859199171100619)
                      ·
                        rfl

theorem cell23_6811254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_6811254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811254 prefixEnd_6811254 := by exact prefixLift 6811254
  have htrace : WordTrace (prefixWord ++ tailWord_6811254) baseStart_6811254 baseEnd_6811254 := by
    simpa [prefixWord, tailWord_6811254, baseEnd_6811254] using wordTrace_append hprefix tailTrace_6811254
  have hstable : (prefixWord ++ tailWord_6811254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811254).length < 2 ^ (prefixWord ++ tailWord_6811254).sum := by decide
  have hdescent : baseEnd_6811254 < baseStart_6811254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811271 : List Nat := [1, 1, 4, 2, 1, 4, 2, 2, 1, 2, 3]
def baseStart_6811271 : Nat := 118140960795 + 6811271 * 2 ^ 59
def prefixEnd_6811271 : Nat := 4983230072969 + 3 ^ 40 * 6811271 * 2
def baseEnd_6811271 : Nat := 3497455891030325604588041

theorem tailTrace_6811271 : CollatzResearch.WordTrace tailWord_6811271 prefixEnd_6811271 3497455891030325604588041 := by
  unfold tailWord_6811271
  simp only [CollatzResearch.WordTrace]
  refine ⟨248427462506935914319057667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165618308337957276212705111 248427462506935914319057667)
  ·
    refine ⟨372641193760403871478586501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248427462506935914319057667 372641193760403871478586501)
    ·
      refine ⟨69870223830075725902234969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372641193760403871478586501 69870223830075725902234969)
      ·
        refine ⟨52402667872556794426676227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69870223830075725902234969 52402667872556794426676227)
        ·
          refine ⟨78604001808835191640014341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52402667872556794426676227 78604001808835191640014341)
          ·
            refine ⟨14738250339156598432502689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78604001808835191640014341 14738250339156598432502689)
            ·
              refine ⟨11053687754367448824377017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14738250339156598432502689 11053687754367448824377017)
              ·
                refine ⟨8290265815775586618282763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11053687754367448824377017 8290265815775586618282763)
                ·
                  refine ⟨12435398723663379927424145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8290265815775586618282763 12435398723663379927424145)
                  ·
                    refine ⟨9326549042747534945568109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12435398723663379927424145 9326549042747534945568109)
                    ·
                      refine ⟨3497455891030325604588041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9326549042747534945568109 3497455891030325604588041)
                      ·
                        rfl

theorem cell23_6811271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_6811271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811271 prefixEnd_6811271 := by exact prefixLift 6811271
  have htrace : WordTrace (prefixWord ++ tailWord_6811271) baseStart_6811271 baseEnd_6811271 := by
    simpa [prefixWord, tailWord_6811271, baseEnd_6811271] using wordTrace_append hprefix tailTrace_6811271
  have hstable : (prefixWord ++ tailWord_6811271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811271).length < 2 ^ (prefixWord ++ tailWord_6811271).sum := by decide
  have hdescent : baseEnd_6811271 < baseStart_6811271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811274 : List Nat := [3, 1, 2, 3, 2, 1, 4, 7]
def baseStart_6811274 : Nat := 118140960795 + 6811274 * 2 ^ 59
def prefixEnd_6811274 : Nat := 4983230072969 + 3 ^ 40 * 6811274 * 2
def baseEnd_6811274 : Nat := 129535460424899596031501

theorem tailTrace_6811274 : CollatzResearch.WordTrace tailWord_6811274 prefixEnd_6811274 129535460424899596031501 := by
  unfold tailWord_6811274
  simp only [CollatzResearch.WordTrace]
  refine ⟨62106892981481261457854219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165618381283950030554277917 62106892981481261457854219)
  ·
    refine ⟨93160339472221892186781329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62106892981481261457854219 93160339472221892186781329)
    ·
      refine ⟨69870254604166419140085997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93160339472221892186781329 69870254604166419140085997)
      ·
        refine ⟨26201345476562407177532249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69870254604166419140085997 26201345476562407177532249)
        ·
          refine ⟨19651009107421805383149187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26201345476562407177532249 19651009107421805383149187)
          ·
            refine ⟨29476513661132708074723781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19651009107421805383149187 29476513661132708074723781)
            ·
              refine ⟨5526846311462382764010709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29476513661132708074723781 5526846311462382764010709)
              ·
                refine ⟨129535460424899596031501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5526846311462382764010709 129535460424899596031501)
                ·
                  rfl

theorem cell23_6811274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 7].length) (baseStart_6811274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811274 prefixEnd_6811274 := by exact prefixLift 6811274
  have htrace : WordTrace (prefixWord ++ tailWord_6811274) baseStart_6811274 baseEnd_6811274 := by
    simpa [prefixWord, tailWord_6811274, baseEnd_6811274] using wordTrace_append hprefix tailTrace_6811274
  have hstable : (prefixWord ++ tailWord_6811274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811274).length < 2 ^ (prefixWord ++ tailWord_6811274).sum := by decide
  have hdescent : baseEnd_6811274 < baseStart_6811274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811327 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 5]
def baseStart_6811327 : Nat := 118140960795 + 6811327 * 2 ^ 59
def prefixEnd_6811327 : Nat := 4983230072969 + 3 ^ 40 * 6811327 * 2
def baseEnd_6811327 : Nat := 3497484645946977385487783

theorem tailTrace_6811327 : CollatzResearch.WordTrace tailWord_6811327 prefixEnd_6811327 3497484645946977385487783 := by
  unfold tailWord_6811327
  simp only [CollatzResearch.WordTrace]
  refine ⟨248429504994733035883096235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165619669996488690588730823 248429504994733035883096235)
  ·
    refine ⟨372644257492099553824644353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248429504994733035883096235 372644257492099553824644353)
    ·
      refine ⟨279483193119074665368483265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372644257492099553824644353 279483193119074665368483265)
      ·
        refine ⟨209612394839305999026362449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279483193119074665368483265 209612394839305999026362449)
        ·
          refine ⟨157209296129479499269771837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209612394839305999026362449 157209296129479499269771837)
          ·
            refine ⟨58953486048554812226164439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157209296129479499269771837 58953486048554812226164439)
            ·
              refine ⟨88430229072832218339246659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58953486048554812226164439 88430229072832218339246659)
              ·
                refine ⟨132645343609248327508869989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88430229072832218339246659 132645343609248327508869989)
                ·
                  refine ⟨24871001926734061407913123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132645343609248327508869989 24871001926734061407913123)
                  ·
                    refine ⟨37306502890101092111869685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24871001926734061407913123 37306502890101092111869685)
                    ·
                      refine ⟨3497484645946977385487783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37306502890101092111869685 3497484645946977385487783)
                      ·
                        rfl

theorem cell23_6811327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_6811327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811327 prefixEnd_6811327 := by exact prefixLift 6811327
  have htrace : WordTrace (prefixWord ++ tailWord_6811327) baseStart_6811327 baseEnd_6811327 := by
    simpa [prefixWord, tailWord_6811327, baseEnd_6811327] using wordTrace_append hprefix tailTrace_6811327
  have hstable : (prefixWord ++ tailWord_6811327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811327).length < 2 ^ (prefixWord ++ tailWord_6811327).sum := by decide
  have hdescent : baseEnd_6811327 < baseStart_6811327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811387 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 5]
def baseStart_6811387 : Nat := 118140960795 + 6811387 * 2 ^ 59
def prefixEnd_6811387 : Nat := 4983230072969 + 3 ^ 40 * 6811387 * 2
def baseEnd_6811387 : Nat := 3497515454786247150737507

theorem tailTrace_6811387 : CollatzResearch.WordTrace tailWord_6811387 prefixEnd_6811387 3497515454786247150737507 := by
  unfold tailWord_6811387
  simp only [CollatzResearch.WordTrace]
  refine ⟨248431693374515666130280415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165621128916343777420186943 248431693374515666130280415)
  ·
    refine ⟨372647540061773499195420623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248431693374515666130280415 372647540061773499195420623)
    ·
      refine ⟨558971310092660248793130935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372647540061773499195420623 558971310092660248793130935)
      ·
        refine ⟨838456965138990373189696403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558971310092660248793130935 838456965138990373189696403)
        ·
          refine ⟨1257685447708485559784544605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838456965138990373189696403 1257685447708485559784544605)
          ·
            refine ⟨471632042890682084919204227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1257685447708485559784544605 471632042890682084919204227)
            ·
              refine ⟨707448064336023127378806341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471632042890682084919204227 707448064336023127378806341)
              ·
                refine ⟨132646512063004336383526189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 707448064336023127378806341 132646512063004336383526189)
                ·
                  refine ⟨49742442023626626143822321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132646512063004336383526189 49742442023626626143822321)
                  ·
                    refine ⟨37306831517719969607866741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49742442023626626143822321 37306831517719969607866741)
                    ·
                      refine ⟨3497515454786247150737507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37306831517719969607866741 3497515454786247150737507)
                      ·
                        rfl

theorem cell23_6811387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 5].length) (baseStart_6811387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811387 prefixEnd_6811387 := by exact prefixLift 6811387
  have htrace : WordTrace (prefixWord ++ tailWord_6811387) baseStart_6811387 baseEnd_6811387 := by
    simpa [prefixWord, tailWord_6811387, baseEnd_6811387] using wordTrace_append hprefix tailTrace_6811387
  have hstable : (prefixWord ++ tailWord_6811387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811387).length < 2 ^ (prefixWord ++ tailWord_6811387).sum := by decide
  have hdescent : baseEnd_6811387 < baseStart_6811387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811441 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 3, 4]
def baseStart_6811441 : Nat := 118140960795 + 6811441 * 2 ^ 59
def prefixEnd_6811441 : Nat := 4983230072969 + 3 ^ 40 * 6811441 * 2
def baseEnd_6811441 : Nat := 1165847727580529979820753

theorem tailTrace_6811441 : CollatzResearch.WordTrace tailWord_6811441 prefixEnd_6811441 1165847727580529979820753 := by
  unfold tailWord_6811441
  simp only [CollatzResearch.WordTrace]
  refine ⟨248433662916320033352746177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165622441944213355568497451 248433662916320033352746177)
  ·
    refine ⟨186325247187240025014559633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248433662916320033352746177 186325247187240025014559633)
    ·
      refine ⟨139743935390430018760919725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186325247187240025014559633 139743935390430018760919725)
      ·
        refine ⟨52403975771411257035344897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139743935390430018760919725 52403975771411257035344897)
        ·
          refine ⟨39302981828558442776508673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52403975771411257035344897 39302981828558442776508673)
          ·
            refine ⟨29477236371418832082381505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39302981828558442776508673 29477236371418832082381505)
            ·
              refine ⟨22107927278564124061786129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29477236371418832082381505 22107927278564124061786129)
              ·
                refine ⟨16580945458923093046339597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22107927278564124061786129 16580945458923093046339597)
                ·
                  refine ⟨6217854547096159892377349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16580945458923093046339597 6217854547096159892377349)
                  ·
                    refine ⟨1165847727580529979820753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6217854547096159892377349 1165847727580529979820753)
                    ·
                      rfl

theorem cell23_6811441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_6811441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811441 prefixEnd_6811441 := by exact prefixLift 6811441
  have htrace : WordTrace (prefixWord ++ tailWord_6811441) baseStart_6811441 baseEnd_6811441 := by
    simpa [prefixWord, tailWord_6811441, baseEnd_6811441] using wordTrace_append hprefix tailTrace_6811441
  have hstable : (prefixWord ++ tailWord_6811441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811441).length < 2 ^ (prefixWord ++ tailWord_6811441).sum := by decide
  have hdescent : baseEnd_6811441 < baseStart_6811441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811468 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 2, 2, 3]
def baseStart_6811468 : Nat := 118140960795 + 6811468 * 2 ^ 59
def prefixEnd_6811468 : Nat := 4983230072969 + 3 ^ 40 * 6811468 * 2
def baseEnd_6811468 : Nat := 3497557046719261333824635

theorem tailTrace_6811468 : CollatzResearch.WordTrace tailWord_6811468 prefixEnd_6811468 3497557046719261333824635 := by
  unfold tailWord_6811468
  simp only [CollatzResearch.WordTrace]
  refine ⟨124217323843611108481989529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165623098458148144642652705 124217323843611108481989529)
  ·
    refine ⟨93162992882708331361492147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124217323843611108481989529 93162992882708331361492147)
    ·
      refine ⟨139744489324062497042238221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93162992882708331361492147 139744489324062497042238221)
      ·
        refine ⟨52404183496523436390839333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139744489324062497042238221 52404183496523436390839333)
        ·
          refine ⟨9825784405598144323282375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52404183496523436390839333 9825784405598144323282375)
          ·
            refine ⟨14738676608397216484923563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9825784405598144323282375 14738676608397216484923563)
            ·
              refine ⟨22108014912595824727385345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14738676608397216484923563 22108014912595824727385345)
              ·
                refine ⟨16581011184446868545539009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22108014912595824727385345 16581011184446868545539009)
                ·
                  refine ⟨12435758388335151409154257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16581011184446868545539009 12435758388335151409154257)
                  ·
                    refine ⟨9326818791251363556865693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12435758388335151409154257 9326818791251363556865693)
                    ·
                      refine ⟨3497557046719261333824635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9326818791251363556865693 3497557046719261333824635)
                      ·
                        rfl

theorem cell23_6811468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_6811468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811468 prefixEnd_6811468 := by exact prefixLift 6811468
  have htrace : WordTrace (prefixWord ++ tailWord_6811468) baseStart_6811468 baseEnd_6811468 := by
    simpa [prefixWord, tailWord_6811468, baseEnd_6811468] using wordTrace_append hprefix tailTrace_6811468
  have hstable : (prefixWord ++ tailWord_6811468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811468).length < 2 ^ (prefixWord ++ tailWord_6811468).sum := by decide
  have hdescent : baseEnd_6811468 < baseStart_6811468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811488 : List Nat := [2, 1, 1, 3, 3, 4, 2, 1, 6]
def baseStart_6811488 : Nat := 118140960795 + 6811488 * 2 ^ 59
def prefixEnd_6811488 : Nat := 4983230072969 + 3 ^ 40 * 6811488 * 2
def baseEnd_6811488 : Nat := 388618590703594583952727

theorem tailTrace_6811488 : CollatzResearch.WordTrace tailWord_6811488 prefixEnd_6811488 388618590703594583952727 := by
  unfold tailWord_6811488
  simp only [CollatzResearch.WordTrace]
  refine ⟨124217688573574880189853559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165623584764766506919804745 124217688573574880189853559)
  ·
    refine ⟨186326532860362320284780339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124217688573574880189853559 186326532860362320284780339)
    ·
      refine ⟨279489799290543480427170509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186326532860362320284780339 279489799290543480427170509)
      ·
        refine ⟨104808674733953805160188941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279489799290543480427170509 104808674733953805160188941)
        ·
          refine ⟨39303253025232676935070853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104808674733953805160188941 39303253025232676935070853)
          ·
            refine ⟨7369359942231126925325785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39303253025232676935070853 7369359942231126925325785)
            ·
              refine ⟨5527019956673345193994339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7369359942231126925325785 5527019956673345193994339)
              ·
                refine ⟨8290529935010017790991509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5527019956673345193994339 8290529935010017790991509)
                ·
                  refine ⟨388618590703594583952727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8290529935010017790991509 388618590703594583952727)
                  ·
                    rfl

theorem cell23_6811488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 6].length) (baseStart_6811488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811488 prefixEnd_6811488 := by exact prefixLift 6811488
  have htrace : WordTrace (prefixWord ++ tailWord_6811488) baseStart_6811488 baseEnd_6811488 := by
    simpa [prefixWord, tailWord_6811488, baseEnd_6811488] using wordTrace_append hprefix tailTrace_6811488
  have hstable : (prefixWord ++ tailWord_6811488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811488).length < 2 ^ (prefixWord ++ tailWord_6811488).sum := by decide
  have hdescent : baseEnd_6811488 < baseStart_6811488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811514 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 3, 6]
def baseStart_6811514 : Nat := 118140960795 + 6811514 * 2 ^ 59
def prefixEnd_6811514 : Nat := 4983230072969 + 3 ^ 40 * 6811514 * 2
def baseEnd_6811514 : Nat := 1165860222276456051283141

theorem tailTrace_6811514 : CollatzResearch.WordTrace tailWord_6811514 prefixEnd_6811514 1165860222276456051283141 := by
  unfold tailWord_6811514
  simp only [CollatzResearch.WordTrace]
  refine ⟨62109081361263891705038399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165624216963370377880102397 62109081361263891705038399)
  ·
    refine ⟨93163622041895837557557599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62109081361263891705038399 93163622041895837557557599)
    ·
      refine ⟨139745433062843756336336399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93163622041895837557557599 139745433062843756336336399)
      ·
        refine ⟨209618149594265634504504599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139745433062843756336336399 209618149594265634504504599)
        ·
          refine ⟨314427224391398451756756899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209618149594265634504504599 314427224391398451756756899)
          ·
            refine ⟨471640836587097677635135349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314427224391398451756756899 471640836587097677635135349)
            ·
              refine ⟨44216328430040407278293939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 471640836587097677635135349 44216328430040407278293939)
              ·
                refine ⟨66324492645060610917440909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44216328430040407278293939 66324492645060610917440909)
                ·
                  refine ⟨24871684741897729094040341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66324492645060610917440909 24871684741897729094040341)
                  ·
                    refine ⟨1165860222276456051283141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24871684741897729094040341 1165860222276456051283141)
                    ·
                      rfl

theorem cell23_6811514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_6811514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811514 prefixEnd_6811514 := by exact prefixLift 6811514
  have htrace : WordTrace (prefixWord ++ tailWord_6811514) baseStart_6811514 baseEnd_6811514 := by
    simpa [prefixWord, tailWord_6811514, baseEnd_6811514] using wordTrace_append hprefix tailTrace_6811514
  have hstable : (prefixWord ++ tailWord_6811514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811514).length < 2 ^ (prefixWord ++ tailWord_6811514).sum := by decide
  have hdescent : baseEnd_6811514 < baseStart_6811514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811538 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_6811538 : Nat := 118140960795 + 6811538 * 2 ^ 59
def prefixEnd_6811538 : Nat := 4983230072969 + 3 ^ 40 * 6811538 * 2
def baseEnd_6811538 : Nat := 3497592990365076059949313

theorem tailTrace_6811538 : CollatzResearch.WordTrace tailWord_6811538 prefixEnd_6811538 3497592990365076059949313 := by
  unfold tailWord_6811538
  simp only [CollatzResearch.WordTrace]
  refine ⟨62109300199242154729756817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165624800531312412612684845 62109300199242154729756817)
  ·
    refine ⟨46581975149431616047317613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62109300199242154729756817 46581975149431616047317613)
    ·
      refine ⟨17468240681036856017744105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46581975149431616047317613 17468240681036856017744105)
      ·
        refine ⟨13101180510777642013308079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17468240681036856017744105 13101180510777642013308079)
        ·
          refine ⟨19651770766166463019962119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13101180510777642013308079 19651770766166463019962119)
          ·
            refine ⟨29477656149249694529943179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19651770766166463019962119 29477656149249694529943179)
            ·
              refine ⟨44216484223874541794914769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29477656149249694529943179 44216484223874541794914769)
              ·
                refine ⟨33162363167905906346186077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44216484223874541794914769 33162363167905906346186077)
                ·
                  refine ⟨12435886187964714879819779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33162363167905906346186077 12435886187964714879819779)
                  ·
                    refine ⟨18653829281947072319729669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12435886187964714879819779 18653829281947072319729669)
                    ·
                      refine ⟨3497592990365076059949313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18653829281947072319729669 3497592990365076059949313)
                      ·
                        rfl

theorem cell23_6811538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_6811538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811538 prefixEnd_6811538 := by exact prefixLift 6811538
  have htrace : WordTrace (prefixWord ++ tailWord_6811538) baseStart_6811538 baseEnd_6811538 := by
    simpa [prefixWord, tailWord_6811538, baseEnd_6811538] using wordTrace_append hprefix tailTrace_6811538
  have hstable : (prefixWord ++ tailWord_6811538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811538).length < 2 ^ (prefixWord ++ tailWord_6811538).sum := by decide
  have hdescent : baseEnd_6811538 < baseStart_6811538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
