import V185TrunkScan23Chunk0473

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2803151 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 3]
def baseStart_2803151 : Nat := 118140960795 + 2803151 * 2 ^ 59
def prefixEnd_2803151 : Nat := 4983230072969 + 3 ^ 40 * 2803151 * 2
def baseEnd_2803151 : Nat := 1439363810131467392521049

theorem tailTrace_2803151 : CollatzResearch.WordTrace tailWord_2803151 prefixEnd_2803151 1439363810131467392521049 := by
  unfold tailWord_2803151
  simp only [CollatzResearch.WordTrace]
  refine ⟨102239316267670141921465307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68159544178446761280976871 102239316267670141921465307)
  ·
    refine ⟨153358974401505212882197961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102239316267670141921465307 153358974401505212882197961)
    ·
      refine ⟨115019230801128909661648471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153358974401505212882197961 115019230801128909661648471)
      ·
        refine ⟨172528846201693364492472707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115019230801128909661648471 172528846201693364492472707)
        ·
          refine ⟨258793269302540046738709061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172528846201693364492472707 258793269302540046738709061)
          ·
            refine ⟨48523737994226258763507949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258793269302540046738709061 48523737994226258763507949)
            ·
              refine ⟨18196401747834847036315481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48523737994226258763507949 18196401747834847036315481)
              ·
                refine ⟨13647301310876135277236611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18196401747834847036315481 13647301310876135277236611)
                ·
                  refine ⟨20470951966314202915854917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13647301310876135277236611 20470951966314202915854917)
                  ·
                    refine ⟨3838303493683913046722797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20470951966314202915854917 3838303493683913046722797)
                    ·
                      refine ⟨1439363810131467392521049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3838303493683913046722797 1439363810131467392521049)
                      ·
                        rfl

theorem cell23_2803151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 3].length) (baseStart_2803151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803151 prefixEnd_2803151 := by exact prefixLift 2803151
  have htrace : WordTrace (prefixWord ++ tailWord_2803151) baseStart_2803151 baseEnd_2803151 := by
    simpa [prefixWord, tailWord_2803151, baseEnd_2803151] using wordTrace_append hprefix tailTrace_2803151
  have hstable : (prefixWord ++ tailWord_2803151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803151).length < 2 ^ (prefixWord ++ tailWord_2803151).sum := by decide
  have hdescent : baseEnd_2803151 < baseStart_2803151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803171 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 8]
def baseStart_2803171 : Nat := 118140960795 + 2803171 * 2 ^ 59
def prefixEnd_2803171 : Nat := 4983230072969 + 3 ^ 40 * 2803171 * 2
def baseEnd_2803171 : Nat := 159930453304950812696773

theorem tailTrace_2803171 : CollatzResearch.WordTrace tailWord_2803171 prefixEnd_2803171 159930453304950812696773 := by
  unfold tailWord_2803171
  simp only [CollatzResearch.WordTrace]
  refine ⟨102240045727597685337193367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68160030485065123558128911 102240045727597685337193367)
  ·
    refine ⟨153360068591396528005790051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102240045727597685337193367 153360068591396528005790051)
    ·
      refine ⟨230040102887094792008685077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153360068591396528005790051 230040102887094792008685077)
      ·
        refine ⟨10783129822832568375407113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 230040102887094792008685077 10783129822832568375407113)
        ·
          refine ⟨8087347367124426281555335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10783129822832568375407113 8087347367124426281555335)
          ·
            refine ⟨12131021050686639422333003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8087347367124426281555335 12131021050686639422333003)
            ·
              refine ⟨18196531576029959133499505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12131021050686639422333003 18196531576029959133499505)
              ·
                refine ⟨13647398682022469350124629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18196531576029959133499505 13647398682022469350124629)
                ·
                  refine ⟨159930453304950812696773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13647398682022469350124629 159930453304950812696773)
                  ·
                    rfl

theorem cell23_2803171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 8].length) (baseStart_2803171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803171 prefixEnd_2803171 := by exact prefixLift 2803171
  have htrace : WordTrace (prefixWord ++ tailWord_2803171) baseStart_2803171 baseEnd_2803171 := by
    simpa [prefixWord, tailWord_2803171, baseEnd_2803171] using wordTrace_append hprefix tailTrace_2803171
  have hstable : (prefixWord ++ tailWord_2803171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803171).length < 2 ^ (prefixWord ++ tailWord_2803171).sum := by decide
  have hdescent : baseEnd_2803171 < baseStart_2803171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803192 : List Nat := [2, 1, 2, 1, 1, 6, 3, 2, 1, 4]
def baseStart_2803192 : Nat := 118140960795 + 2803192 * 2 ^ 59
def prefixEnd_2803192 : Nat := 4983230072969 + 3 ^ 40 * 2803192 * 2
def baseEnd_2803192 : Nat := 479794954279433910702787

theorem tailTrace_2803192 : CollatzResearch.WordTrace tailWord_2803192 prefixEnd_2803192 479794954279433910702787 := by
  unfold tailWord_2803192
  simp only [CollatzResearch.WordTrace]
  refine ⟨51120405830260802961853915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68160541107014403949138553 51120405830260802961853915)
  ·
    refine ⟨76680608745391204442780873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51120405830260802961853915 76680608745391204442780873)
    ·
      refine ⟨57510456559043403332085655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76680608745391204442780873 57510456559043403332085655)
      ·
        refine ⟨86265684838565104998128483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57510456559043403332085655 86265684838565104998128483)
        ·
          refine ⟨129398527257847657497192725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86265684838565104998128483 129398527257847657497192725)
          ·
            refine ⟨6065555965211608945180909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129398527257847657497192725 6065555965211608945180909)
            ·
              refine ⟨2274583486954353354442841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6065555965211608945180909 2274583486954353354442841)
              ·
                refine ⟨1705937615215765015832131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2274583486954353354442841 1705937615215765015832131)
                ·
                  refine ⟨2558906422823647523748197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705937615215765015832131 2558906422823647523748197)
                  ·
                    refine ⟨479794954279433910702787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2558906422823647523748197 479794954279433910702787)
                    ·
                      rfl

theorem cell23_2803192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 1, 4].length) (baseStart_2803192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803192 prefixEnd_2803192 := by exact prefixLift 2803192
  have htrace : WordTrace (prefixWord ++ tailWord_2803192) baseStart_2803192 baseEnd_2803192 := by
    simpa [prefixWord, tailWord_2803192, baseEnd_2803192] using wordTrace_append hprefix tailTrace_2803192
  have hstable : (prefixWord ++ tailWord_2803192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803192).length < 2 ^ (prefixWord ++ tailWord_2803192).sum := by decide
  have hdescent : baseEnd_2803192 < baseStart_2803192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803208 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 3, 5, 2]
def baseStart_2803208 : Nat := 118140960795 + 2803208 * 2 ^ 59
def prefixEnd_2803208 : Nat := 4983230072969 + 3 ^ 40 * 2803208 * 2
def baseEnd_2803208 : Nat := 1439393078528773669508287

theorem tailTrace_2803208 : CollatzResearch.WordTrace tailWord_2803208 prefixEnd_2803208 1439393078528773669508287 := by
  unfold tailWord_2803208
  simp only [CollatzResearch.WordTrace]
  refine ⟨51120697614231820328145139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68160930152309093770860185 51120697614231820328145139)
  ·
    refine ⟨76681046421347730492217709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51120697614231820328145139 76681046421347730492217709)
    ·
      refine ⟨28755392408005398934581641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76681046421347730492217709 28755392408005398934581641)
      ·
        refine ⟨21566544306004049200936231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28755392408005398934581641 21566544306004049200936231)
        ·
          refine ⟨32349816459006073801404347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21566544306004049200936231 32349816459006073801404347)
          ·
            refine ⟨48524724688509110702106521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32349816459006073801404347 48524724688509110702106521)
            ·
              refine ⟨36393543516381833026579891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48524724688509110702106521 36393543516381833026579891)
              ·
                refine ⟨54590315274572749539869837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36393543516381833026579891 54590315274572749539869837)
                ·
                  refine ⟨20471368227964781077451189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54590315274572749539869837 20471368227964781077451189)
                  ·
                    refine ⟨1919190771371698226011049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20471368227964781077451189 1919190771371698226011049)
                    ·
                      refine ⟨1439393078528773669508287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919190771371698226011049 1439393078528773669508287)
                      ·
                        rfl

theorem cell23_2803208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_2803208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803208 prefixEnd_2803208 := by exact prefixLift 2803208
  have htrace : WordTrace (prefixWord ++ tailWord_2803208) baseStart_2803208 baseEnd_2803208 := by
    simpa [prefixWord, tailWord_2803208, baseEnd_2803208] using wordTrace_append hprefix tailTrace_2803208
  have hstable : (prefixWord ++ tailWord_2803208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803208).length < 2 ^ (prefixWord ++ tailWord_2803208).sum := by decide
  have hdescent : baseEnd_2803208 < baseStart_2803208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803231 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 3, 6]
def baseStart_2803231 : Nat := 118140960795 + 2803231 * 2 ^ 59
def prefixEnd_2803231 : Nat := 4983230072969 + 3 ^ 40 * 2803231 * 2
def baseEnd_2803231 : Nat := 479801629527942359840227

theorem tailTrace_2803231 : CollatzResearch.WordTrace tailWord_2803231 prefixEnd_2803231 479801629527942359840227 := by
  unfold tailWord_2803231
  simp only [CollatzResearch.WordTrace]
  refine ⟨102242234107380315584377547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68161489404920210389585031 102242234107380315584377547)
  ·
    refine ⟨153363351161070473376566321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102242234107380315584377547 153363351161070473376566321)
    ·
      refine ⟨115022513370802855032424741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153363351161070473376566321 115022513370802855032424741)
      ·
        refine ⟨21566721257025535318579639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115022513370802855032424741 21566721257025535318579639)
        ·
          refine ⟨32350081885538302977869459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21566721257025535318579639 32350081885538302977869459)
          ·
            refine ⟨48525122828307454466804189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32350081885538302977869459 48525122828307454466804189)
            ·
              refine ⟨18196921060615295425051571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48525122828307454466804189 18196921060615295425051571)
              ·
                refine ⟨27295381590922943137577357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18196921060615295425051571 27295381590922943137577357)
                ·
                  refine ⟨10235768096596103676591509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27295381590922943137577357 10235768096596103676591509)
                  ·
                    refine ⟨479801629527942359840227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10235768096596103676591509 479801629527942359840227)
                    ·
                      rfl

theorem cell23_2803231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 6].length) (baseStart_2803231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803231 prefixEnd_2803231 := by exact prefixLift 2803231
  have htrace : WordTrace (prefixWord ++ tailWord_2803231) baseStart_2803231 baseEnd_2803231 := by
    simpa [prefixWord, tailWord_2803231, baseEnd_2803231] using wordTrace_append hprefix tailTrace_2803231
  have hstable : (prefixWord ++ tailWord_2803231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803231).length < 2 ^ (prefixWord ++ tailWord_2803231).sum := by decide
  have hdescent : baseEnd_2803231 < baseStart_2803231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803258 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3]
def baseStart_2803258 : Nat := 118140960795 + 2803258 * 2 ^ 59
def prefixEnd_2803258 : Nat := 4983230072969 + 3 ^ 40 * 2803258 * 2
def baseEnd_2803258 : Nat := 1439418752561498473883057

theorem tailTrace_2803258 : CollatzResearch.WordTrace tailWord_2803258 prefixEnd_2803258 1439418752561498473883057 := by
  unfold tailWord_2803258
  simp only [CollatzResearch.WordTrace]
  refine ⟨25560804719570624798902607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68162145918854999463740285 25560804719570624798902607)
  ·
    refine ⟨38341207079355937198353911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25560804719570624798902607 38341207079355937198353911)
    ·
      refine ⟨57511810619033905797530867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38341207079355937198353911 57511810619033905797530867)
      ·
        refine ⟨86267715928550858696296301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57511810619033905797530867 86267715928550858696296301)
        ·
          refine ⟨32350393473206572011111113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86267715928550858696296301 32350393473206572011111113)
          ·
            refine ⟨24262795104904929008333335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32350393473206572011111113 24262795104904929008333335)
            ·
              refine ⟨36394192657357393512500003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24262795104904929008333335 36394192657357393512500003)
              ·
                refine ⟨54591288986036090268750005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36394192657357393512500003 54591288986036090268750005)
                ·
                  refine ⟨5117933342440883462695313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54591288986036090268750005 5117933342440883462695313)
                  ·
                    refine ⟨3838450006830662597021485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5117933342440883462695313 3838450006830662597021485)
                    ·
                      refine ⟨1439418752561498473883057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3838450006830662597021485 1439418752561498473883057)
                      ·
                        rfl

theorem cell23_2803258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_2803258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803258 prefixEnd_2803258 := by exact prefixLift 2803258
  have htrace : WordTrace (prefixWord ++ tailWord_2803258) baseStart_2803258 baseEnd_2803258 := by
    simpa [prefixWord, tailWord_2803258, baseEnd_2803258] using wordTrace_append hprefix tailTrace_2803258
  have hstable : (prefixWord ++ tailWord_2803258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803258).length < 2 ^ (prefixWord ++ tailWord_2803258).sum := by decide
  have hdescent : baseEnd_2803258 < baseStart_2803258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803265 : List Nat := [1, 2, 5, 1, 1, 1, 1, 5, 2, 4]
def baseStart_2803265 : Nat := 118140960795 + 2803265 * 2 ^ 59
def prefixEnd_2803265 : Nat := 4983230072969 + 3 ^ 40 * 2803265 * 2
def baseEnd_2803265 : Nat := 479807448975359982165175

theorem tailTrace_2803265 : CollatzResearch.WordTrace tailWord_2803265 prefixEnd_2803265 479807448975359982165175 := by
  unfold tailWord_2803265
  simp only [CollatzResearch.WordTrace]
  refine ⟨102243474189257139391115249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68162316126171426260743499 102243474189257139391115249)
  ·
    refine ⟨76682605641942854543336437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102243474189257139391115249 76682605641942854543336437)
    ·
      refine ⟨7188994278932142613437791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76682605641942854543336437 7188994278932142613437791)
      ·
        refine ⟨10783491418398213920156687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7188994278932142613437791 10783491418398213920156687)
        ·
          refine ⟨16175237127597320880235031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10783491418398213920156687 16175237127597320880235031)
          ·
            refine ⟨24262855691395981320352547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16175237127597320880235031 24262855691395981320352547)
            ·
              refine ⟨36394283537093971980528821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24262855691395981320352547 36394283537093971980528821)
              ·
                refine ⟨3411964081602559873174577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36394283537093971980528821 3411964081602559873174577)
                ·
                  refine ⟨2558973061201919904880933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3411964081602559873174577 2558973061201919904880933)
                  ·
                    refine ⟨479807448975359982165175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2558973061201919904880933 479807448975359982165175)
                    ·
                      rfl

theorem cell23_2803265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_2803265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803265 prefixEnd_2803265 := by exact prefixLift 2803265
  have htrace : WordTrace (prefixWord ++ tailWord_2803265) baseStart_2803265 baseEnd_2803265 := by
    simpa [prefixWord, tailWord_2803265, baseEnd_2803265] using wordTrace_append hprefix tailTrace_2803265
  have hstable : (prefixWord ++ tailWord_2803265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803265).length < 2 ^ (prefixWord ++ tailWord_2803265).sum := by decide
  have hdescent : baseEnd_2803265 < baseStart_2803265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803292 : List Nat := [2, 2, 4, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_2803292 : Nat := 118140960795 + 2803292 * 2 ^ 59
def prefixEnd_2803292 : Nat := 4983230072969 + 3 ^ 40 * 2803292 * 2
def baseEnd_2803292 : Nat := 1439436210903751340857901

theorem tailTrace_2803292 : CollatzResearch.WordTrace tailWord_2803292 prefixEnd_2803292 1439436210903751340857901 := by
  unfold tailWord_2803292
  simp only [CollatzResearch.WordTrace]
  refine ⟨51122229480079661501174065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68162972640106215334898753 51122229480079661501174065)
  ·
    refine ⟨38341672110059746125880549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51122229480079661501174065 38341672110059746125880549)
    ·
      refine ⟨7189063520636202398602603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38341672110059746125880549 7189063520636202398602603)
      ·
        refine ⟨10783595280954303597903905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7189063520636202398602603 10783595280954303597903905)
        ·
          refine ⟨8087696460715727698427929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10783595280954303597903905 8087696460715727698427929)
          ·
            refine ⟨6065772345536795773820947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8087696460715727698427929 6065772345536795773820947)
            ·
              refine ⟨9098658518305193660731421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6065772345536795773820947 9098658518305193660731421)
              ·
                refine ⟨3411996944364447622774283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9098658518305193660731421 3411996944364447622774283)
                ·
                  refine ⟨5117995416546671434161425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3411996944364447622774283 5117995416546671434161425)
                  ·
                    refine ⟨3838496562410003575621069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5117995416546671434161425 3838496562410003575621069)
                    ·
                      refine ⟨1439436210903751340857901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3838496562410003575621069 1439436210903751340857901)
                      ·
                        rfl

theorem cell23_2803292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_2803292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803292 prefixEnd_2803292 := by exact prefixLift 2803292
  have htrace : WordTrace (prefixWord ++ tailWord_2803292) baseStart_2803292 baseEnd_2803292 := by
    simpa [prefixWord, tailWord_2803292, baseEnd_2803292] using wordTrace_append hprefix tailTrace_2803292
  have hstable : (prefixWord ++ tailWord_2803292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803292).length < 2 ^ (prefixWord ++ tailWord_2803292).sum := by decide
  have hdescent : baseEnd_2803292 < baseStart_2803292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803382 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2803382 : Nat := 118140960795 + 2803382 * 2 ^ 59
def prefixEnd_2803382 : Nat := 4983230072969 + 3 ^ 40 * 2803382 * 2
def baseEnd_2803382 : Nat := 1439482424162655988732487

theorem tailTrace_2803382 : CollatzResearch.WordTrace tailWord_2803382 prefixEnd_2803382 1439482424162655988732487 := by
  unfold tailWord_2803382
  simp only [CollatzResearch.WordTrace]
  refine ⟨6390483845614579273320275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68165161019888845582082933 6390483845614579273320275)
  ·
    refine ⟨9585725768421868909980413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6390483845614579273320275 9585725768421868909980413)
    ·
      refine ⟨3594647163158200841242655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9585725768421868909980413 3594647163158200841242655)
      ·
        refine ⟨5391970744737301261863983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3594647163158200841242655 5391970744737301261863983)
        ·
          refine ⟨8087956117105951892795975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5391970744737301261863983 8087956117105951892795975)
          ·
            refine ⟨12131934175658927839193963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8087956117105951892795975 12131934175658927839193963)
            ·
              refine ⟨18197901263488391758790945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12131934175658927839193963 18197901263488391758790945)
              ·
                refine ⟨13648425947616293819093209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18197901263488391758790945 13648425947616293819093209)
                ·
                  refine ⟨10236319460712220364319907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13648425947616293819093209 10236319460712220364319907)
                  ·
                    refine ⟨15354479191068330546479861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10236319460712220364319907 15354479191068330546479861)
                    ·
                      refine ⟨1439482424162655988732487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15354479191068330546479861 1439482424162655988732487)
                      ·
                        rfl

theorem cell23_2803382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2803382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803382 prefixEnd_2803382 := by exact prefixLift 2803382
  have htrace : WordTrace (prefixWord ++ tailWord_2803382) baseStart_2803382 baseEnd_2803382 := by
    simpa [prefixWord, tailWord_2803382, baseEnd_2803382] using wordTrace_append hprefix tailTrace_2803382
  have hstable : (prefixWord ++ tailWord_2803382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803382).length < 2 ^ (prefixWord ++ tailWord_2803382).sum := by decide
  have hdescent : baseEnd_2803382 < baseStart_2803382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803435 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 1, 6, 2]
def baseStart_2803435 : Nat := 118140960795 + 2803435 * 2 ^ 59
def prefixEnd_2803435 : Nat := 4983230072969 + 3 ^ 40 * 2803435 * 2
def baseEnd_2803435 : Nat := 1439509638637344281369743

theorem tailTrace_2803435 : CollatzResearch.WordTrace tailWord_2803435 prefixEnd_2803435 1439509638637344281369743 := by
  unfold tailWord_2803435
  simp only [CollatzResearch.WordTrace]
  refine ⟨102249674598641258424803759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68166449732427505616535839 102249674598641258424803759)
  ·
    refine ⟨153374511897961887637205639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102249674598641258424803759 153374511897961887637205639)
    ·
      refine ⟨230061767846942831455808459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153374511897961887637205639 230061767846942831455808459)
      ·
        refine ⟨345092651770414247183712689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230061767846942831455808459 345092651770414247183712689)
        ·
          refine ⟨258819488827810685387784517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345092651770414247183712689 258819488827810685387784517)
          ·
            refine ⟨48528654155214503510209597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258819488827810685387784517 48528654155214503510209597)
            ·
              refine ⟨18198245308205438816328599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48528654155214503510209597 18198245308205438816328599)
              ·
                refine ⟨27297367962308158224492899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18198245308205438816328599 27297367962308158224492899)
                ·
                  refine ⟨40946051943462237336739349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27297367962308158224492899 40946051943462237336739349)
                  ·
                    refine ⟨1919346184849792375159657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40946051943462237336739349 1919346184849792375159657)
                    ·
                      refine ⟨1439509638637344281369743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919346184849792375159657 1439509638637344281369743)
                      ·
                        rfl

theorem cell23_2803435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 6, 2].length) (baseStart_2803435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803435 prefixEnd_2803435 := by exact prefixLift 2803435
  have htrace : WordTrace (prefixWord ++ tailWord_2803435) baseStart_2803435 baseEnd_2803435 := by
    simpa [prefixWord, tailWord_2803435, baseEnd_2803435] using wordTrace_append hprefix tailTrace_2803435
  have hstable : (prefixWord ++ tailWord_2803435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803435).length < 2 ^ (prefixWord ++ tailWord_2803435).sum := by decide
  have hdescent : baseEnd_2803435 < baseStart_2803435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803448 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 1, 6, 4]
def baseStart_2803448 : Nat := 118140960795 + 2803448 * 2 ^ 59
def prefixEnd_2803448 : Nat := 4983230072969 + 3 ^ 40 * 2803448 * 2
def baseEnd_2803448 : Nat := 1439516313885852730507183

theorem tailTrace_2803448 : CollatzResearch.WordTrace tailWord_2803448 prefixEnd_2803448 1439516313885852730507183 := by
  unfold tailWord_2803448
  simp only [CollatzResearch.WordTrace]
  refine ⟨51125074373797080822513499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68166765831729441096684665 51125074373797080822513499)
  ·
    refine ⟨76687611560695621233770249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51125074373797080822513499 76687611560695621233770249)
    ·
      refine ⟨57515708670521715925327687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76687611560695621233770249 57515708670521715925327687)
      ·
        refine ⟨86273563005782573887991531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57515708670521715925327687 86273563005782573887991531)
        ·
          refine ⟨129410344508673860831987297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86273563005782573887991531 129410344508673860831987297)
          ·
            refine ⟨97057758381505395623990473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129410344508673860831987297 97057758381505395623990473)
            ·
              refine ⟨72793318786129046717992855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97057758381505395623990473 72793318786129046717992855)
              ·
                refine ⟨109189978179193570076989283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72793318786129046717992855 109189978179193570076989283)
                ·
                  refine ⟨163784967268790355115483925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109189978179193570076989283 163784967268790355115483925)
                  ·
                    refine ⟨7677420340724547896038309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 163784967268790355115483925 7677420340724547896038309)
                    ·
                      refine ⟨1439516313885852730507183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7677420340724547896038309 1439516313885852730507183)
                      ·
                        rfl

theorem cell23_2803448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_2803448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803448 prefixEnd_2803448 := by exact prefixLift 2803448
  have htrace : WordTrace (prefixWord ++ tailWord_2803448) baseStart_2803448 baseEnd_2803448 := by
    simpa [prefixWord, tailWord_2803448, baseEnd_2803448] using wordTrace_append hprefix tailTrace_2803448
  have hstable : (prefixWord ++ tailWord_2803448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803448).length < 2 ^ (prefixWord ++ tailWord_2803448).sum := by decide
  have hdescent : baseEnd_2803448 < baseStart_2803448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803479 : List Nat := [1, 1, 3, 4, 2, 1, 2, 4, 1, 4]
def baseStart_2803479 : Nat := 118140960795 + 2803479 * 2 ^ 59
def prefixEnd_2803479 : Nat := 4983230072969 + 3 ^ 40 * 2803479 * 2
def baseEnd_2803479 : Nat := 479844077262047369739847

theorem tailTrace_2803479 : CollatzResearch.WordTrace tailWord_2803479 prefixEnd_2803479 479844077262047369739847 := by
  unfold tailWord_2803479
  simp only [CollatzResearch.WordTrace]
  refine ⟨102251279410481853939405491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68167519606987902626270327 102251279410481853939405491)
  ·
    refine ⟨153376919115722780909108237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102251279410481853939405491 153376919115722780909108237)
    ·
      refine ⟨57516344668396042840915589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153376919115722780909108237 57516344668396042840915589)
      ·
        refine ⟨10784314625324258032671673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57516344668396042840915589 10784314625324258032671673)
        ·
          refine ⟨8088235968993193524503755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10784314625324258032671673 8088235968993193524503755)
          ·
            refine ⟨12132353953489790286755633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8088235968993193524503755 12132353953489790286755633)
            ·
              refine ⟨9099265465117342715066725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12132353953489790286755633 9099265465117342715066725)
              ·
                refine ⟨1706112274709501759075011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9099265465117342715066725 1706112274709501759075011)
                ·
                  refine ⟨2559168412064252638612517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1706112274709501759075011 2559168412064252638612517)
                  ·
                    refine ⟨479844077262047369739847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2559168412064252638612517 479844077262047369739847)
                    ·
                      rfl

theorem cell23_2803479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 1, 4].length) (baseStart_2803479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803479 prefixEnd_2803479 := by exact prefixLift 2803479
  have htrace : WordTrace (prefixWord ++ tailWord_2803479) baseStart_2803479 baseEnd_2803479 := by
    simpa [prefixWord, tailWord_2803479, baseEnd_2803479] using wordTrace_append hprefix tailTrace_2803479
  have hstable : (prefixWord ++ tailWord_2803479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803479).length < 2 ^ (prefixWord ++ tailWord_2803479).sum := by decide
  have hdescent : baseEnd_2803479 < baseStart_2803479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803512 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 1, 5, 2]
def baseStart_2803512 : Nat := 118140960795 + 2803512 * 2 ^ 59
def prefixEnd_2803512 : Nat := 4983230072969 + 3 ^ 40 * 2803512 * 2
def baseEnd_2803512 : Nat := 1439549176647740480106889

theorem tailTrace_2803512 : CollatzResearch.WordTrace tailWord_2803512 prefixEnd_2803512 1439549176647740480106889 := by
  unfold tailWord_2803512
  simp only [CollatzResearch.WordTrace]
  refine ⟨51126241509681150287678395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68168322012908200383571193 51126241509681150287678395)
  ·
    refine ⟨76689362264521725431517593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51126241509681150287678395 76689362264521725431517593)
    ·
      refine ⟨57517021698391294073638195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76689362264521725431517593 57517021698391294073638195)
      ·
        refine ⟨86275532547586941110457293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57517021698391294073638195 86275532547586941110457293)
        ·
          refine ⟨32353324705345102916421485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86275532547586941110457293 32353324705345102916421485)
          ·
            refine ⟨12132496764504413593658057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32353324705345102916421485 12132496764504413593658057)
            ·
              refine ⟨9099372573378310195243543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12132496764504413593658057 9099372573378310195243543)
              ·
                refine ⟨13649058860067465292865315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9099372573378310195243543 13649058860067465292865315)
                ·
                  refine ⟨20473588290101197939297973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13649058860067465292865315 20473588290101197939297973)
                  ·
                    refine ⟨1919398902196987306809185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20473588290101197939297973 1919398902196987306809185)
                    ·
                      refine ⟨1439549176647740480106889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919398902196987306809185 1439549176647740480106889)
                      ·
                        rfl

theorem cell23_2803512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 1, 5, 2].length) (baseStart_2803512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803512 prefixEnd_2803512 := by exact prefixLift 2803512
  have htrace : WordTrace (prefixWord ++ tailWord_2803512) baseStart_2803512 baseEnd_2803512 := by
    simpa [prefixWord, tailWord_2803512, baseEnd_2803512] using wordTrace_append hprefix tailTrace_2803512
  have hstable : (prefixWord ++ tailWord_2803512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803512).length < 2 ^ (prefixWord ++ tailWord_2803512).sum := by decide
  have hdescent : baseEnd_2803512 < baseStart_2803512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803513 : List Nat := [1, 2, 1, 7, 1, 2, 1, 3, 1, 4]
def baseStart_2803513 : Nat := 118140960795 + 2803513 * 2 ^ 59
def prefixEnd_2803513 : Nat := 4983230072969 + 3 ^ 40 * 2803513 * 2
def baseEnd_2803513 : Nat := 479849896709464992064795

theorem tailTrace_2803513 : CollatzResearch.WordTrace tailWord_2803513 prefixEnd_2803513 479849896709464992064795 := by
  unfold tailWord_2803513
  simp only [CollatzResearch.WordTrace]
  refine ⟨102252519492358677746143193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68168346328239118497428795 102252519492358677746143193)
  ·
    refine ⟨76689389619269008309607395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102252519492358677746143193 76689389619269008309607395)
    ·
      refine ⟨115034084428903512464411093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76689389619269008309607395 115034084428903512464411093)
      ·
        refine ⟨2696111353802426073384635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 115034084428903512464411093 2696111353802426073384635)
        ·
          refine ⟨4044167030703639110076953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2696111353802426073384635 4044167030703639110076953)
          ·
            refine ⟨3033125273027729332557715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4044167030703639110076953 3033125273027729332557715)
            ·
              refine ⟨4549687909541593998836573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3033125273027729332557715 4549687909541593998836573)
              ·
                refine ⟨1706132966078097749563715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4549687909541593998836573 1706132966078097749563715)
                ·
                  refine ⟨2559199449117146624345573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1706132966078097749563715 2559199449117146624345573)
                  ·
                    refine ⟨479849896709464992064795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2559199449117146624345573 479849896709464992064795)
                    ·
                      rfl

theorem cell23_2803513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 1, 4].length) (baseStart_2803513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803513 prefixEnd_2803513 := by exact prefixLift 2803513
  have htrace : WordTrace (prefixWord ++ tailWord_2803513) baseStart_2803513 baseEnd_2803513 := by
    simpa [prefixWord, tailWord_2803513, baseEnd_2803513] using wordTrace_append hprefix tailTrace_2803513
  have hstable : (prefixWord ++ tailWord_2803513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803513).length < 2 ^ (prefixWord ++ tailWord_2803513).sum := by decide
  have hdescent : baseEnd_2803513 < baseStart_2803513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803545 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 1, 1, 5]
def baseStart_2803545 : Nat := 118140960795 + 2803545 * 2 ^ 59
def prefixEnd_2803545 : Nat := 4983230072969 + 3 ^ 40 * 2803545 * 2
def baseEnd_2803545 : Nat := 1439566121509338850994237

theorem tailTrace_2803545 : CollatzResearch.WordTrace tailWord_2803545 prefixEnd_2803545 1439566121509338850994237 := by
  unfold tailWord_2803545
  simp only [CollatzResearch.WordTrace]
  refine ⟨102253686628242747211308089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68169124418828498140872059 102253686628242747211308089)
  ·
    refine ⟨76690264971182060408481067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102253686628242747211308089 76690264971182060408481067)
    ·
      refine ⟨115035397456773090612721601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76690264971182060408481067 115035397456773090612721601)
      ·
        refine ⟨86276548092579817959541201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115035397456773090612721601 86276548092579817959541201)
        ·
          refine ⟨64707411069434863469655901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86276548092579817959541201 64707411069434863469655901)
          ·
            refine ⟨24265279151038073801120963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64707411069434863469655901 24265279151038073801120963)
            ·
              refine ⟨36397918726557110701681445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24265279151038073801120963 36397918726557110701681445)
              ·
                refine ⟨6824609761229458256565271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36397918726557110701681445 6824609761229458256565271)
                ·
                  refine ⟨10236914641844187384847907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6824609761229458256565271 10236914641844187384847907)
                  ·
                    refine ⟨15355371962766281077271861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10236914641844187384847907 15355371962766281077271861)
                    ·
                      refine ⟨1439566121509338850994237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15355371962766281077271861 1439566121509338850994237)
                      ·
                        rfl

theorem cell23_2803545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_2803545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803545 prefixEnd_2803545 := by exact prefixLift 2803545
  have htrace : WordTrace (prefixWord ++ tailWord_2803545) baseStart_2803545 baseEnd_2803545 := by
    simpa [prefixWord, tailWord_2803545, baseEnd_2803545] using wordTrace_append hprefix tailTrace_2803545
  have hstable : (prefixWord ++ tailWord_2803545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803545).length < 2 ^ (prefixWord ++ tailWord_2803545).sum := by decide
  have hdescent : baseEnd_2803545 < baseStart_2803545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803556 : List Nat := [2, 3, 1, 1, 6, 1, 1, 2, 1, 5]
def baseStart_2803556 : Nat := 118140960795 + 2803556 * 2 ^ 59
def prefixEnd_2803556 : Nat := 4983230072969 + 3 ^ 40 * 2803556 * 2
def baseEnd_2803556 : Nat := 479857256598846102652229

theorem tailTrace_2803556 : CollatzResearch.WordTrace tailWord_2803556 prefixEnd_2803556 479857256598846102652229 := by
  unfold tailWord_2803556
  simp only [CollatzResearch.WordTrace]
  refine ⟨51127043915601448044979261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68169391887468597393305681 51127043915601448044979261)
  ·
    refine ⟨19172641468350543016867223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51127043915601448044979261 19172641468350543016867223)
    ·
      refine ⟨28758962202525814525300835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19172641468350543016867223 28758962202525814525300835)
      ·
        refine ⟨43138443303788721787951253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28758962202525814525300835 43138443303788721787951253)
        ·
          refine ⟨2022114529865096333810215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43138443303788721787951253 2022114529865096333810215)
          ·
            refine ⟨3033171794797644500715323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022114529865096333810215 3033171794797644500715323)
            ·
              refine ⟨4549757692196466751072985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3033171794797644500715323 4549757692196466751072985)
              ·
                refine ⟨3412318269147350063304739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4549757692196466751072985 3412318269147350063304739)
                ·
                  refine ⟨5118477403721025094957109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3412318269147350063304739 5118477403721025094957109)
                  ·
                    refine ⟨479857256598846102652229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5118477403721025094957109 479857256598846102652229)
                    ·
                      rfl

theorem cell23_2803556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_2803556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803556 prefixEnd_2803556 := by exact prefixLift 2803556
  have htrace : WordTrace (prefixWord ++ tailWord_2803556) baseStart_2803556 baseEnd_2803556 := by
    simpa [prefixWord, tailWord_2803556, baseEnd_2803556] using wordTrace_append hprefix tailTrace_2803556
  have hstable : (prefixWord ++ tailWord_2803556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803556).length < 2 ^ (prefixWord ++ tailWord_2803556).sum := by decide
  have hdescent : baseEnd_2803556 < baseStart_2803556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803559 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 5, 2, 2]
def baseStart_2803559 : Nat := 118140960795 + 2803559 * 2 ^ 59
def prefixEnd_2803559 : Nat := 4983230072969 + 3 ^ 40 * 2803559 * 2
def baseEnd_2803559 : Nat := 1439573310238501796219173

theorem tailTrace_2803559 : CollatzResearch.WordTrace tailWord_2803559 prefixEnd_2803559 1439573310238501796219173 := by
  unfold tailWord_2803559
  simp only [CollatzResearch.WordTrace]
  refine ⟨102254197250192027602317731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68169464833461351734878487 102254197250192027602317731)
  ·
    refine ⟨153381295875288041403476597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102254197250192027602317731 153381295875288041403476597)
    ·
      refine ⟨14379496488308253881575931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153381295875288041403476597 14379496488308253881575931)
      ·
        refine ⟨21569244732462380822363897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14379496488308253881575931 21569244732462380822363897)
        ·
          refine ⟨16176933549346785616772923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21569244732462380822363897 16176933549346785616772923)
          ·
            refine ⟨24265400324020178425159385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16176933549346785616772923 24265400324020178425159385)
            ·
              refine ⟨18199050243015133818869539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24265400324020178425159385 18199050243015133818869539)
              ·
                refine ⟨27298575364522700728304309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18199050243015133818869539 27298575364522700728304309)
                ·
                  refine ⟨2559241440424003193278529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27298575364522700728304309 2559241440424003193278529)
                  ·
                    refine ⟨1919431080318002394958897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2559241440424003193278529 1919431080318002394958897)
                    ·
                      refine ⟨1439573310238501796219173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919431080318002394958897 1439573310238501796219173)
                      ·
                        rfl

theorem cell23_2803559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_2803559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803559 prefixEnd_2803559 := by exact prefixLift 2803559
  have htrace : WordTrace (prefixWord ++ tailWord_2803559) baseStart_2803559 baseEnd_2803559 := by
    simpa [prefixWord, tailWord_2803559, baseEnd_2803559] using wordTrace_append hprefix tailTrace_2803559
  have hstable : (prefixWord ++ tailWord_2803559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803559).length < 2 ^ (prefixWord ++ tailWord_2803559).sum := by decide
  have hdescent : baseEnd_2803559 < baseStart_2803559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803565 : List Nat := [1, 5, 1, 1, 1, 1, 4, 9]
def baseStart_2803565 : Nat := 118140960795 + 2803565 * 2 ^ 59
def prefixEnd_2803565 : Nat := 4983230072969 + 3 ^ 40 * 2803565 * 2
def baseEnd_2803565 : Nat := 53317644115645510101635

theorem tailTrace_2803565 : CollatzResearch.WordTrace tailWord_2803565 prefixEnd_2803565 53317644115645510101635 := by
  unfold tailWord_2803565
  simp only [CollatzResearch.WordTrace]
  refine ⟨102254416088170290627036149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68169610725446860418024099 102254416088170290627036149)
  ·
    refine ⟨9586351508265964746284639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102254416088170290627036149 9586351508265964746284639)
    ·
      refine ⟨14379527262398947119426959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9586351508265964746284639 14379527262398947119426959)
      ·
        refine ⟨21569290893598420679140439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14379527262398947119426959 21569290893598420679140439)
        ·
          refine ⟨32353936340397631018710659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21569290893598420679140439 32353936340397631018710659)
          ·
            refine ⟨48530904510596446528065989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32353936340397631018710659 48530904510596446528065989)
            ·
              refine ⟨9099544595736833724012373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48530904510596446528065989 9099544595736833724012373)
              ·
                refine ⟨53317644115645510101635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9099544595736833724012373 53317644115645510101635)
                ·
                  rfl

theorem cell23_2803565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 9].length) (baseStart_2803565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803565 prefixEnd_2803565 := by exact prefixLift 2803565
  have htrace : WordTrace (prefixWord ++ tailWord_2803565) baseStart_2803565 baseEnd_2803565 := by
    simpa [prefixWord, tailWord_2803565, baseEnd_2803565] using wordTrace_append hprefix tailTrace_2803565
  have hstable : (prefixWord ++ tailWord_2803565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803565).length < 2 ^ (prefixWord ++ tailWord_2803565).sum := by decide
  have hdescent : baseEnd_2803565 < baseStart_2803565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803582 : List Nat := [4, 2, 3, 1, 1, 12]
def baseStart_2803582 : Nat := 118140960795 + 2803582 * 2 ^ 59
def prefixEnd_2803582 : Nat := 4983230072969 + 3 ^ 40 * 2803582 * 2
def baseEnd_2803582 : Nat := 5924218602031091383669

theorem tailTrace_2803582 : CollatzResearch.WordTrace tailWord_2803582 prefixEnd_2803582 5924218602031091383669 := by
  unfold tailWord_2803582
  simp only [CollatzResearch.WordTrace]
  refine ⟨12781879516138587816300625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68170024086072468353603333 12781879516138587816300625)
  ·
    refine ⟨9586409637103940862225469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12781879516138587816300625 9586409637103940862225469)
    ·
      refine ⟨3594903613913977823334551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9586409637103940862225469 3594903613913977823334551)
      ·
        refine ⟨5392355420870966735001827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3594903613913977823334551 5392355420870966735001827)
        ·
          refine ⟨8088533131306450102502741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5392355420870966735001827 8088533131306450102502741)
          ·
            refine ⟨5924218602031091383669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8088533131306450102502741 5924218602031091383669)
            ·
              rfl

theorem cell23_2803582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 12].length) (baseStart_2803582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803582 prefixEnd_2803582 := by exact prefixLift 2803582
  have htrace : WordTrace (prefixWord ++ tailWord_2803582) baseStart_2803582 baseEnd_2803582 := by
    simpa [prefixWord, tailWord_2803582, baseEnd_2803582] using wordTrace_append hprefix tailTrace_2803582
  have hstable : (prefixWord ++ tailWord_2803582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803582).length < 2 ^ (prefixWord ++ tailWord_2803582).sum := by decide
  have hdescent : baseEnd_2803582 < baseStart_2803582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803609 : List Nat := [1, 2, 1, 2, 1, 3, 4, 3, 2, 1, 3]
def baseStart_2803609 : Nat := 118140960795 + 2803609 * 2 ^ 59
def prefixEnd_2803609 : Nat := 4983230072969 + 3 ^ 40 * 2803609 * 2
def baseEnd_2803609 : Nat := 1439598984271226600593943

theorem tailTrace_2803609 : CollatzResearch.WordTrace tailWord_2803609 prefixEnd_2803609 1439598984271226600593943 := by
  unfold tailWord_2803609
  simp only [CollatzResearch.WordTrace]
  refine ⟨102256020900010886141637881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68170680600007257427758587 102256020900010886141637881)
  ·
    refine ⟨76692015675008164606228411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102256020900010886141637881 76692015675008164606228411)
    ·
      refine ⟨115038023512512246909342617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76692015675008164606228411 115038023512512246909342617)
      ·
        refine ⟨86278517634384185182006963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115038023512512246909342617 86278517634384185182006963)
        ·
          refine ⟨129417776451576277773010445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86278517634384185182006963 129417776451576277773010445)
          ·
            refine ⟨48531666169341104164878917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129417776451576277773010445 48531666169341104164878917)
            ·
              refine ⟨9099687406751457030914797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48531666169341104164878917 9099687406751457030914797)
              ·
                refine ⟨3412382777531796386593049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9099687406751457030914797 3412382777531796386593049)
                ·
                  refine ⟨2559287083148847289944787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3412382777531796386593049 2559287083148847289944787)
                  ·
                    refine ⟨3838930624723270934917181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2559287083148847289944787 3838930624723270934917181)
                    ·
                      refine ⟨1439598984271226600593943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3838930624723270934917181 1439598984271226600593943)
                      ·
                        rfl

theorem cell23_2803609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_2803609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803609 prefixEnd_2803609 := by exact prefixLift 2803609
  have htrace : WordTrace (prefixWord ++ tailWord_2803609) baseStart_2803609 baseEnd_2803609 := by
    simpa [prefixWord, tailWord_2803609, baseEnd_2803609] using wordTrace_append hprefix tailTrace_2803609
  have hstable : (prefixWord ++ tailWord_2803609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803609).length < 2 ^ (prefixWord ++ tailWord_2803609).sum := by decide
  have hdescent : baseEnd_2803609 < baseStart_2803609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803619 : List Nat := [1, 1, 1, 4, 1, 2, 1, 6, 1, 3, 2]
def baseStart_2803619 : Nat := 118140960795 + 2803619 * 2 ^ 59
def prefixEnd_2803619 : Nat := 4983230072969 + 3 ^ 40 * 2803619 * 2
def baseEnd_2803619 : Nat := 1439604119077771561468897

theorem tailTrace_2803619 : CollatzResearch.WordTrace tailWord_2803619 prefixEnd_2803619 1439604119077771561468897 := by
  unfold tailWord_2803619
  simp only [CollatzResearch.WordTrace]
  refine ⟨102256385629974657849501911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68170923753316438566334607 102256385629974657849501911)
  ·
    refine ⟨153384578444961986774252867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102256385629974657849501911 153384578444961986774252867)
    ·
      refine ⟨230076867667442980161379301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153384578444961986774252867 230076867667442980161379301)
      ·
        refine ⟨43139412687645558780258619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230076867667442980161379301 43139412687645558780258619)
        ·
          refine ⟨64709119031468338170387929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43139412687645558780258619 64709119031468338170387929)
          ·
            refine ⟨48531839273601253627790947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64709119031468338170387929 48531839273601253627790947)
            ·
              refine ⟨72797758910401880441686421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48531839273601253627790947 72797758910401880441686421)
              ·
                refine ⟨3412394948925088145704051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72797758910401880441686421 3412394948925088145704051)
                ·
                  refine ⟨5118592423387632218556077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3412394948925088145704051 5118592423387632218556077)
                  ·
                    refine ⟨1919472158770362081958529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5118592423387632218556077 1919472158770362081958529)
                    ·
                      refine ⟨1439604119077771561468897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919472158770362081958529 1439604119077771561468897)
                      ·
                        rfl

theorem cell23_2803619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_2803619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803619 prefixEnd_2803619 := by exact prefixLift 2803619
  have htrace : WordTrace (prefixWord ++ tailWord_2803619) baseStart_2803619 baseEnd_2803619 := by
    simpa [prefixWord, tailWord_2803619, baseEnd_2803619] using wordTrace_append hprefix tailTrace_2803619
  have hstable : (prefixWord ++ tailWord_2803619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803619).length < 2 ^ (prefixWord ++ tailWord_2803619).sum := by decide
  have hdescent : baseEnd_2803619 < baseStart_2803619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803630 : List Nat := [4, 1, 5, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2803630 : Nat := 118140960795 + 2803630 * 2 ^ 59
def prefixEnd_2803630 : Nat := 4983230072969 + 3 ^ 40 * 2803630 * 2
def baseEnd_2803630 : Nat := 1439609767364971018431347

theorem tailTrace_2803630 : CollatzResearch.WordTrace tailWord_2803630 prefixEnd_2803630 1439609767364971018431347 := by
  unfold tailWord_2803630
  simp only [CollatzResearch.WordTrace]
  refine ⟨12782098354116850841019043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68171191221956537818768229 12782098354116850841019043)
  ·
    refine ⟨19173147531175276261528565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12782098354116850841019043 19173147531175276261528565)
    ·
      refine ⟨1797482581047682149518303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19173147531175276261528565 1797482581047682149518303)
      ·
        refine ⟨2696223871571523224277455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1797482581047682149518303 2696223871571523224277455)
        ·
          refine ⟨4044335807357284836416183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2696223871571523224277455 4044335807357284836416183)
          ·
            refine ⟨6066503711035927254624275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044335807357284836416183 6066503711035927254624275)
            ·
              refine ⟨9099755566553890881936413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6066503711035927254624275 9099755566553890881936413)
              ·
                refine ⟨3412408337457709080726155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9099755566553890881936413 3412408337457709080726155)
                ·
                  refine ⟨5118612506186563621089233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3412408337457709080726155 5118612506186563621089233)
                  ·
                    refine ⟨3838959379639922715816925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5118612506186563621089233 3838959379639922715816925)
                    ·
                      refine ⟨1439609767364971018431347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3838959379639922715816925 1439609767364971018431347)
                      ·
                        rfl

theorem cell23_2803630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2803630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803630 prefixEnd_2803630 := by exact prefixLift 2803630
  have htrace : WordTrace (prefixWord ++ tailWord_2803630) baseStart_2803630 baseEnd_2803630 := by
    simpa [prefixWord, tailWord_2803630, baseEnd_2803630] using wordTrace_append hprefix tailTrace_2803630
  have hstable : (prefixWord ++ tailWord_2803630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803630).length < 2 ^ (prefixWord ++ tailWord_2803630).sum := by decide
  have hdescent : baseEnd_2803630 < baseStart_2803630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803635 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 5]
def baseStart_2803635 : Nat := 118140960795 + 2803635 * 2 ^ 59
def prefixEnd_2803635 : Nat := 4983230072969 + 3 ^ 40 * 2803635 * 2
def baseEnd_2803635 : Nat := 1439612334768243498868823

theorem tailTrace_2803635 : CollatzResearch.WordTrace tailWord_2803635 prefixEnd_2803635 1439612334768243498868823 := by
  unfold tailWord_2803635
  simp only [CollatzResearch.WordTrace]
  refine ⟨102256969197916692582084359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68171312798611128388056239 102256969197916692582084359)
  ·
    refine ⟨153385453796875038873126539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102256969197916692582084359 153385453796875038873126539)
    ·
      refine ⟨230078180695312558309689809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153385453796875038873126539 230078180695312558309689809)
      ·
        refine ⟨172558635521484418732267357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230078180695312558309689809 172558635521484418732267357)
        ·
          refine ⟨64709488320556657024600259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172558635521484418732267357 64709488320556657024600259)
          ·
            refine ⟨97064232480834985536900389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64709488320556657024600259 97064232480834985536900389)
            ·
              refine ⟨18199543590156559788168823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97064232480834985536900389 18199543590156559788168823)
              ·
                refine ⟨27299315385234839682253235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18199543590156559788168823 27299315385234839682253235)
                ·
                  refine ⟨40948973077852259523379853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27299315385234839682253235 40948973077852259523379853)
                  ·
                    refine ⟨15355864904194597321267445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40948973077852259523379853 15355864904194597321267445)
                    ·
                      refine ⟨1439612334768243498868823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15355864904194597321267445 1439612334768243498868823)
                      ·
                        rfl

theorem cell23_2803635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_2803635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803635 prefixEnd_2803635 := by exact prefixLift 2803635
  have htrace : WordTrace (prefixWord ++ tailWord_2803635) baseStart_2803635 baseEnd_2803635 := by
    simpa [prefixWord, tailWord_2803635, baseEnd_2803635] using wordTrace_append hprefix tailTrace_2803635
  have hstable : (prefixWord ++ tailWord_2803635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803635).length < 2 ^ (prefixWord ++ tailWord_2803635).sum := by decide
  have hdescent : baseEnd_2803635 < baseStart_2803635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803662 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_2803662 : Nat := 118140960795 + 2803662 * 2 ^ 59
def prefixEnd_2803662 : Nat := 4983230072969 + 3 ^ 40 * 2803662 * 2
def baseEnd_2803662 : Nat := 1439626198745914893231199

theorem tailTrace_2803662 : CollatzResearch.WordTrace tailWord_2803662 prefixEnd_2803662 1439626198745914893231199 := by
  unfold tailWord_2803662
  simp only [CollatzResearch.WordTrace]
  refine ⟨12782244246102359524164655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68171969312545917462211493 12782244246102359524164655)
  ·
    refine ⟨19173366369153539286246983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12782244246102359524164655 19173366369153539286246983)
    ·
      refine ⟨28760049553730308929370475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19173366369153539286246983 28760049553730308929370475)
      ·
        refine ⟨43140074330595463394055713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28760049553730308929370475 43140074330595463394055713)
        ·
          refine ⟨32355055747946597545541785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43140074330595463394055713 32355055747946597545541785)
          ·
            refine ⟨24266291810959948159156339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32355055747946597545541785 24266291810959948159156339)
            ·
              refine ⟨36399437716439922238734509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24266291810959948159156339 36399437716439922238734509)
              ·
                refine ⟨13649789143664970839525441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36399437716439922238734509 13649789143664970839525441)
                ·
                  refine ⟨10237341857748728129644081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13649789143664970839525441 10237341857748728129644081)
                  ·
                    refine ⟨7678006393311546097233061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10237341857748728129644081 7678006393311546097233061)
                    ·
                      refine ⟨1439626198745914893231199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7678006393311546097233061 1439626198745914893231199)
                      ·
                        rfl

theorem cell23_2803662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_2803662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803662 prefixEnd_2803662 := by exact prefixLift 2803662
  have htrace : WordTrace (prefixWord ++ tailWord_2803662) baseStart_2803662 baseEnd_2803662 := by
    simpa [prefixWord, tailWord_2803662, baseEnd_2803662] using wordTrace_append hprefix tailTrace_2803662
  have hstable : (prefixWord ++ tailWord_2803662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803662).length < 2 ^ (prefixWord ++ tailWord_2803662).sum := by decide
  have hdescent : baseEnd_2803662 < baseStart_2803662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803670 : List Nat := [5, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_2803670 : Nat := 118140960795 + 2803670 * 2 ^ 59
def prefixEnd_2803670 : Nat := 4983230072969 + 3 ^ 40 * 2803670 * 2
def baseEnd_2803670 : Nat := 1439630306591150861931163

theorem tailTrace_2803670 : CollatzResearch.WordTrace tailWord_2803670 prefixEnd_2803670 1439630306591150861931163 := by
  unfold tailWord_2803670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6391140359549368347475529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68172163835193262373072309 6391140359549368347475529)
  ·
    refine ⟨4793355269662026260606647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6391140359549368347475529 4793355269662026260606647)
    ·
      refine ⟨7190032904493039390909971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4793355269662026260606647 7190032904493039390909971)
      ·
        refine ⟨10785049356739559086364957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7190032904493039390909971 10785049356739559086364957)
        ·
          refine ⟨4044393508777334657386859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10785049356739559086364957 4044393508777334657386859)
          ·
            refine ⟨6066590263166001986080289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044393508777334657386859 6066590263166001986080289)
            ·
              refine ⟨4549942697374501489560217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6066590263166001986080289 4549942697374501489560217)
              ·
                refine ⟨3412457023030876117170163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4549942697374501489560217 3412457023030876117170163)
                ·
                  refine ⟨5118685534546314175755245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3412457023030876117170163 5118685534546314175755245)
                  ·
                    refine ⟨1919507075454867815908217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5118685534546314175755245 1919507075454867815908217)
                    ·
                      refine ⟨1439630306591150861931163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919507075454867815908217 1439630306591150861931163)
                      ·
                        rfl

theorem cell23_2803670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_2803670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803670 prefixEnd_2803670 := by exact prefixLift 2803670
  have htrace : WordTrace (prefixWord ++ tailWord_2803670) baseStart_2803670 baseEnd_2803670 := by
    simpa [prefixWord, tailWord_2803670, baseEnd_2803670] using wordTrace_append hprefix tailTrace_2803670
  have hstable : (prefixWord ++ tailWord_2803670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803670).length < 2 ^ (prefixWord ++ tailWord_2803670).sum := by decide
  have hdescent : baseEnd_2803670 < baseStart_2803670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803766 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_2803766 : Nat := 118140960795 + 2803766 * 2 ^ 59
def prefixEnd_2803766 : Nat := 4983230072969 + 3 ^ 40 * 2803766 * 2
def baseEnd_2803766 : Nat := 479893200244660828776907

theorem tailTrace_2803766 : CollatzResearch.WordTrace tailWord_2803766 prefixEnd_2803766 479893200244660828776907 := by
  unfold tailWord_2803766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6391359197527631372193947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68174498106961401303402101 6391359197527631372193947)
  ·
    refine ⟨9587038796291447058290921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6391359197527631372193947 9587038796291447058290921)
    ·
      refine ⟨7190279097218585293718191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9587038796291447058290921 7190279097218585293718191)
      ·
        refine ⟨10785418645827877940577287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7190279097218585293718191 10785418645827877940577287)
        ·
          refine ⟨16178127968741816910865931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10785418645827877940577287 16178127968741816910865931)
          ·
            refine ⟨24267191953112725366298897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16178127968741816910865931 24267191953112725366298897)
            ·
              refine ⟨18200393964834544024724173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24267191953112725366298897 18200393964834544024724173)
              ·
                refine ⟨6825147736812954009271565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18200393964834544024724173 6825147736812954009271565)
                ·
                  refine ⟨2559430401304857753476837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6825147736812954009271565 2559430401304857753476837)
                  ·
                    refine ⟨479893200244660828776907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2559430401304857753476837 479893200244660828776907)
                    ·
                      rfl

theorem cell23_2803766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_2803766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803766 prefixEnd_2803766 := by exact prefixLift 2803766
  have htrace : WordTrace (prefixWord ++ tailWord_2803766) baseStart_2803766 baseEnd_2803766 := by
    simpa [prefixWord, tailWord_2803766, baseEnd_2803766] using wordTrace_append hprefix tailTrace_2803766
  have hstable : (prefixWord ++ tailWord_2803766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803766).length < 2 ^ (prefixWord ++ tailWord_2803766).sum := by decide
  have hdescent : baseEnd_2803766 < baseStart_2803766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803823 : List Nat := [1, 1, 2, 1, 3, 4, 2, 4, 1, 1, 3]
def baseStart_2803823 : Nat := 118140960795 + 2803823 * 2 ^ 59
def prefixEnd_2803823 : Nat := 4983230072969 + 3 ^ 40 * 2803823 * 2
def baseEnd_2803823 : Nat := 1439708869131288763317959

theorem tailTrace_2803823 : CollatzResearch.WordTrace tailWord_2803823 prefixEnd_2803823 1439708869131288763317959 := by
  unfold tailWord_2803823
  simp only [CollatzResearch.WordTrace]
  refine ⟨102263826121235600689928123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68175884080823733793285415 102263826121235600689928123)
  ·
    refine ⟨153395739181853401034892185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102263826121235600689928123 153395739181853401034892185)
    ·
      refine ⟨115046804386390050776169139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153395739181853401034892185 115046804386390050776169139)
      ·
        refine ⟨172570206579585076164253709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115046804386390050776169139 172570206579585076164253709)
        ·
          refine ⟨64713827467344403561595141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172570206579585076164253709 64713827467344403561595141)
          ·
            refine ⟨12133842650127075667799089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64713827467344403561595141 12133842650127075667799089)
            ·
              refine ⟨9100381987595306750849317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12133842650127075667799089 9100381987595306750849317)
              ·
                refine ⟨1706321622674120015784247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9100381987595306750849317 1706321622674120015784247)
                ·
                  refine ⟨2559482434011180023676371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1706321622674120015784247 2559482434011180023676371)
                  ·
                    refine ⟨3839223651016770035514557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2559482434011180023676371 3839223651016770035514557)
                    ·
                      refine ⟨1439708869131288763317959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3839223651016770035514557 1439708869131288763317959)
                      ·
                        rfl

theorem cell23_2803823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 1, 1, 3].length) (baseStart_2803823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803823 prefixEnd_2803823 := by exact prefixLift 2803823
  have htrace : WordTrace (prefixWord ++ tailWord_2803823) baseStart_2803823 baseEnd_2803823 := by
    simpa [prefixWord, tailWord_2803823, baseEnd_2803823] using wordTrace_append hprefix tailTrace_2803823
  have hstable : (prefixWord ++ tailWord_2803823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803823).length < 2 ^ (prefixWord ++ tailWord_2803823).sum := by decide
  have hdescent : baseEnd_2803823 < baseStart_2803823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803869 : List Nat := [1, 4, 2, 1, 1, 5, 9]
def baseStart_2803869 : Nat := 118140960795 + 2803869 * 2 ^ 59
def prefixEnd_2803869 : Nat := 4983230072969 + 3 ^ 40 * 2803869 * 2
def baseEnd_2803869 : Nat := 17774475175819698559787

theorem tailTrace_2803869 : CollatzResearch.WordTrace tailWord_2803869 prefixEnd_2803869 17774475175819698559787 := by
  unfold tailWord_2803869
  simp only [CollatzResearch.WordTrace]
  refine ⟨102265503879068950546102661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68177002586045967030735107 102265503879068950546102661)
  ·
    refine ⟨19174781977325428227394249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102265503879068950546102661 19174781977325428227394249)
    ·
      refine ⟨14381086482994071170545687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19174781977325428227394249 14381086482994071170545687)
      ·
        refine ⟨21571629724491106755818531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14381086482994071170545687 21571629724491106755818531)
        ·
          refine ⟨32357444586736660133727797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21571629724491106755818531 32357444586736660133727797)
          ·
            refine ⟨3033510430006561887536981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32357444586736660133727797 3033510430006561887536981)
            ·
              refine ⟨17774475175819698559787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3033510430006561887536981 17774475175819698559787)
              ·
                rfl

theorem cell23_2803869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 9].length) (baseStart_2803869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803869 prefixEnd_2803869 := by exact prefixLift 2803869
  have htrace : WordTrace (prefixWord ++ tailWord_2803869) baseStart_2803869 baseEnd_2803869 := by
    simpa [prefixWord, tailWord_2803869, baseEnd_2803869] using wordTrace_append hprefix tailTrace_2803869
  have hstable : (prefixWord ++ tailWord_2803869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803869).length < 2 ^ (prefixWord ++ tailWord_2803869).sum := by decide
  have hdescent : baseEnd_2803869 < baseStart_2803869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803900 : List Nat := [2, 2, 2, 3, 3, 2, 1, 2, 1, 2, 3]
def baseStart_2803900 : Nat := 118140960795 + 2803900 * 2 ^ 59
def prefixEnd_2803900 : Nat := 4983230072969 + 3 ^ 40 * 2803900 * 2
def baseEnd_2803900 : Nat := 1439748407141684962055105

theorem tailTrace_2803900 : CollatzResearch.WordTrace tailWord_2803900 prefixEnd_2803900 1439748407141684962055105 := by
  unfold tailWord_2803900
  simp only [CollatzResearch.WordTrace]
  refine ⟨51133317270978321420240577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68177756361304428560320769 51133317270978321420240577)
  ·
    refine ⟨38349987953233741065180433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51133317270978321420240577 38349987953233741065180433)
    ·
      refine ⟨28762490964925305798885325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38349987953233741065180433 28762490964925305798885325)
      ·
        refine ⟨10785934111846989674581997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28762490964925305798885325 10785934111846989674581997)
        ·
          refine ⟨4044725291942621127968249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10785934111846989674581997 4044725291942621127968249)
          ·
            refine ⟨3033543968956965845976187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4044725291942621127968249 3033543968956965845976187)
            ·
              refine ⟨4550315953435448768964281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3033543968956965845976187 4550315953435448768964281)
              ·
                refine ⟨3412736965076586576723211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4550315953435448768964281 3412736965076586576723211)
                ·
                  refine ⟨5119105447614879865084817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3412736965076586576723211 5119105447614879865084817)
                  ·
                    refine ⟨3839329085711159898813613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5119105447614879865084817 3839329085711159898813613)
                    ·
                      refine ⟨1439748407141684962055105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3839329085711159898813613 1439748407141684962055105)
                      ·
                        rfl

theorem cell23_2803900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_2803900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803900 prefixEnd_2803900 := by exact prefixLift 2803900
  have htrace : WordTrace (prefixWord ++ tailWord_2803900) baseStart_2803900 baseEnd_2803900 := by
    simpa [prefixWord, tailWord_2803900, baseEnd_2803900] using wordTrace_append hprefix tailTrace_2803900
  have hstable : (prefixWord ++ tailWord_2803900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803900).length < 2 ^ (prefixWord ++ tailWord_2803900).sum := by decide
  have hdescent : baseEnd_2803900 < baseStart_2803900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803936 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 3, 4, 2]
def baseStart_2803936 : Nat := 118140960795 + 2803936 * 2 ^ 59
def prefixEnd_2803936 : Nat := 4983230072969 + 3 ^ 40 * 2803936 * 2
def baseEnd_2803936 : Nat := 1439766892445246821204939

theorem tailTrace_2803936 : CollatzResearch.WordTrace tailWord_2803936 prefixEnd_2803936 1439766892445246821204939 := by
  unfold tailWord_2803936
  simp only [CollatzResearch.WordTrace]
  refine ⟨51133973784913110494395831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68178631713217480659194441 51133973784913110494395831)
  ·
    refine ⟨76700960677369665741593747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51133973784913110494395831 76700960677369665741593747)
    ·
      refine ⟨115051441016054498612390621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76700960677369665741593747 115051441016054498612390621)
      ·
        refine ⟨43144290381020436979646483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115051441016054498612390621 43144290381020436979646483)
        ·
          refine ⟨64716435571530655469469725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43144290381020436979646483 64716435571530655469469725)
          ·
            refine ⟨24268663339323995801051147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64716435571530655469469725 24268663339323995801051147)
            ·
              refine ⟨36402995008985993701576721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24268663339323995801051147 36402995008985993701576721)
              ·
                refine ⟨27302246256739495276182541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36402995008985993701576721 27302246256739495276182541)
                ·
                  refine ⟨10238342346277310728568453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27302246256739495276182541 10238342346277310728568453)
                  ·
                    refine ⟨1919689189926995761606585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10238342346277310728568453 1919689189926995761606585)
                    ·
                      refine ⟨1439766892445246821204939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919689189926995761606585 1439766892445246821204939)
                      ·
                        rfl

theorem cell23_2803936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_2803936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803936 prefixEnd_2803936 := by exact prefixLift 2803936
  have htrace : WordTrace (prefixWord ++ tailWord_2803936) baseStart_2803936 baseEnd_2803936 := by
    simpa [prefixWord, tailWord_2803936, baseEnd_2803936] using wordTrace_append hprefix tailTrace_2803936
  have hstable : (prefixWord ++ tailWord_2803936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803936).length < 2 ^ (prefixWord ++ tailWord_2803936).sum := by decide
  have hdescent : baseEnd_2803936 < baseStart_2803936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803966 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2803966 : Nat := 118140960795 + 2803966 * 2 ^ 59
def prefixEnd_2803966 : Nat := 4983230072969 + 3 ^ 40 * 2803966 * 2
def baseEnd_2803966 : Nat := 1439782296864881703829801

theorem tailTrace_2803966 : CollatzResearch.WordTrace tailWord_2803966 prefixEnd_2803966 1439782296864881703829801 := by
  unfold tailWord_2803966
  simp only [CollatzResearch.WordTrace]
  refine ⟨12783630219964692014047969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68179361173145024074922501 12783630219964692014047969)
  ·
    refine ⟨9587722664973519010535977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12783630219964692014047969 9587722664973519010535977)
    ·
      refine ⟨7190791998730139257901983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9587722664973519010535977 7190791998730139257901983)
      ·
        refine ⟨10786187998095208886852975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7190791998730139257901983 10786187998095208886852975)
        ·
          refine ⟨16179281997142813330279463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10786187998095208886852975 16179281997142813330279463)
          ·
            refine ⟨24268922995714219995419195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16179281997142813330279463 24268922995714219995419195)
            ·
              refine ⟨36403384493571329993128793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24268922995714219995419195 36403384493571329993128793)
              ·
                refine ⟨27302538370178497494846595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36403384493571329993128793 27302538370178497494846595)
                ·
                  refine ⟨40953807555267746242269893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27302538370178497494846595 40953807555267746242269893)
                  ·
                    refine ⟨7678838916612702420425605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40953807555267746242269893 7678838916612702420425605)
                    ·
                      refine ⟨1439782296864881703829801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7678838916612702420425605 1439782296864881703829801)
                      ·
                        rfl

theorem cell23_2803966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2803966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803966 prefixEnd_2803966 := by exact prefixLift 2803966
  have htrace : WordTrace (prefixWord ++ tailWord_2803966) baseStart_2803966 baseEnd_2803966 := by
    simpa [prefixWord, tailWord_2803966, baseEnd_2803966] using wordTrace_append hprefix tailTrace_2803966
  have hstable : (prefixWord ++ tailWord_2803966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803966).length < 2 ^ (prefixWord ++ tailWord_2803966).sum := by decide
  have hdescent : baseEnd_2803966 < baseStart_2803966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2803970 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_2803970 : Nat := 118140960795 + 2803970 * 2 ^ 59
def prefixEnd_2803970 : Nat := 4983230072969 + 3 ^ 40 * 2803970 * 2
def baseEnd_2803970 : Nat := 1439784350787499688179783

theorem tailTrace_2803970 : CollatzResearch.WordTrace tailWord_2803970 prefixEnd_2803970 1439784350787499688179783 := by
  unfold tailWord_2803970
  simp only [CollatzResearch.WordTrace]
  refine ⟨25567296912925761198882341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68179458434468696530352909 25567296912925761198882341)
  ·
    refine ⟨4793868171173580224790439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25567296912925761198882341 4793868171173580224790439)
    ·
      refine ⟨7190802256760370337185659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4793868171173580224790439 7190802256760370337185659)
      ·
        refine ⟨10786203385140555505778489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7190802256760370337185659 10786203385140555505778489)
        ·
          refine ⟨8089652538855416629333867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10786203385140555505778489 8089652538855416629333867)
          ·
            refine ⟨12134478808283124944000801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8089652538855416629333867 12134478808283124944000801)
            ·
              refine ⟨9100859106212343708000601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12134478808283124944000801 9100859106212343708000601)
              ·
                refine ⟨6825644329659257781000451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9100859106212343708000601 6825644329659257781000451)
                ·
                  refine ⟨10238466494488886671500677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6825644329659257781000451 10238466494488886671500677)
                  ·
                    refine ⟨1919712467716666250906377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10238466494488886671500677 1919712467716666250906377)
                    ·
                      refine ⟨1439784350787499688179783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919712467716666250906377 1439784350787499688179783)
                      ·
                        rfl

theorem cell23_2803970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_2803970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2803970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2803970 prefixEnd_2803970 := by exact prefixLift 2803970
  have htrace : WordTrace (prefixWord ++ tailWord_2803970) baseStart_2803970 baseEnd_2803970 := by
    simpa [prefixWord, tailWord_2803970, baseEnd_2803970] using wordTrace_append hprefix tailTrace_2803970
  have hstable : (prefixWord ++ tailWord_2803970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2803970).length < 2 ^ (prefixWord ++ tailWord_2803970).sum := by decide
  have hdescent : baseEnd_2803970 < baseStart_2803970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2803970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804019 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 2, 8]
def baseStart_2804019 : Nat := 118140960795 + 2804019 * 2 ^ 59
def prefixEnd_2804019 : Nat := 4983230072969 + 3 ^ 40 * 2804019 * 2
def baseEnd_2804019 : Nat := 479936503779856665489019

theorem tailTrace_2804019 : CollatzResearch.WordTrace tailWord_2804019 prefixEnd_2804019 479936503779856665489019 := by
  unfold tailWord_2804019
  simp only [CollatzResearch.WordTrace]
  refine ⟨102270974828525526164063111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68180649885683684109375407 102270974828525526164063111)
  ·
    refine ⟨153406462242788289246094667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102270974828525526164063111 153406462242788289246094667)
    ·
      refine ⟨230109693364182433869142001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153406462242788289246094667 230109693364182433869142001)
      ·
        refine ⟨172582270023136825401856501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230109693364182433869142001 172582270023136825401856501)
        ·
          refine ⟨16179587814669077381424047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172582270023136825401856501 16179587814669077381424047)
          ·
            refine ⟨24269381722003616072136071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16179587814669077381424047 24269381722003616072136071)
            ·
              refine ⟨36404072583005424108204107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24269381722003616072136071 36404072583005424108204107)
              ·
                refine ⟨54606108874508136162306161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36404072583005424108204107 54606108874508136162306161)
                ·
                  refine ⟨40954581655881102121729621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54606108874508136162306161 40954581655881102121729621)
                  ·
                    refine ⟨479936503779856665489019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40954581655881102121729621 479936503779856665489019)
                    ·
                      rfl

theorem cell23_2804019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 8].length) (baseStart_2804019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804019 prefixEnd_2804019 := by exact prefixLift 2804019
  have htrace : WordTrace (prefixWord ++ tailWord_2804019) baseStart_2804019 baseEnd_2804019 := by
    simpa [prefixWord, tailWord_2804019, baseEnd_2804019] using wordTrace_append hprefix tailTrace_2804019
  have hstable : (prefixWord ++ tailWord_2804019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804019).length < 2 ^ (prefixWord ++ tailWord_2804019).sum := by decide
  have hdescent : baseEnd_2804019 < baseStart_2804019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804026 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4]
def baseStart_2804026 : Nat := 118140960795 + 2804026 * 2 ^ 59
def prefixEnd_2804026 : Nat := 4983230072969 + 3 ^ 40 * 2804026 * 2
def baseEnd_2804026 : Nat := 1439813105704151469079525

theorem tailTrace_2804026 : CollatzResearch.WordTrace tailWord_2804026 prefixEnd_2804026 1439813105704151469079525 := by
  unfold tailWord_2804026
  simp only [CollatzResearch.WordTrace]
  refine ⟨25567807534875041589891983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68180820093000110906378621 25567807534875041589891983)
  ·
    refine ⟨38351711302312562384837975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25567807534875041589891983 38351711302312562384837975)
    ·
      refine ⟨57527566953468843577256963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38351711302312562384837975 57527566953468843577256963)
      ·
        refine ⟨86291350430203265365885445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57527566953468843577256963 86291350430203265365885445)
        ·
          refine ⟨16179628205663112256103521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86291350430203265365885445 16179628205663112256103521)
          ·
            refine ⟨12134721154247334192077641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16179628205663112256103521 12134721154247334192077641)
            ·
              refine ⟨9101040865685500644058231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12134721154247334192077641 9101040865685500644058231)
              ·
                refine ⟨13651561298528250966087347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9101040865685500644058231 13651561298528250966087347)
                ·
                  refine ⟨20477341947792376449131021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13651561298528250966087347 20477341947792376449131021)
                  ·
                    refine ⟨7679003230422141168424133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20477341947792376449131021 7679003230422141168424133)
                    ·
                      refine ⟨1439813105704151469079525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7679003230422141168424133 1439813105704151469079525)
                      ·
                        rfl

theorem cell23_2804026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_2804026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804026 prefixEnd_2804026 := by exact prefixLift 2804026
  have htrace : WordTrace (prefixWord ++ tailWord_2804026) baseStart_2804026 baseEnd_2804026 := by
    simpa [prefixWord, tailWord_2804026, baseEnd_2804026] using wordTrace_append hprefix tailTrace_2804026
  have hstable : (prefixWord ++ tailWord_2804026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804026).length < 2 ^ (prefixWord ++ tailWord_2804026).sum := by decide
  have hdescent : baseEnd_2804026 < baseStart_2804026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804046 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3]
def baseStart_2804046 : Nat := 118140960795 + 2804046 * 2 ^ 59
def prefixEnd_2804046 : Nat := 4983230072969 + 3 ^ 40 * 2804046 * 2
def baseEnd_2804046 : Nat := 1439823375317241390829433

theorem tailTrace_2804046 : CollatzResearch.WordTrace tailWord_2804046 prefixEnd_2804046 1439823375317241390829433 := by
  unfold tailWord_2804046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12783994949928463721911999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68181306399618473183530661 12783994949928463721911999)
  ·
    refine ⟨19175992424892695582867999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12783994949928463721911999 19175992424892695582867999)
    ·
      refine ⟨28763988637339043374301999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19175992424892695582867999 28763988637339043374301999)
      ·
        refine ⟨43145982956008565061452999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28763988637339043374301999 43145982956008565061452999)
        ·
          refine ⟨64718974434012847592179499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43145982956008565061452999 64718974434012847592179499)
          ·
            refine ⟨97078461651019271388269249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64718974434012847592179499 97078461651019271388269249)
            ·
              refine ⟨72808846238264453541201937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97078461651019271388269249 72808846238264453541201937)
              ·
                refine ⟨54606634678698340155901453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72808846238264453541201937 54606634678698340155901453)
                ·
                  refine ⟨20477488004511877558463045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54606634678698340155901453 20477488004511877558463045)
                  ·
                    refine ⟨3839529000845977042211821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20477488004511877558463045 3839529000845977042211821)
                    ·
                      refine ⟨1439823375317241390829433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3839529000845977042211821 1439823375317241390829433)
                      ·
                        rfl

theorem cell23_2804046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_2804046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804046 prefixEnd_2804046 := by exact prefixLift 2804046
  have htrace : WordTrace (prefixWord ++ tailWord_2804046) baseStart_2804046 baseEnd_2804046 := by
    simpa [prefixWord, tailWord_2804046, baseEnd_2804046] using wordTrace_append hprefix tailTrace_2804046
  have hstable : (prefixWord ++ tailWord_2804046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804046).length < 2 ^ (prefixWord ++ tailWord_2804046).sum := by decide
  have hdescent : baseEnd_2804046 < baseStart_2804046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804133 : List Nat := [1, 3, 1, 2, 1, 1, 4, 4, 1, 1, 4]
def baseStart_2804133 : Nat := 118140960795 + 2804133 * 2 ^ 59
def prefixEnd_2804133 : Nat := 4983230072969 + 3 ^ 40 * 2804133 * 2
def baseEnd_2804133 : Nat := 1439868048134182550441533

theorem tailTrace_2804133 : CollatzResearch.WordTrace tailWord_2804133 prefixEnd_2804133 1439868048134182550441533 := by
  unfold tailWord_2804133
  simp only [CollatzResearch.WordTrace]
  refine ⟨102275132750112523633713053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68183421833408349089142035 102275132750112523633713053)
  ·
    refine ⟨38353174781292196362642395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102275132750112523633713053 38353174781292196362642395)
    ·
      refine ⟨57529762171938294543963593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38353174781292196362642395 57529762171938294543963593)
      ·
        refine ⟨43147321628953720907972695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57529762171938294543963593 43147321628953720907972695)
        ·
          refine ⟨64720982443430581361959043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43147321628953720907972695 64720982443430581361959043)
          ·
            refine ⟨97081473665145872042938565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64720982443430581361959043 97081473665145872042938565)
            ·
              refine ⟨18202776312214851008050981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97081473665145872042938565 18202776312214851008050981)
              ·
                refine ⟨3413020558540284564009559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18202776312214851008050981 3413020558540284564009559)
                ·
                  refine ⟨5119530837810426846014339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3413020558540284564009559 5119530837810426846014339)
                  ·
                    refine ⟨7679296256715640269021509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5119530837810426846014339 7679296256715640269021509)
                    ·
                      refine ⟨1439868048134182550441533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7679296256715640269021509 1439868048134182550441533)
                      ·
                        rfl

theorem cell23_2804133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_2804133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804133 prefixEnd_2804133 := by exact prefixLift 2804133
  have htrace : WordTrace (prefixWord ++ tailWord_2804133) baseStart_2804133 baseEnd_2804133 := by
    simpa [prefixWord, tailWord_2804133, baseEnd_2804133] using wordTrace_append hprefix tailTrace_2804133
  have hstable : (prefixWord ++ tailWord_2804133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804133).length < 2 ^ (prefixWord ++ tailWord_2804133).sum := by decide
  have hdescent : baseEnd_2804133 < baseStart_2804133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804161 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2804161 : Nat := 118140960795 + 2804161 * 2 ^ 59
def prefixEnd_2804161 : Nat := 4983230072969 + 3 ^ 40 * 2804161 * 2
def baseEnd_2804161 : Nat := 1439882425592508440891405

theorem tailTrace_2804161 : CollatzResearch.WordTrace tailWord_2804161 prefixEnd_2804161 1439882425592508440891405 := by
  unfold tailWord_2804161
  simp only [CollatzResearch.WordTrace]
  refine ⟨102276153994011084415732337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68184102662674056277154891 102276153994011084415732337)
  ·
    refine ⟨76707115495508313311799253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102276153994011084415732337 76707115495508313311799253)
    ·
      refine ⟨1797823019425976093245295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 76707115495508313311799253 1797823019425976093245295)
      ·
        refine ⟨2696734529138964139867943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1797823019425976093245295 2696734529138964139867943)
        ·
          refine ⟨4045101793708446209801915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2696734529138964139867943 4045101793708446209801915)
          ·
            refine ⟨6067652690562669314702873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4045101793708446209801915 6067652690562669314702873)
            ·
              refine ⟨4550739517922001986027155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6067652690562669314702873 4550739517922001986027155)
              ·
                refine ⟨6826109276883002979040733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4550739517922001986027155 6826109276883002979040733)
                ·
                  refine ⟨2559790978831126117140275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6826109276883002979040733 2559790978831126117140275)
                  ·
                    refine ⟨3839686468246689175710413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2559790978831126117140275 3839686468246689175710413)
                    ·
                      refine ⟨1439882425592508440891405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3839686468246689175710413 1439882425592508440891405)
                      ·
                        rfl

theorem cell23_2804161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2804161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804161 prefixEnd_2804161 := by exact prefixLift 2804161
  have htrace : WordTrace (prefixWord ++ tailWord_2804161) baseStart_2804161 baseEnd_2804161 := by
    simpa [prefixWord, tailWord_2804161, baseEnd_2804161] using wordTrace_append hprefix tailTrace_2804161
  have hstable : (prefixWord ++ tailWord_2804161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804161).length < 2 ^ (prefixWord ++ tailWord_2804161).sum := by decide
  have hdescent : baseEnd_2804161 < baseStart_2804161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804167 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 3, 2, 2]
def baseStart_2804167 : Nat := 118140960795 + 2804167 * 2 ^ 59
def prefixEnd_2804167 : Nat := 4983230072969 + 3 ^ 40 * 2804167 * 2
def baseEnd_2804167 : Nat := 1439885506476435417416377

theorem tailTrace_2804167 : CollatzResearch.WordTrace tailWord_2804167 prefixEnd_2804167 1439885506476435417416377 := by
  unfold tailWord_2804167
  simp only [CollatzResearch.WordTrace]
  refine ⟨102276372831989347440450755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68184248554659564960300503 102276372831989347440450755)
  ·
    refine ⟨153414559247984021160676133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102276372831989347440450755 153414559247984021160676133)
    ·
      refine ⟨28765229858997003967626775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153414559247984021160676133 28765229858997003967626775)
      ·
        refine ⟨43147844788495505951440163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28765229858997003967626775 43147844788495505951440163)
        ·
          refine ⟨64721767182743258927160245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43147844788495505951440163 64721767182743258927160245)
          ·
            refine ⟨6067665673382180524421273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64721767182743258927160245 6067665673382180524421273)
            ·
              refine ⟨4550749255036635393315955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6067665673382180524421273 4550749255036635393315955)
              ·
                refine ⟨6826123882554953089973933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4550749255036635393315955 6826123882554953089973933)
                ·
                  refine ⟨2559796455958107408740225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6826123882554953089973933 2559796455958107408740225)
                  ·
                    refine ⟨1919847341968580556555169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2559796455958107408740225 1919847341968580556555169)
                    ·
                      refine ⟨1439885506476435417416377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919847341968580556555169 1439885506476435417416377)
                      ·
                        rfl

theorem cell23_2804167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_2804167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804167 prefixEnd_2804167 := by exact prefixLift 2804167
  have htrace : WordTrace (prefixWord ++ tailWord_2804167) baseStart_2804167 baseEnd_2804167 := by
    simpa [prefixWord, tailWord_2804167, baseEnd_2804167] using wordTrace_append hprefix tailTrace_2804167
  have hstable : (prefixWord ++ tailWord_2804167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804167).length < 2 ^ (prefixWord ++ tailWord_2804167).sum := by decide
  have hdescent : baseEnd_2804167 < baseStart_2804167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804180 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_2804180 : Nat := 118140960795 + 2804180 * 2 ^ 59
def prefixEnd_2804180 : Nat := 4983230072969 + 3 ^ 40 * 2804180 * 2
def baseEnd_2804180 : Nat := 1439892181724943866553817

theorem tailTrace_2804180 : CollatzResearch.WordTrace tailWord_2804180 prefixEnd_2804180 1439892181724943866553817 := by
  unfold tailWord_2804180
  simp only [CollatzResearch.WordTrace]
  refine ⟨51138423490471125330336997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68184564653961500440449329 51138423490471125330336997)
  ·
    refine ⟨9588454404463335999438187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51138423490471125330336997 9588454404463335999438187)
    ·
      refine ⟨14382681606695003999157281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9588454404463335999438187 14382681606695003999157281)
      ·
        refine ⟨10787011205021252999367961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14382681606695003999157281 10787011205021252999367961)
        ·
          refine ⟨8090258403765939749525971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10787011205021252999367961 8090258403765939749525971)
          ·
            refine ⟨12135387605648909624288957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8090258403765939749525971 12135387605648909624288957)
            ·
              refine ⟨4550770352118341109108359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12135387605648909624288957 4550770352118341109108359)
              ·
                refine ⟨6826155528177511663662539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4550770352118341109108359 6826155528177511663662539)
                ·
                  refine ⟨10239233292266267495493809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6826155528177511663662539 10239233292266267495493809)
                  ·
                    refine ⟨7679424969199700621620357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10239233292266267495493809 7679424969199700621620357)
                    ·
                      refine ⟨1439892181724943866553817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7679424969199700621620357 1439892181724943866553817)
                      ·
                        rfl

theorem cell23_2804180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_2804180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804180 prefixEnd_2804180 := by exact prefixLift 2804180
  have htrace : WordTrace (prefixWord ++ tailWord_2804180) baseStart_2804180 baseEnd_2804180 := by
    simpa [prefixWord, tailWord_2804180, baseEnd_2804180] using wordTrace_append hprefix tailTrace_2804180
  have hstable : (prefixWord ++ tailWord_2804180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804180).length < 2 ^ (prefixWord ++ tailWord_2804180).sum := by decide
  have hdescent : baseEnd_2804180 < baseStart_2804180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804200 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_2804200 : Nat := 118140960795 + 2804200 * 2 ^ 59
def prefixEnd_2804200 : Nat := 4983230072969 + 3 ^ 40 * 2804200 * 2
def baseEnd_2804200 : Nat := 1439902451338033788303725

theorem tailTrace_2804200 : CollatzResearch.WordTrace tailWord_2804200 prefixEnd_2804200 1439902451338033788303725 := by
  unfold tailWord_2804200
  simp only [CollatzResearch.WordTrace]
  refine ⟨51138788220434897038201027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68185050960579862717601369 51138788220434897038201027)
  ·
    refine ⟨76708182330652345557301541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51138788220434897038201027 76708182330652345557301541)
    ·
      refine ⟨14382784186997314791994039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76708182330652345557301541 14382784186997314791994039)
      ·
        refine ⟨21574176280495972187991059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14382784186997314791994039 21574176280495972187991059)
        ·
          refine ⟨32361264420743958281986589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21574176280495972187991059 32361264420743958281986589)
          ·
            refine ⟨12135474157778984355744971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32361264420743958281986589 12135474157778984355744971)
            ·
              refine ⟨18203211236668476533617457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12135474157778984355744971 18203211236668476533617457)
              ·
                refine ⟨13652408427501357400213093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18203211236668476533617457 13652408427501357400213093)
                ·
                  refine ⟨2559826580156504512539955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13652408427501357400213093 2559826580156504512539955)
                  ·
                    refine ⟨3839739870234756768809933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2559826580156504512539955 3839739870234756768809933)
                    ·
                      refine ⟨1439902451338033788303725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3839739870234756768809933 1439902451338033788303725)
                      ·
                        rfl

theorem cell23_2804200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_2804200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804200 prefixEnd_2804200 := by exact prefixLift 2804200
  have htrace : WordTrace (prefixWord ++ tailWord_2804200) baseStart_2804200 baseEnd_2804200 := by
    simpa [prefixWord, tailWord_2804200, baseEnd_2804200] using wordTrace_append hprefix tailTrace_2804200
  have hstable : (prefixWord ++ tailWord_2804200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804200).length < 2 ^ (prefixWord ++ tailWord_2804200).sum := by decide
  have hdescent : baseEnd_2804200 < baseStart_2804200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804244 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_2804244 : Nat := 118140960795 + 2804244 * 2 ^ 59
def prefixEnd_2804244 : Nat := 4983230072969 + 3 ^ 40 * 2804244 * 2
def baseEnd_2804244 : Nat := 1439925044486831616153523

theorem tailTrace_2804244 : CollatzResearch.WordTrace tailWord_2804244 prefixEnd_2804244 1439925044486831616153523 := by
  unfold tailWord_2804244
  simp only [CollatzResearch.WordTrace]
  refine ⟨51139590626355194795501893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68186120835140259727335857 51139590626355194795501893)
  ·
    refine ⟨9588673242441599024156605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51139590626355194795501893 9588673242441599024156605)
    ·
      refine ⟨3595752465915599634058727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9588673242441599024156605 3595752465915599634058727)
      ·
        refine ⟨5393628698873399451088091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3595752465915599634058727 5393628698873399451088091)
        ·
          refine ⟨8090443048310099176632137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5393628698873399451088091 8090443048310099176632137)
          ·
            refine ⟨6067832286232574382474103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8090443048310099176632137 6067832286232574382474103)
            ·
              refine ⟨9101748429348861573711155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6067832286232574382474103 9101748429348861573711155)
              ·
                refine ⟨13652622644023292360566733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9101748429348861573711155 13652622644023292360566733)
                ·
                  refine ⟨5119733491508734635212525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13652622644023292360566733 5119733491508734635212525)
                  ·
                    refine ⟨1919900059315775488204697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5119733491508734635212525 1919900059315775488204697)
                    ·
                      refine ⟨1439925044486831616153523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919900059315775488204697 1439925044486831616153523)
                      ·
                        rfl

theorem cell23_2804244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_2804244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804244 prefixEnd_2804244 := by exact prefixLift 2804244
  have htrace : WordTrace (prefixWord ++ tailWord_2804244) baseStart_2804244 baseEnd_2804244 := by
    simpa [prefixWord, tailWord_2804244, baseEnd_2804244] using wordTrace_append hprefix tailTrace_2804244
  have hstable : (prefixWord ++ tailWord_2804244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804244).length < 2 ^ (prefixWord ++ tailWord_2804244).sum := by decide
  have hdescent : baseEnd_2804244 < baseStart_2804244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804269 : List Nat := [1, 5, 4, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_2804269 : Nat := 118140960795 + 2804269 * 2 ^ 59
def prefixEnd_2804269 : Nat := 4983230072969 + 3 ^ 40 * 2804269 * 2
def baseEnd_2804269 : Nat := 1439937881503194018340909

theorem tailTrace_2804269 : CollatzResearch.WordTrace tailWord_2804269 prefixEnd_2804269 1439937881503194018340909 := by
  unfold tailWord_2804269
  simp only [CollatzResearch.WordTrace]
  refine ⟨102280093077619818860663861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68186728718413212573775907 102280093077619818860663861)
  ·
    refine ⟨9588758726026858018187237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102280093077619818860663861 9588758726026858018187237)
    ·
      refine ⟨1797892261130035878410107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9588758726026858018187237 1797892261130035878410107)
      ·
        refine ⟨2696838391695053817615161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1797892261130035878410107 2696838391695053817615161)
        ·
          refine ⟨2022628793771290363211371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2696838391695053817615161 2022628793771290363211371)
          ·
            refine ⟨3033943190656935544817057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022628793771290363211371 3033943190656935544817057)
            ·
              refine ⟨2275457392992701658612793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3033943190656935544817057 2275457392992701658612793)
              ·
                refine ⟨1706593044744526243959595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2275457392992701658612793 1706593044744526243959595)
                ·
                  refine ⟨2559889567116789365939393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1706593044744526243959595 2559889567116789365939393)
                  ·
                    refine ⟨1919917175337592024454545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2559889567116789365939393 1919917175337592024454545)
                    ·
                      refine ⟨1439937881503194018340909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919917175337592024454545 1439937881503194018340909)
                      ·
                        rfl

theorem cell23_2804269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_2804269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804269 prefixEnd_2804269 := by exact prefixLift 2804269
  have htrace : WordTrace (prefixWord ++ tailWord_2804269) baseStart_2804269 baseEnd_2804269 := by
    simpa [prefixWord, tailWord_2804269, baseEnd_2804269] using wordTrace_append hprefix tailTrace_2804269
  have hstable : (prefixWord ++ tailWord_2804269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804269).length < 2 ^ (prefixWord ++ tailWord_2804269).sum := by decide
  have hdescent : baseEnd_2804269 < baseStart_2804269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804280 : List Nat := [2, 1, 2, 1, 4, 1, 3, 4, 5]
def baseStart_2804280 : Nat := 118140960795 + 2804280 * 2 ^ 59
def prefixEnd_2804280 : Nat := 4983230072969 + 3 ^ 40 * 2804280 * 2
def baseEnd_2804280 : Nat := 159993725532265941700373

theorem tailTrace_2804280 : CollatzResearch.WordTrace tailWord_2804280 prefixEnd_2804280 159993725532265941700373 := by
  unfold tailWord_2804280
  simp only [CollatzResearch.WordTrace]
  refine ⟨51140247140289983869657147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68186996187053311826209529 51140247140289983869657147)
  ·
    refine ⟨76710370710434975804485721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51140247140289983869657147 76710370710434975804485721)
    ·
      refine ⟨57532778032826231853364291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76710370710434975804485721 57532778032826231853364291)
      ·
        refine ⟨86299167049239347780046437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57532778032826231853364291 86299167049239347780046437)
        ·
          refine ⟨16181093821732377708758707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86299167049239347780046437 16181093821732377708758707)
          ·
            refine ⟨24271640732598566563138061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16181093821732377708758707 24271640732598566563138061)
            ·
              refine ⟨9101865274724462461176773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24271640732598566563138061 9101865274724462461176773)
              ·
                refine ⟨1706599739010836711470645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9101865274724462461176773 1706599739010836711470645)
                ·
                  refine ⟨159993725532265941700373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1706599739010836711470645 159993725532265941700373)
                  ·
                    rfl

theorem cell23_2804280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 5].length) (baseStart_2804280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804280 prefixEnd_2804280 := by exact prefixLift 2804280
  have htrace : WordTrace (prefixWord ++ tailWord_2804280) baseStart_2804280 baseEnd_2804280 := by
    simpa [prefixWord, tailWord_2804280, baseEnd_2804280] using wordTrace_append hprefix tailTrace_2804280
  have hstable : (prefixWord ++ tailWord_2804280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804280).length < 2 ^ (prefixWord ++ tailWord_2804280).sum := by decide
  have hdescent : baseEnd_2804280 < baseStart_2804280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804300 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 2, 5, 2]
def baseStart_2804300 : Nat := 118140960795 + 2804300 * 2 ^ 59
def prefixEnd_2804300 : Nat := 4983230072969 + 3 ^ 40 * 2804300 * 2
def baseEnd_2804300 : Nat := 1439953799403483397053265

theorem tailTrace_2804300 : CollatzResearch.WordTrace tailWord_2804300 prefixEnd_2804300 1439953799403483397053265 := by
  unfold tailWord_2804300
  simp only [CollatzResearch.WordTrace]
  refine ⟨51140611870253755577521177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68187482493671674103361569 51140611870253755577521177)
  ·
    refine ⟨38355458902690316683140883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51140611870253755577521177 38355458902690316683140883)
    ·
      refine ⟨57533188354035475024711325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38355458902690316683140883 57533188354035475024711325)
      ·
        refine ⟨21574945632763303134266747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57533188354035475024711325 21574945632763303134266747)
        ·
          refine ⟨32362418449144954701400121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21574945632763303134266747 32362418449144954701400121)
          ·
            refine ⟨24271813836858716026050091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32362418449144954701400121 24271813836858716026050091)
            ·
              refine ⟨36407720755288074039075137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24271813836858716026050091 36407720755288074039075137)
              ·
                refine ⟨27305790566466055529306353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36407720755288074039075137 27305790566466055529306353)
                ·
                  refine ⟨20479342924849541646979765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27305790566466055529306353 20479342924849541646979765)
                  ·
                    refine ⟨1919938399204644529404353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20479342924849541646979765 1919938399204644529404353)
                    ·
                      refine ⟨1439953799403483397053265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1919938399204644529404353 1439953799403483397053265)
                      ·
                        rfl

theorem cell23_2804300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_2804300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804300 prefixEnd_2804300 := by exact prefixLift 2804300
  have htrace : WordTrace (prefixWord ++ tailWord_2804300) baseStart_2804300 baseEnd_2804300 := by
    simpa [prefixWord, tailWord_2804300, baseEnd_2804300] using wordTrace_append hprefix tailTrace_2804300
  have hstable : (prefixWord ++ tailWord_2804300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804300).length < 2 ^ (prefixWord ++ tailWord_2804300).sum := by decide
  have hdescent : baseEnd_2804300 < baseStart_2804300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804330 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_2804330 : Nat := 118140960795 + 2804330 * 2 ^ 59
def prefixEnd_2804330 : Nat := 4983230072969 + 3 ^ 40 * 2804330 * 2
def baseEnd_2804330 : Nat := 1439969203823118279678127

theorem tailTrace_2804330 : CollatzResearch.WordTrace tailWord_2804330 prefixEnd_2804330 1439969203823118279678127 := by
  unfold tailWord_2804330
  simp only [CollatzResearch.WordTrace]
  refine ⟨25570579482599706569658611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68188211953599217519089629 25570579482599706569658611)
  ·
    refine ⟨38355869223899559854487917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25570579482599706569658611 38355869223899559854487917)
    ·
      refine ⟨14383450958962334945432969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38355869223899559854487917 14383450958962334945432969)
      ·
        refine ⟨10787588219221751209074727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14383450958962334945432969 10787588219221751209074727)
        ·
          refine ⟨16181382328832626813612091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10787588219221751209074727 16181382328832626813612091)
          ·
            refine ⟨24272073493248940220418137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16181382328832626813612091 24272073493248940220418137)
            ·
              refine ⟨18204055119936705165313603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24272073493248940220418137 18204055119936705165313603)
              ·
                refine ⟨27306082679905057747970405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18204055119936705165313603 27306082679905057747970405)
                ·
                  refine ⟨5119890502482198327744451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27306082679905057747970405 5119890502482198327744451)
                  ·
                    refine ⟨7679835753723297491616677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5119890502482198327744451 7679835753723297491616677)
                    ·
                      refine ⟨1439969203823118279678127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7679835753723297491616677 1439969203823118279678127)
                      ·
                        rfl

theorem cell23_2804330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_2804330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804330 prefixEnd_2804330 := by exact prefixLift 2804330
  have htrace : WordTrace (prefixWord ++ tailWord_2804330) baseStart_2804330 baseEnd_2804330 := by
    simpa [prefixWord, tailWord_2804330, baseEnd_2804330] using wordTrace_append hprefix tailTrace_2804330
  have hstable : (prefixWord ++ tailWord_2804330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804330).length < 2 ^ (prefixWord ++ tailWord_2804330).sum := by decide
  have hdescent : baseEnd_2804330 < baseStart_2804330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804370 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 8]
def baseStart_2804370 : Nat := 118140960795 + 2804370 * 2 ^ 59
def prefixEnd_2804370 : Nat := 4983230072969 + 3 ^ 40 * 2804370 * 2
def baseEnd_2804370 : Nat := 159998860338810902575327

theorem tailTrace_2804370 : CollatzResearch.WordTrace tailWord_2804370 prefixEnd_2804370 159998860338810902575327 := by
  unfold tailWord_2804370
  simp only [CollatzResearch.WordTrace]
  refine ⟨25570944212563478277522641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68189184566835942073393709 25570944212563478277522641)
  ·
    refine ⟨19178208159422608708141981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25570944212563478277522641 19178208159422608708141981)
    ·
      refine ⟨7191828059783478265553243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19178208159422608708141981 7191828059783478265553243)
      ·
        refine ⟨10787742089675217398329865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7191828059783478265553243 10787742089675217398329865)
        ·
          refine ⟨8090806567256413048747399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10787742089675217398329865 8090806567256413048747399)
          ·
            refine ⟨12136209850884619573121099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8090806567256413048747399 12136209850884619573121099)
            ·
              refine ⟨18204314776326929359681649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12136209850884619573121099 18204314776326929359681649)
              ·
                refine ⟨13653236082245197019761237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18204314776326929359681649 13653236082245197019761237)
                ·
                  refine ⟨159998860338810902575327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13653236082245197019761237 159998860338810902575327)
                  ·
                    rfl

theorem cell23_2804370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_2804370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804370 prefixEnd_2804370 := by exact prefixLift 2804370
  have htrace : WordTrace (prefixWord ++ tailWord_2804370) baseStart_2804370 baseEnd_2804370 := by
    simpa [prefixWord, tailWord_2804370, baseEnd_2804370] using wordTrace_append hprefix tailTrace_2804370
  have hstable : (prefixWord ++ tailWord_2804370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804370).length < 2 ^ (prefixWord ++ tailWord_2804370).sum := by decide
  have hdescent : baseEnd_2804370 < baseStart_2804370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804391 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 3, 4]
def baseStart_2804391 : Nat := 118140960795 + 2804391 * 2 ^ 59
def prefixEnd_2804391 : Nat := 4983230072969 + 3 ^ 40 * 2804391 * 2
def baseEnd_2804391 : Nat := 480000175381014180338449

theorem tailTrace_2804391 : CollatzResearch.WordTrace tailWord_2804391 prefixEnd_2804391 480000175381014180338449 := by
  unfold tailWord_2804391
  simp only [CollatzResearch.WordTrace]
  refine ⟨102284542783177833696605027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68189695188785222464403351 102284542783177833696605027)
  ·
    refine ⟨153426814174766750544907541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102284542783177833696605027 153426814174766750544907541)
    ·
      refine ⟨7191881914442191431792541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 153426814174766750544907541 7191881914442191431792541)
      ·
        refine ⟨2696955717915821786922203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7191881914442191431792541 2696955717915821786922203)
        ·
          refine ⟨4045433576873732680383305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2696955717915821786922203 4045433576873732680383305)
          ·
            refine ⟨3034075182655299510287479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4045433576873732680383305 3034075182655299510287479)
            ·
              refine ⟨4551112773982949265431219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034075182655299510287479 4551112773982949265431219)
              ·
                refine ⟨6826669160974423898146829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4551112773982949265431219 6826669160974423898146829)
                ·
                  refine ⟨2560000935365408961805061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6826669160974423898146829 2560000935365408961805061)
                  ·
                    refine ⟨480000175381014180338449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2560000935365408961805061 480000175381014180338449)
                    ·
                      rfl

theorem cell23_2804391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_2804391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804391 prefixEnd_2804391 := by exact prefixLift 2804391
  have htrace : WordTrace (prefixWord ++ tailWord_2804391) baseStart_2804391 baseEnd_2804391 := by
    simpa [prefixWord, tailWord_2804391, baseEnd_2804391] using wordTrace_append hprefix tailTrace_2804391
  have hstable : (prefixWord ++ tailWord_2804391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804391).length < 2 ^ (prefixWord ++ tailWord_2804391).sum := by decide
  have hdescent : baseEnd_2804391 < baseStart_2804391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804424 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 2, 3, 2]
def baseStart_2804424 : Nat := 118140960795 + 2804424 * 2 ^ 59
def prefixEnd_2804424 : Nat := 4983230072969 + 3 ^ 40 * 2804424 * 2
def baseEnd_2804424 : Nat := 1440017471004640911902695

theorem tailTrace_2804424 : CollatzResearch.WordTrace tailWord_2804424 prefixEnd_2804424 1440017471004640911902695 := by
  unfold tailWord_2804424
  simp only [CollatzResearch.WordTrace]
  refine ⟨51142873196029140166278163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68190497594705520221704217 51142873196029140166278163)
  ·
    refine ⟨76714309794043710249417245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51142873196029140166278163 76714309794043710249417245)
    ·
      refine ⟨28767866172766391343531467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76714309794043710249417245 28767866172766391343531467)
      ·
        refine ⟨43151799259149587015297201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28767866172766391343531467 43151799259149587015297201)
        ·
          refine ⟨32363849444362190261472901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43151799259149587015297201 32363849444362190261472901)
          ·
            refine ⟨6068221770817910674026169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32363849444362190261472901 6068221770817910674026169)
            ·
              refine ⟨4551166328113433005519627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6068221770817910674026169 4551166328113433005519627)
              ·
                refine ⟨6826749492170149508279441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4551166328113433005519627 6826749492170149508279441)
                ·
                  refine ⟨5120062119127612131209581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6826749492170149508279441 5120062119127612131209581)
                  ·
                    refine ⟨1920023294672854549203593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5120062119127612131209581 1920023294672854549203593)
                    ·
                      refine ⟨1440017471004640911902695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1920023294672854549203593 1440017471004640911902695)
                      ·
                        rfl

theorem cell23_2804424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_2804424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804424 prefixEnd_2804424 := by exact prefixLift 2804424
  have htrace : WordTrace (prefixWord ++ tailWord_2804424) baseStart_2804424 baseEnd_2804424 := by
    simpa [prefixWord, tailWord_2804424, baseEnd_2804424] using wordTrace_append hprefix tailTrace_2804424
  have hstable : (prefixWord ++ tailWord_2804424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804424).length < 2 ^ (prefixWord ++ tailWord_2804424).sum := by decide
  have hdescent : baseEnd_2804424 < baseStart_2804424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804430 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 3, 6]
def baseStart_2804430 : Nat := 118140960795 + 2804430 * 2 ^ 59
def prefixEnd_2804430 : Nat := 4983230072969 + 3 ^ 40 * 2804430 * 2
def baseEnd_2804430 : Nat := 480006850629522629475889

theorem tailTrace_2804430 : CollatzResearch.WordTrace tailWord_2804430 prefixEnd_2804430 480006850629522629475889 := by
  unfold tailWord_2804430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12785745653754567919659343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68190643486691028904849829 12785745653754567919659343)
  ·
    refine ⟨19178618480631851879489015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12785745653754567919659343 19178618480631851879489015)
    ·
      refine ⟨28767927720947777819233523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19178618480631851879489015 28767927720947777819233523)
      ·
        refine ⟨43151891581421666728850285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28767927720947777819233523 43151891581421666728850285)
        ·
          refine ⟨16181959343033125023318857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43151891581421666728850285 16181959343033125023318857)
          ·
            refine ⟨12136469507274843767489143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16181959343033125023318857 12136469507274843767489143)
            ·
              refine ⟨18204704260912265651233715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12136469507274843767489143 18204704260912265651233715)
              ·
                refine ⟨27307056391368398476850573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18204704260912265651233715 27307056391368398476850573)
                ·
                  refine ⟨10240146146763149428818965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27307056391368398476850573 10240146146763149428818965)
                  ·
                    refine ⟨480006850629522629475889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10240146146763149428818965 480006850629522629475889)
                    ·
                      rfl

theorem cell23_2804430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_2804430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804430 prefixEnd_2804430 := by exact prefixLift 2804430
  have htrace : WordTrace (prefixWord ++ tailWord_2804430) baseStart_2804430 baseEnd_2804430 := by
    simpa [prefixWord, tailWord_2804430, baseEnd_2804430] using wordTrace_append hprefix tailTrace_2804430
  have hstable : (prefixWord ++ tailWord_2804430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804430).length < 2 ^ (prefixWord ++ tailWord_2804430).sum := by decide
  have hdescent : baseEnd_2804430 < baseStart_2804430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804447 : List Nat := [1, 1, 2, 3, 2, 3, 1, 4, 2, 4]
def baseStart_2804447 : Nat := 118140960795 + 2804447 * 2 ^ 59
def prefixEnd_2804447 : Nat := 4983230072969 + 3 ^ 40 * 2804447 * 2
def baseEnd_2804447 : Nat := 480009760353231440638363

theorem tailTrace_2804447 : CollatzResearch.WordTrace tailWord_2804447 prefixEnd_2804447 480009760353231440638363 := by
  unfold tailWord_2804447
  simp only [CollatzResearch.WordTrace]
  refine ⟨102286585270974955260643595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68191056847316636840429063 102286585270974955260643595)
  ·
    refine ⟨153429877906462432890965393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102286585270974955260643595 153429877906462432890965393)
    ·
      refine ⟨115072408429846824668224045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153429877906462432890965393 115072408429846824668224045)
      ·
        refine ⟨43152153161192559250584017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115072408429846824668224045 43152153161192559250584017)
        ·
          refine ⟨32364114870894419437938013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43152153161192559250584017 32364114870894419437938013)
          ·
            refine ⟨12136543076585407289226755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32364114870894419437938013 12136543076585407289226755)
            ·
              refine ⟨18204814614878110933840133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12136543076585407289226755 18204814614878110933840133)
              ·
                refine ⟨3413402740289645800095025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18204814614878110933840133 3413402740289645800095025)
                ·
                  refine ⟨2560052055217234350071269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3413402740289645800095025 2560052055217234350071269)
                  ·
                    refine ⟨480009760353231440638363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2560052055217234350071269 480009760353231440638363)
                    ·
                      rfl

theorem cell23_2804447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 4].length) (baseStart_2804447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804447 prefixEnd_2804447 := by exact prefixLift 2804447
  have htrace : WordTrace (prefixWord ++ tailWord_2804447) baseStart_2804447 baseEnd_2804447 := by
    simpa [prefixWord, tailWord_2804447, baseEnd_2804447] using wordTrace_append hprefix tailTrace_2804447
  have hstable : (prefixWord ++ tailWord_2804447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804447).length < 2 ^ (prefixWord ++ tailWord_2804447).sum := by decide
  have hdescent : baseEnd_2804447 < baseStart_2804447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804488 : List Nat := [2, 1, 3, 2, 2, 3, 2, 3, 1, 2, 2]
def baseStart_2804488 : Nat := 118140960795 + 2804488 * 2 ^ 59
def prefixEnd_2804488 : Nat := 4983230072969 + 3 ^ 40 * 2804488 * 2
def baseEnd_2804488 : Nat := 1440050333766528661502401

theorem tailTrace_2804488 : CollatzResearch.WordTrace tailWord_2804488 prefixEnd_2804488 1440050333766528661502401 := by
  unfold tailWord_2804488
  simp only [CollatzResearch.WordTrace]
  refine ⟨51144040331913209631443059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68192053775884279508590745 51144040331913209631443059)
  ·
    refine ⟨76716060497869814447164589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51144040331913209631443059 76716060497869814447164589)
    ·
      refine ⟨28768522686701180417686721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76716060497869814447164589 28768522686701180417686721)
      ·
        refine ⟨21576392015025885313265041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28768522686701180417686721 21576392015025885313265041)
        ·
          refine ⟨16182294011269413984948781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21576392015025885313265041 16182294011269413984948781)
          ·
            refine ⟨6068360254226030244355793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16182294011269413984948781 6068360254226030244355793)
            ·
              refine ⟨4551270190669522683266845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6068360254226030244355793 4551270190669522683266845)
              ·
                refine ⟨1706726321501071006225067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4551270190669522683266845 1706726321501071006225067)
                ·
                  refine ⟨2560089482251606509337601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1706726321501071006225067 2560089482251606509337601)
                  ·
                    refine ⟨1920067111688704882003201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2560089482251606509337601 1920067111688704882003201)
                    ·
                      refine ⟨1440050333766528661502401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1920067111688704882003201 1440050333766528661502401)
                      ·
                        rfl

theorem cell23_2804488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_2804488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804488 prefixEnd_2804488 := by exact prefixLift 2804488
  have htrace : WordTrace (prefixWord ++ tailWord_2804488) baseStart_2804488 baseEnd_2804488 := by
    simpa [prefixWord, tailWord_2804488, baseEnd_2804488] using wordTrace_append hprefix tailTrace_2804488
  have hstable : (prefixWord ++ tailWord_2804488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804488).length < 2 ^ (prefixWord ++ tailWord_2804488).sum := by decide
  have hdescent : baseEnd_2804488 < baseStart_2804488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804498 : List Nat := [3, 2, 4, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2804498 : Nat := 118140960795 + 2804498 * 2 ^ 59
def prefixEnd_2804498 : Nat := 4983230072969 + 3 ^ 40 * 2804498 * 2
def baseEnd_2804498 : Nat := 480018489524357874125785

theorem tailTrace_2804498 : CollatzResearch.WordTrace tailWord_2804498 prefixEnd_2804498 480018489524357874125785 := by
  unfold tailWord_2804498
  simp only [CollatzResearch.WordTrace]
  refine ⟨25572111348447547742687537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68192296929193460647166765 25572111348447547742687537)
  ·
    refine ⟨19179083511335660807015653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25572111348447547742687537 19179083511335660807015653)
    ·
      refine ⟨3596078158375436401315435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19179083511335660807015653 3596078158375436401315435)
      ·
        refine ⟨5394117237563154601973153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3596078158375436401315435 5394117237563154601973153)
        ·
          refine ⟨4045587928172365951479865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5394117237563154601973153 4045587928172365951479865)
          ·
            refine ⟨3034190946129274463609899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4045587928172365951479865 3034190946129274463609899)
            ·
              refine ⟨4551286419193911695414849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034190946129274463609899 4551286419193911695414849)
              ·
                refine ⟨3413464814395433771561137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4551286419193911695414849 3413464814395433771561137)
                ·
                  refine ⟨2560098610796575328670853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3413464814395433771561137 2560098610796575328670853)
                  ·
                    refine ⟨480018489524357874125785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2560098610796575328670853 480018489524357874125785)
                    ·
                      rfl

theorem cell23_2804498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2804498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804498 prefixEnd_2804498 := by exact prefixLift 2804498
  have htrace : WordTrace (prefixWord ++ tailWord_2804498) baseStart_2804498 baseEnd_2804498 := by
    simpa [prefixWord, tailWord_2804498, baseEnd_2804498] using wordTrace_append hprefix tailTrace_2804498
  have hstable : (prefixWord ++ tailWord_2804498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804498).length < 2 ^ (prefixWord ++ tailWord_2804498).sum := by decide
  have hdescent : baseEnd_2804498 < baseStart_2804498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804531 : List Nat := [1, 1, 1, 2, 6, 2, 2, 2, 1, 3, 2]
def baseStart_2804531 : Nat := 118140960795 + 2804531 * 2 ^ 59
def prefixEnd_2804531 : Nat := 4983230072969 + 3 ^ 40 * 2804531 * 2
def baseEnd_2804531 : Nat := 1440072413434671993264703

theorem tailTrace_2804531 : CollatzResearch.WordTrace tailWord_2804531 prefixEnd_2804531 1440072413434671993264703 := by
  unfold tailWord_2804531
  simp only [CollatzResearch.WordTrace]
  refine ⟨102289649002670637606701447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68193099335113758404467631 102289649002670637606701447)
  ·
    refine ⟨153434473504005956410052171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102289649002670637606701447 153434473504005956410052171)
    ·
      refine ⟨230151710256008934615078257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153434473504005956410052171 230151710256008934615078257)
      ·
        refine ⟨172613782692006700961308693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230151710256008934615078257 172613782692006700961308693)
        ·
          refine ⟨8091271063687814107561345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 172613782692006700961308693 8091271063687814107561345)
          ·
            refine ⟨6068453297765860580671009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8091271063687814107561345 6068453297765860580671009)
            ·
              refine ⟨4551339973324395435503257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6068453297765860580671009 4551339973324395435503257)
              ·
                refine ⟨3413504979993296576627443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4551339973324395435503257 3413504979993296576627443)
                ·
                  refine ⟨5120257469989944864941165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3413504979993296576627443 5120257469989944864941165)
                  ·
                    refine ⟨1920096551246229324352937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5120257469989944864941165 1920096551246229324352937)
                    ·
                      refine ⟨1440072413434671993264703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1920096551246229324352937 1440072413434671993264703)
                      ·
                        rfl

theorem cell23_2804531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 3, 2].length) (baseStart_2804531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804531 prefixEnd_2804531 := by exact prefixLift 2804531
  have htrace : WordTrace (prefixWord ++ tailWord_2804531) baseStart_2804531 baseEnd_2804531 := by
    simpa [prefixWord, tailWord_2804531, baseEnd_2804531] using wordTrace_append hprefix tailTrace_2804531
  have hstable : (prefixWord ++ tailWord_2804531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804531).length < 2 ^ (prefixWord ++ tailWord_2804531).sum := by decide
  have hdescent : baseEnd_2804531 < baseStart_2804531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804567 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 7]
def baseStart_2804567 : Nat := 118140960795 + 2804567 * 2 ^ 59
def prefixEnd_2804567 : Nat := 4983230072969 + 3 ^ 40 * 2804567 * 2
def baseEnd_2804567 : Nat := 160010099859803761379393

theorem tailTrace_2804567 : CollatzResearch.WordTrace tailWord_2804567 prefixEnd_2804567 160010099859803761379393 := by
  unfold tailWord_2804567
  simp only [CollatzResearch.WordTrace]
  refine ⟨102290962030540215755011955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68193974687026810503341303 102290962030540215755011955)
  ·
    refine ⟨153436443045810323632517933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102290962030540215755011955 153436443045810323632517933)
    ·
      refine ⟨57538666142178871362194225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153436443045810323632517933 57538666142178871362194225)
      ·
        refine ⟨43153999606634153521645669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57538666142178871362194225 43153999606634153521645669)
        ·
          refine ⟨8091374926243903785308563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43153999606634153521645669 8091374926243903785308563)
          ·
            refine ⟨12137062389365855677962845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8091374926243903785308563 12137062389365855677962845)
            ·
              refine ⟨4551398396012195879236067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12137062389365855677962845 4551398396012195879236067)
              ·
                refine ⟨6827097594018293818854101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4551398396012195879236067 6827097594018293818854101)
                ·
                  refine ⟨160010099859803761379393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6827097594018293818854101 160010099859803761379393)
                  ·
                    rfl

theorem cell23_2804567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 7].length) (baseStart_2804567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804567 prefixEnd_2804567 := by exact prefixLift 2804567
  have htrace : WordTrace (prefixWord ++ tailWord_2804567) baseStart_2804567 baseEnd_2804567 := by
    simpa [prefixWord, tailWord_2804567, baseEnd_2804567] using wordTrace_append hprefix tailTrace_2804567
  have hstable : (prefixWord ++ tailWord_2804567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804567).length < 2 ^ (prefixWord ++ tailWord_2804567).sum := by decide
  have hdescent : baseEnd_2804567 < baseStart_2804567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804618 : List Nat := [3, 1, 2, 4, 1, 3, 2, 2, 5]
def baseStart_2804618 : Nat := 118140960795 + 2804618 * 2 ^ 59
def prefixEnd_2804618 : Nat := 4983230072969 + 3 ^ 40 * 2804618 * 2
def baseEnd_2804618 : Nat := 160013009583512572541867

theorem tailTrace_2804618 : CollatzResearch.WordTrace tailWord_2804618 prefixEnd_2804618 160013009583512572541867 := by
  unfold tailWord_2804618
  simp only [CollatzResearch.WordTrace]
  refine ⟨25573205538338862866279627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68195214768903634310079005 25573205538338862866279627)
  ·
    refine ⟨38359808307508294299419441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25573205538338862866279627 38359808307508294299419441)
    ·
      refine ⟨28769856230631220724564581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38359808307508294299419441 28769856230631220724564581)
      ·
        refine ⟨5394348043243353885855859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28769856230631220724564581 5394348043243353885855859)
        ·
          refine ⟨8091522064865030828783789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5394348043243353885855859 8091522064865030828783789)
          ·
            refine ⟨3034320774324386560793921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8091522064865030828783789 3034320774324386560793921)
            ·
              refine ⟨2275740580743289920595441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3034320774324386560793921 2275740580743289920595441)
              ·
                refine ⟨1706805435557467440446581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2275740580743289920595441 1706805435557467440446581)
                ·
                  refine ⟨160013009583512572541867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1706805435557467440446581 160013009583512572541867)
                  ·
                    rfl

theorem cell23_2804618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 5].length) (baseStart_2804618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804618 prefixEnd_2804618 := by exact prefixLift 2804618
  have htrace : WordTrace (prefixWord ++ tailWord_2804618) baseStart_2804618 baseEnd_2804618 := by
    simpa [prefixWord, tailWord_2804618, baseEnd_2804618] using wordTrace_append hprefix tailTrace_2804618
  have hstable : (prefixWord ++ tailWord_2804618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804618).length < 2 ^ (prefixWord ++ tailWord_2804618).sum := by decide
  have hdescent : baseEnd_2804618 < baseStart_2804618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804644 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 3, 4]
def baseStart_2804644 : Nat := 118140960795 + 2804644 * 2 ^ 59
def prefixEnd_2804644 : Nat := 4983230072969 + 3 ^ 40 * 2804644 * 2
def baseEnd_2804644 : Nat := 480043478916210017050561

theorem tailTrace_2804644 : CollatzResearch.WordTrace tailWord_2804644 prefixEnd_2804644 480043478916210017050561 := by
  unfold tailWord_2804644
  simp only [CollatzResearch.WordTrace]
  refine ⟨51146885225630628952782493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68195846967507505270376657 51146885225630628952782493)
  ·
    refine ⟨19180081959611485857293435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51146885225630628952782493 19180081959611485857293435)
    ·
      refine ⟨28770122939417228785940153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19180081959611485857293435 28770122939417228785940153)
      ·
        refine ⟨21577592204562921589455115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28770122939417228785940153 21577592204562921589455115)
        ·
          refine ⟨32366388306844382384182673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21577592204562921589455115 32366388306844382384182673)
          ·
            refine ⟨24274791230133286788137005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32366388306844382384182673 24274791230133286788137005)
            ·
              refine ⟨9103046711299982545551377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24274791230133286788137005 9103046711299982545551377)
              ·
                refine ⟨6827285033474986909163533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9103046711299982545551377 6827285033474986909163533)
                ·
                  refine ⟨2560231887553120090936325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6827285033474986909163533 2560231887553120090936325)
                  ·
                    refine ⟨480043478916210017050561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2560231887553120090936325 480043478916210017050561)
                    ·
                      rfl

theorem cell23_2804644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_2804644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804644 prefixEnd_2804644 := by exact prefixLift 2804644
  have htrace : WordTrace (prefixWord ++ tailWord_2804644) baseStart_2804644 baseEnd_2804644 := by
    simpa [prefixWord, tailWord_2804644, baseEnd_2804644] using wordTrace_append hprefix tailTrace_2804644
  have hstable : (prefixWord ++ tailWord_2804644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804644).length < 2 ^ (prefixWord ++ tailWord_2804644).sum := by decide
  have hdescent : baseEnd_2804644 < baseStart_2804644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804711 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 1, 5, 2]
def baseStart_2804711 : Nat := 118140960795 + 2804711 * 2 ^ 59
def prefixEnd_2804711 : Nat := 4983230072969 + 3 ^ 40 * 2804711 * 2
def baseEnd_2804711 : Nat := 1440164839952481289013875

theorem tailTrace_2804711 : CollatzResearch.WordTrace tailWord_2804711 prefixEnd_2804711 1440164839952481289013875 := by
  unfold tailWord_2804711
  simp only [CollatzResearch.WordTrace]
  refine ⟨102296214142018528348253987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68197476094679018898835991 102296214142018528348253987)
  ·
    refine ⟨153444321213027792522380981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102296214142018528348253987 153444321213027792522380981)
    ·
      refine ⟨14385405113721355548973217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153444321213027792522380981 14385405113721355548973217)
      ·
        refine ⟨10789053835291016661729913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14385405113721355548973217 10789053835291016661729913)
        ·
          refine ⟨8091790376468262496297435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10789053835291016661729913 8091790376468262496297435)
          ·
            refine ⟨12137685564702393744446153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8091790376468262496297435 12137685564702393744446153)
            ·
              refine ⟨9103264173526795308334615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12137685564702393744446153 9103264173526795308334615)
              ·
                refine ⟨13654896260290192962501923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9103264173526795308334615 13654896260290192962501923)
                ·
                  refine ⟨20482344390435289443752885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13654896260290192962501923 20482344390435289443752885)
                  ·
                    refine ⟨1920219786603308385351833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20482344390435289443752885 1920219786603308385351833)
                    ·
                      refine ⟨1440164839952481289013875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1920219786603308385351833 1440164839952481289013875)
                      ·
                        rfl

theorem cell23_2804711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_2804711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804711 prefixEnd_2804711 := by exact prefixLift 2804711
  have htrace : WordTrace (prefixWord ++ tailWord_2804711) baseStart_2804711 baseEnd_2804711 := by
    simpa [prefixWord, tailWord_2804711, baseEnd_2804711] using wordTrace_append hprefix tailTrace_2804711
  have hstable : (prefixWord ++ tailWord_2804711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804711).length < 2 ^ (prefixWord ++ tailWord_2804711).sum := by decide
  have hdescent : baseEnd_2804711 < baseStart_2804711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804744 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_2804744 : Nat := 118140960795 + 2804744 * 2 ^ 59
def prefixEnd_2804744 : Nat := 4983230072969 + 3 ^ 40 * 2804744 * 2
def baseEnd_2804744 : Nat := 1440181784814079659901223

theorem tailTrace_2804744 : CollatzResearch.WordTrace tailWord_2804744 prefixEnd_2804744 1440181784814079659901223 := by
  unfold tailWord_2804744
  simp only [CollatzResearch.WordTrace]
  refine ⟨51148708875449487492102643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68198278500599316656136857 51148708875449487492102643)
  ·
    refine ⟨76723063313174231238153965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51148708875449487492102643 76723063313174231238153965)
    ·
      refine ⟨28771148742440336714307737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76723063313174231238153965 28771148742440336714307737)
      ·
        refine ⟨21578361556830252535730803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28771148742440336714307737 21578361556830252535730803)
        ·
          refine ⟨32367542335245378803596205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21578361556830252535730803 32367542335245378803596205)
          ·
            refine ⟨12137828375717017051348577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32367542335245378803596205 12137828375717017051348577)
            ·
              refine ⟨9103371281787762788511433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12137828375717017051348577 9103371281787762788511433)
              ·
                refine ⟨6827528461340822091383575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9103371281787762788511433 6827528461340822091383575)
                ·
                  refine ⟨10241292692011233137075363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6827528461340822091383575 10241292692011233137075363)
                  ·
                    refine ⟨15361939038016849705613045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10241292692011233137075363 15361939038016849705613045)
                    ·
                      refine ⟨1440181784814079659901223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15361939038016849705613045 1440181784814079659901223)
                      ·
                        rfl

theorem cell23_2804744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_2804744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804744 prefixEnd_2804744 := by exact prefixLift 2804744
  have htrace : WordTrace (prefixWord ++ tailWord_2804744) baseStart_2804744 baseEnd_2804744 := by
    simpa [prefixWord, tailWord_2804744, baseEnd_2804744] using wordTrace_append hprefix tailTrace_2804744
  have hstable : (prefixWord ++ tailWord_2804744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804744).length < 2 ^ (prefixWord ++ tailWord_2804744).sum := by decide
  have hdescent : baseEnd_2804744 < baseStart_2804744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804747 : List Nat := [1, 1, 1, 1, 6, 2, 1, 10]
def baseStart_2804747 : Nat := 118140960795 + 2804747 * 2 ^ 59
def prefixEnd_2804747 : Nat := 4983230072969 + 3 ^ 40 * 2804747 * 2
def baseEnd_2804747 : Nat := 53340123157631227709767

theorem tailTrace_2804747 : CollatzResearch.WordTrace tailWord_2804747 prefixEnd_2804747 53340123157631227709767 := by
  unfold tailWord_2804747
  simp only [CollatzResearch.WordTrace]
  refine ⟨102297527169888106496564495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68198351446592070997709663 102297527169888106496564495)
  ·
    refine ⟨153446290754832159744846743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102297527169888106496564495 153446290754832159744846743)
    ·
      refine ⟨230169436132248239617270115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153446290754832159744846743 230169436132248239617270115)
      ·
        refine ⟨345254154198372359425905173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230169436132248239617270115 345254154198372359425905173)
        ·
          refine ⟨16183788478048704348089305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 345254154198372359425905173 16183788478048704348089305)
          ·
            refine ⟨12137841358536528261066979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16183788478048704348089305 12137841358536528261066979)
            ·
              refine ⟨18206762037804792391600469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12137841358536528261066979 18206762037804792391600469)
              ·
                refine ⟨53340123157631227709767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18206762037804792391600469 53340123157631227709767)
                ·
                  rfl

theorem cell23_2804747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 10].length) (baseStart_2804747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804747 prefixEnd_2804747 := by exact prefixLift 2804747
  have htrace : WordTrace (prefixWord ++ tailWord_2804747) baseStart_2804747 baseEnd_2804747 := by
    simpa [prefixWord, tailWord_2804747, baseEnd_2804747] using wordTrace_append hprefix tailTrace_2804747
  have hstable : (prefixWord ++ tailWord_2804747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804747).length < 2 ^ (prefixWord ++ tailWord_2804747).sum := by decide
  have hdescent : baseEnd_2804747 < baseStart_2804747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804761 : List Nat := [1, 2, 1, 2, 1, 1, 7, 2, 1, 2, 3]
def baseStart_2804761 : Nat := 118140960795 + 2804761 * 2 ^ 59
def prefixEnd_2804761 : Nat := 4983230072969 + 3 ^ 40 * 2804761 * 2
def baseEnd_2804761 : Nat := 1440190513985206093388645

theorem tailTrace_2804761 : CollatzResearch.WordTrace tailWord_2804761 prefixEnd_2804761 1440190513985206093388645 := by
  unfold tailWord_2804761
  simp only [CollatzResearch.WordTrace]
  refine ⟨102298037791837386887574137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68198691861224924591716091 102298037791837386887574137)
  ·
    refine ⟨76723528343878040165680603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102298037791837386887574137 76723528343878040165680603)
    ·
      refine ⟨115085292515817060248520905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76723528343878040165680603 115085292515817060248520905)
      ·
        refine ⟨86313969386862795186390679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115085292515817060248520905 86313969386862795186390679)
        ·
          refine ⟨129470954080294192779586019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86313969386862795186390679 129470954080294192779586019)
          ·
            refine ⟨194206431120441289169379029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129470954080294192779586019 194206431120441289169379029)
            ·
              refine ⟨4551713229385342714907321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 194206431120441289169379029 4551713229385342714907321)
              ·
                refine ⟨3413784922039007036180491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4551713229385342714907321 3413784922039007036180491)
                ·
                  refine ⟨5120677383058510554270737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3413784922039007036180491 5120677383058510554270737)
                  ·
                    refine ⟨3840508037293882915703053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5120677383058510554270737 3840508037293882915703053)
                    ·
                      refine ⟨1440190513985206093388645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3840508037293882915703053 1440190513985206093388645)
                      ·
                        rfl

theorem cell23_2804761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_2804761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804761 prefixEnd_2804761 := by exact prefixLift 2804761
  have htrace : WordTrace (prefixWord ++ tailWord_2804761) baseStart_2804761 baseEnd_2804761 := by
    simpa [prefixWord, tailWord_2804761, baseEnd_2804761] using wordTrace_append hprefix tailTrace_2804761
  have hstable : (prefixWord ++ tailWord_2804761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804761).length < 2 ^ (prefixWord ++ tailWord_2804761).sum := by decide
  have hdescent : baseEnd_2804761 < baseStart_2804761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804775 : List Nat := [1, 1, 7, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_2804775 : Nat := 118140960795 + 2804775 * 2 ^ 59
def prefixEnd_2804775 : Nat := 4983230072969 + 3 ^ 40 * 2804775 * 2
def baseEnd_2804775 : Nat := 1440197702714369038613581

theorem tailTrace_2804775 : CollatzResearch.WordTrace tailWord_2804775 prefixEnd_2804775 1440197702714369038613581 := by
  unfold tailWord_2804775
  simp only [CollatzResearch.WordTrace]
  refine ⟨102298548413786667278583779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68199032275857778185722519 102298548413786667278583779)
  ·
    refine ⟨153447822620680000917875669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102298548413786667278583779 153447822620680000917875669)
    ·
      refine ⟨3596433342672187521512711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 153447822620680000917875669 3596433342672187521512711)
      ·
        refine ⟨5394650014008281282269067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3596433342672187521512711 5394650014008281282269067)
        ·
          refine ⟨8091975021012421923403601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5394650014008281282269067 8091975021012421923403601)
          ·
            refine ⟨6068981265759316442552701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8091975021012421923403601 6068981265759316442552701)
            ·
              refine ⟨2275867974659743665957263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6068981265759316442552701 2275867974659743665957263)
              ·
                refine ⟨3413801961989615498935895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2275867974659743665957263 3413801961989615498935895)
                ·
                  refine ⟨5120702942984423248403843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3413801961989615498935895 5120702942984423248403843)
                  ·
                    refine ⟨7681054414476634872605765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5120702942984423248403843 7681054414476634872605765)
                    ·
                      refine ⟨1440197702714369038613581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7681054414476634872605765 1440197702714369038613581)
                      ·
                        rfl

theorem cell23_2804775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_2804775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804775 prefixEnd_2804775 := by exact prefixLift 2804775
  have htrace : WordTrace (prefixWord ++ tailWord_2804775) baseStart_2804775 baseEnd_2804775 := by
    simpa [prefixWord, tailWord_2804775, baseEnd_2804775] using wordTrace_append hprefix tailTrace_2804775
  have hstable : (prefixWord ++ tailWord_2804775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804775).length < 2 ^ (prefixWord ++ tailWord_2804775).sum := by decide
  have hdescent : baseEnd_2804775 < baseStart_2804775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804778 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_2804778 : Nat := 118140960795 + 2804778 * 2 ^ 59
def prefixEnd_2804778 : Nat := 4983230072969 + 3 ^ 40 * 2804778 * 2
def baseEnd_2804778 : Nat := 1440199243156332526876067

theorem tailTrace_2804778 : CollatzResearch.WordTrace tailWord_2804778 prefixEnd_2804778 1440199243156332526876067 := by
  unfold tailWord_2804778
  simp only [CollatzResearch.WordTrace]
  refine ⟨25574664458193949697735747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68199105221850532527295325 25574664458193949697735747)
  ·
    refine ⟨38361996687290924546603621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25574664458193949697735747 38361996687290924546603621)
    ·
      refine ⟨7192874378867048352488179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38361996687290924546603621 7192874378867048352488179)
      ·
        refine ⟨10789311568300572528732269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7192874378867048352488179 10789311568300572528732269)
        ·
          refine ⟨4045991838112714698274601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10789311568300572528732269 4045991838112714698274601)
          ·
            refine ⟨3034493878584536023705951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4045991838112714698274601 3034493878584536023705951)
            ·
              refine ⟨4551740817876804035558927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034493878584536023705951 4551740817876804035558927)
              ·
                refine ⟨6827611226815206053338391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4551740817876804035558927 6827611226815206053338391)
                ·
                  refine ⟨10241416840222809080007587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6827611226815206053338391 10241416840222809080007587)
                  ·
                    refine ⟨15362125260334213620011381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10241416840222809080007587 15362125260334213620011381)
                    ·
                      refine ⟨1440199243156332526876067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15362125260334213620011381 1440199243156332526876067)
                      ·
                        rfl

theorem cell23_2804778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_2804778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804778 prefixEnd_2804778 := by exact prefixLift 2804778
  have htrace : WordTrace (prefixWord ++ tailWord_2804778) baseStart_2804778 baseEnd_2804778 := by
    simpa [prefixWord, tailWord_2804778, baseEnd_2804778] using wordTrace_append hprefix tailTrace_2804778
  have hstable : (prefixWord ++ tailWord_2804778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804778).length < 2 ^ (prefixWord ++ tailWord_2804778).sum := by decide
  have hdescent : baseEnd_2804778 < baseStart_2804778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804792 : List Nat := [2, 1, 2, 1, 5, 1, 4, 2, 1, 2, 2]
def baseStart_2804792 : Nat := 118140960795 + 2804792 * 2 ^ 59
def prefixEnd_2804792 : Nat := 4983230072969 + 3 ^ 40 * 2804792 * 2
def baseEnd_2804792 : Nat := 1440206431885495472101003

theorem tailTrace_2804792 : CollatzResearch.WordTrace tailWord_2804792 prefixEnd_2804792 1440206431885495472101003 := by
  unfold tailWord_2804792
  simp only [CollatzResearch.WordTrace]
  refine ⟨51149584227362539590976315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68199445636483386121301753 51149584227362539590976315)
  ·
    refine ⟨76724376341043809386464473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51149584227362539590976315 76724376341043809386464473)
    ·
      refine ⟨57543282255782857039848355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76724376341043809386464473 57543282255782857039848355)
      ·
        refine ⟨86314923383674285559772533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57543282255782857039848355 86314923383674285559772533)
        ·
          refine ⟨8092024067219464271228675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86314923383674285559772533 8092024067219464271228675)
          ·
            refine ⟨12138036100829196406843013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8092024067219464271228675 12138036100829196406843013)
            ·
              refine ⟨2275881768905474326283065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12138036100829196406843013 2275881768905474326283065)
              ·
                refine ⟨1706911326679105744712299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2275881768905474326283065 1706911326679105744712299)
                ·
                  refine ⟨2560366990018658617068449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1706911326679105744712299 2560366990018658617068449)
                  ·
                    refine ⟨1920275242513993962801337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2560366990018658617068449 1920275242513993962801337)
                    ·
                      refine ⟨1440206431885495472101003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1920275242513993962801337 1440206431885495472101003)
                      ·
                        rfl

theorem cell23_2804792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 1, 2, 2].length) (baseStart_2804792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804792 prefixEnd_2804792 := by exact prefixLift 2804792
  have htrace : WordTrace (prefixWord ++ tailWord_2804792) baseStart_2804792 baseEnd_2804792 := by
    simpa [prefixWord, tailWord_2804792, baseEnd_2804792] using wordTrace_append hprefix tailTrace_2804792
  have hstable : (prefixWord ++ tailWord_2804792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804792).length < 2 ^ (prefixWord ++ tailWord_2804792).sum := by decide
  have hdescent : baseEnd_2804792 < baseStart_2804792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804814 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_2804814 : Nat := 118140960795 + 2804814 * 2 ^ 59
def prefixEnd_2804814 : Nat := 4983230072969 + 3 ^ 40 * 2804814 * 2
def baseEnd_2804814 : Nat := 1440217728459894386025901

theorem tailTrace_2804814 : CollatzResearch.WordTrace tailWord_2804814 prefixEnd_2804814 1440217728459894386025901 := by
  unfold tailWord_2804814
  simp only [CollatzResearch.WordTrace]
  refine ⟨12787496357580672117406687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68199980573763584626168997 12787496357580672117406687)
  ·
    refine ⟨19181244536371008176110031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12787496357580672117406687 19181244536371008176110031)
    ·
      refine ⟨28771866804556512264165047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19181244536371008176110031 28771866804556512264165047)
      ·
        refine ⟨43157800206834768396247571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28771866804556512264165047 43157800206834768396247571)
        ·
          refine ⟨64736700310252152594371357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43157800206834768396247571 64736700310252152594371357)
          ·
            refine ⟨24276262616344557222889259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64736700310252152594371357 24276262616344557222889259)
            ·
              refine ⟨36414393924516835834333889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24276262616344557222889259 36414393924516835834333889)
              ·
                refine ⟨27310795443387626875750417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36414393924516835834333889 27310795443387626875750417)
                ·
                  refine ⟨20483096582540720156812813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27310795443387626875750417 20483096582540720156812813)
                  ·
                    refine ⟨7681161218452770058804805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20483096582540720156812813 7681161218452770058804805)
                    ·
                      refine ⟨1440217728459894386025901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7681161218452770058804805 1440217728459894386025901)
                      ·
                        rfl

theorem cell23_2804814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_2804814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804814 prefixEnd_2804814 := by exact prefixLift 2804814
  have htrace : WordTrace (prefixWord ++ tailWord_2804814) baseStart_2804814 baseEnd_2804814 := by
    simpa [prefixWord, tailWord_2804814, baseEnd_2804814] using wordTrace_append hprefix tailTrace_2804814
  have hstable : (prefixWord ++ tailWord_2804814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804814).length < 2 ^ (prefixWord ++ tailWord_2804814).sum := by decide
  have hdescent : baseEnd_2804814 < baseStart_2804814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804818 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 3, 3, 2]
def baseStart_2804818 : Nat := 118140960795 + 2804818 * 2 ^ 59
def prefixEnd_2804818 : Nat := 4983230072969 + 3 ^ 40 * 2804818 * 2
def baseEnd_2804818 : Nat := 1440219782382512370375883

theorem tailTrace_2804818 : CollatzResearch.WordTrace tailWord_2804818 prefixEnd_2804818 1440219782382512370375883 := by
  unfold tailWord_2804818
  simp only [CollatzResearch.WordTrace]
  refine ⟨25575029188157721405599777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68200077835087257081599405 25575029188157721405599777)
  ·
    refine ⟨19181271891118291054199833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25575029188157721405599777 19181271891118291054199833)
    ·
      refine ⟨14385953918338718290649875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19181271891118291054199833 14385953918338718290649875)
      ·
        refine ⟨21578930877508077435974813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14385953918338718290649875 21578930877508077435974813)
        ·
          refine ⟨8092099079065529038490555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21578930877508077435974813 8092099079065529038490555)
          ·
            refine ⟨12138148618598293557735833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8092099079065529038490555 12138148618598293557735833)
            ·
              refine ⟨9103611463948720168301875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12138148618598293557735833 9103611463948720168301875)
              ·
                refine ⟨13655417195923080252452813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9103611463948720168301875 13655417195923080252452813)
                ·
                  refine ⟨5120781448471155094669805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13655417195923080252452813 5120781448471155094669805)
                  ·
                    refine ⟨1920293043176683160501177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5120781448471155094669805 1920293043176683160501177)
                    ·
                      refine ⟨1440219782382512370375883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1920293043176683160501177 1440219782382512370375883)
                      ·
                        rfl

theorem cell23_2804818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_2804818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804818 prefixEnd_2804818 := by exact prefixLift 2804818
  have htrace : WordTrace (prefixWord ++ tailWord_2804818) baseStart_2804818 baseEnd_2804818 := by
    simpa [prefixWord, tailWord_2804818, baseEnd_2804818] using wordTrace_append hprefix tailTrace_2804818
  have hstable : (prefixWord ++ tailWord_2804818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804818).length < 2 ^ (prefixWord ++ tailWord_2804818).sum := by decide
  have hdescent : baseEnd_2804818 < baseStart_2804818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804829 : List Nat := [1, 4, 4, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_2804829 : Nat := 118140960795 + 2804829 * 2 ^ 59
def prefixEnd_2804829 : Nat := 4983230072969 + 3 ^ 40 * 2804829 * 2
def baseEnd_2804829 : Nat := 1440225430669711827338333

theorem tailTrace_2804829 : CollatzResearch.WordTrace tailWord_2804829 prefixEnd_2804829 1440225430669711827338333 := by
  unfold tailWord_2804829
  simp only [CollatzResearch.WordTrace]
  refine ⟨102300517955591034501049541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68200345303727356334033027 102300517955591034501049541)
  ·
    refine ⟨19181347116673318968946789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102300517955591034501049541 19181347116673318968946789)
    ·
      refine ⟨3596502584376247306677523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19181347116673318968946789 3596502584376247306677523)
      ·
        refine ⟨5394753876564370960016285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3596502584376247306677523 5394753876564370960016285)
        ·
          refine ⟨2023032703711639110006107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5394753876564370960016285 2023032703711639110006107)
          ·
            refine ⟨3034549055567458665009161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2023032703711639110006107 3034549055567458665009161)
            ·
              refine ⟨2275911791675593998756871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3034549055567458665009161 2275911791675593998756871)
              ·
                refine ⟨3413867687513390998135307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2275911791675593998756871 3413867687513390998135307)
                ·
                  refine ⟨5120801531270086497202961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3413867687513390998135307 5120801531270086497202961)
                  ·
                    refine ⟨3840601148452564872902221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5120801531270086497202961 3840601148452564872902221)
                    ·
                      refine ⟨1440225430669711827338333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3840601148452564872902221 1440225430669711827338333)
                      ·
                        rfl

theorem cell23_2804829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_2804829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804829 prefixEnd_2804829 := by exact prefixLift 2804829
  have htrace : WordTrace (prefixWord ++ tailWord_2804829) baseStart_2804829 baseEnd_2804829 := by
    simpa [prefixWord, tailWord_2804829, baseEnd_2804829] using wordTrace_append hprefix tailTrace_2804829
  have hstable : (prefixWord ++ tailWord_2804829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804829).length < 2 ^ (prefixWord ++ tailWord_2804829).sum := by decide
  have hdescent : baseEnd_2804829 < baseStart_2804829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804831 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 1, 4, 2]
def baseStart_2804831 : Nat := 118140960795 + 2804831 * 2 ^ 59
def prefixEnd_2804831 : Nat := 4983230072969 + 3 ^ 40 * 2804831 * 2
def baseEnd_2804831 : Nat := 1440226457631020819513323

theorem tailTrace_2804831 : CollatzResearch.WordTrace tailWord_2804831 prefixEnd_2804831 1440226457631020819513323 := by
  unfold tailWord_2804831
  simp only [CollatzResearch.WordTrace]
  refine ⟨102300590901583788842622347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68200393934389192561748231 102300590901583788842622347)
  ·
    refine ⟨153450886352375683263933521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102300590901583788842622347 153450886352375683263933521)
    ·
      refine ⟨115088164764281762447950141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153450886352375683263933521 115088164764281762447950141)
      ·
        refine ⟨43158061786605660917981303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115088164764281762447950141 43158061786605660917981303)
        ·
          refine ⟨64737092679908491376971955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43158061786605660917981303 64737092679908491376971955)
          ·
            refine ⟨97105639019862737065457933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64737092679908491376971955 97105639019862737065457933)
            ·
              refine ⟨36414614632448526399546725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97105639019862737065457933 36414614632448526399546725)
              ·
                refine ⟨6827740243584098699915011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36414614632448526399546725 6827740243584098699915011)
                ·
                  refine ⟨10241610365376148049872517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6827740243584098699915011 10241610365376148049872517)
                  ·
                    refine ⟨1920301943508027759351097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10241610365376148049872517 1920301943508027759351097)
                    ·
                      refine ⟨1440226457631020819513323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1920301943508027759351097 1440226457631020819513323)
                      ·
                        rfl

theorem cell23_2804831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_2804831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804831 prefixEnd_2804831 := by exact prefixLift 2804831
  have htrace : WordTrace (prefixWord ++ tailWord_2804831) baseStart_2804831 baseEnd_2804831 := by
    simpa [prefixWord, tailWord_2804831, baseEnd_2804831] using wordTrace_append hprefix tailTrace_2804831
  have hstable : (prefixWord ++ tailWord_2804831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804831).length < 2 ^ (prefixWord ++ tailWord_2804831).sum := by decide
  have hdescent : baseEnd_2804831 < baseStart_2804831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804844 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 4]
def baseStart_2804844 : Nat := 118140960795 + 2804844 * 2 ^ 59
def prefixEnd_2804844 : Nat := 4983230072969 + 3 ^ 40 * 2804844 * 2
def baseEnd_2804844 : Nat := 1440233132879529268650763

theorem tailTrace_2804844 : CollatzResearch.WordTrace tailWord_2804844 prefixEnd_2804844 1440233132879529268650763 := by
  unfold tailWord_2804844
  simp only [CollatzResearch.WordTrace]
  refine ⟨51150532525268346031422793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68200710033691128041897057 51150532525268346031422793)
  ·
    refine ⟨38362899393951259523567095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51150532525268346031422793 38362899393951259523567095)
    ·
      refine ⟨57544349090926889285350643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38362899393951259523567095 57544349090926889285350643)
      ·
        refine ⟨86316523636390333928025965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57544349090926889285350643 86316523636390333928025965)
        ·
          refine ⟨32368696363646375223009737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86316523636390333928025965 32368696363646375223009737)
          ·
            refine ⟨24276522272734781417257303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32368696363646375223009737 24276522272734781417257303)
            ·
              refine ⟨36414783409102172125885955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24276522272734781417257303 36414783409102172125885955)
              ·
                refine ⟨54622175113653258188828933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36414783409102172125885955 54622175113653258188828933)
                ·
                  refine ⟨10241657833809985910405425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54622175113653258188828933 10241657833809985910405425)
                  ·
                    refine ⟨7681243375357489432804069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10241657833809985910405425 7681243375357489432804069)
                    ·
                      refine ⟨1440233132879529268650763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7681243375357489432804069 1440233132879529268650763)
                      ·
                        rfl

theorem cell23_2804844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_2804844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804844 prefixEnd_2804844 := by exact prefixLift 2804844
  have htrace : WordTrace (prefixWord ++ tailWord_2804844) baseStart_2804844 baseEnd_2804844 := by
    simpa [prefixWord, tailWord_2804844, baseEnd_2804844] using wordTrace_append hprefix tailTrace_2804844
  have hstable : (prefixWord ++ tailWord_2804844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804844).length < 2 ^ (prefixWord ++ tailWord_2804844).sum := by decide
  have hdescent : baseEnd_2804844 < baseStart_2804844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804848 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 4, 2, 2]
def baseStart_2804848 : Nat := 118140960795 + 2804848 * 2 ^ 59
def prefixEnd_2804848 : Nat := 4983230072969 + 3 ^ 40 * 2804848 * 2
def baseEnd_2804848 : Nat := 1440235186802147253000745

theorem tailTrace_2804848 : CollatzResearch.WordTrace tailWord_2804848 prefixEnd_2804848 1440235186802147253000745 := by
  unfold tailWord_2804848
  simp only [CollatzResearch.WordTrace]
  refine ⟨51150605471261100372995599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68200807295014800497327465 51150605471261100372995599)
  ·
    refine ⟨76725908206891650559493399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51150605471261100372995599 76725908206891650559493399)
    ·
      refine ⟨115088862310337475839240099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76725908206891650559493399 115088862310337475839240099)
      ·
        refine ⟨172633293465506213758860149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115088862310337475839240099 172633293465506213758860149)
        ·
          refine ⟨16184371262391207539893139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172633293465506213758860149 16184371262391207539893139)
          ·
            refine ⟨24276556893586811309839709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16184371262391207539893139 24276556893586811309839709)
            ·
              refine ⟨9103708835095054241189891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24276556893586811309839709 9103708835095054241189891)
              ·
                refine ⟨13655563252642581361784837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9103708835095054241189891 13655563252642581361784837)
                ·
                  refine ⟨2560418109870484005334657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13655563252642581361784837 2560418109870484005334657)
                  ·
                    refine ⟨1920313582402863004000993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2560418109870484005334657 1920313582402863004000993)
                    ·
                      refine ⟨1440235186802147253000745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1920313582402863004000993 1440235186802147253000745)
                      ·
                        rfl

theorem cell23_2804848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 4, 2, 2].length) (baseStart_2804848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804848 prefixEnd_2804848 := by exact prefixLift 2804848
  have htrace : WordTrace (prefixWord ++ tailWord_2804848) baseStart_2804848 baseEnd_2804848 := by
    simpa [prefixWord, tailWord_2804848, baseEnd_2804848] using wordTrace_append hprefix tailTrace_2804848
  have hstable : (prefixWord ++ tailWord_2804848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804848).length < 2 ^ (prefixWord ++ tailWord_2804848).sum := by decide
  have hdescent : baseEnd_2804848 < baseStart_2804848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804865 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 1, 4, 2]
def baseStart_2804865 : Nat := 118140960795 + 2804865 * 2 ^ 59
def prefixEnd_2804865 : Nat := 4983230072969 + 3 ^ 40 * 2804865 * 2
def baseEnd_2804865 : Nat := 1440243915973273686488167

theorem tailTrace_2804865 : CollatzResearch.WordTrace tailWord_2804865 prefixEnd_2804865 1440243915973273686488167 := by
  unfold tailWord_2804865
  simp only [CollatzResearch.WordTrace]
  refine ⟨102301830983460612649360049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68201220655640408432906699 102301830983460612649360049)
  ·
    refine ⟨76726373237595459487020037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102301830983460612649360049 76726373237595459487020037)
    ·
      refine ⟨14386194982049148653816257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76726373237595459487020037 14386194982049148653816257)
      ·
        refine ⟨10789646236536861490362193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14386194982049148653816257 10789646236536861490362193)
        ·
          refine ⟨8092234677402646117771645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10789646236536861490362193 8092234677402646117771645)
          ·
            refine ⟨3034588004025992294164367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8092234677402646117771645 3034588004025992294164367)
            ·
              refine ⟨4551882006038988441246551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034588004025992294164367 4551882006038988441246551)
              ·
                refine ⟨6827823009058482661869827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4551882006038988441246551 6827823009058482661869827)
                ·
                  refine ⟨10241734513587723992804741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6827823009058482661869827 10241734513587723992804741)
                  ·
                    refine ⟨1920325221297698248650889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10241734513587723992804741 1920325221297698248650889)
                    ·
                      refine ⟨1440243915973273686488167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1920325221297698248650889 1440243915973273686488167)
                      ·
                        rfl

theorem cell23_2804865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_2804865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804865 prefixEnd_2804865 := by exact prefixLift 2804865
  have htrace : WordTrace (prefixWord ++ tailWord_2804865) baseStart_2804865 baseEnd_2804865 := by
    simpa [prefixWord, tailWord_2804865, baseEnd_2804865] using wordTrace_append hprefix tailTrace_2804865
  have hstable : (prefixWord ++ tailWord_2804865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804865).length < 2 ^ (prefixWord ++ tailWord_2804865).sum := by decide
  have hdescent : baseEnd_2804865 < baseStart_2804865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804888 : List Nat := [2, 1, 2, 4, 2, 1, 3, 3, 5]
def baseStart_2804888 : Nat := 118140960795 + 2804888 * 2 ^ 59
def prefixEnd_2804888 : Nat := 4983230072969 + 3 ^ 40 * 2804888 * 2
def baseEnd_2804888 : Nat := 160028414003147455166729

theorem tailTrace_2804888 : CollatzResearch.WordTrace tailWord_2804888 prefixEnd_2804888 160028414003147455166729 := by
  unfold tailWord_2804888
  simp only [CollatzResearch.WordTrace]
  refine ⟨51151334931188643788723659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68201779908251525051631545 51151334931188643788723659)
  ·
    refine ⟨76727002396782965683085489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51151334931188643788723659 76727002396782965683085489)
    ·
      refine ⟨57545251797587224262314117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76727002396782965683085489 57545251797587224262314117)
      ·
        refine ⟨10789734712047604549183897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57545251797587224262314117 10789734712047604549183897)
        ·
          refine ⟨8092301034035703411887923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10789734712047604549183897 8092301034035703411887923)
          ·
            refine ⟨12138451551053555117831885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8092301034035703411887923 12138451551053555117831885)
            ·
              refine ⟨4551919331645083169186957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12138451551053555117831885 4551919331645083169186957)
              ·
                refine ⟨1706969749366906188445109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4551919331645083169186957 1706969749366906188445109)
                ·
                  refine ⟨160028414003147455166729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1706969749366906188445109 160028414003147455166729)
                  ·
                    rfl

theorem cell23_2804888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 5].length) (baseStart_2804888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804888 prefixEnd_2804888 := by exact prefixLift 2804888
  have htrace : WordTrace (prefixWord ++ tailWord_2804888) baseStart_2804888 baseEnd_2804888 := by
    simpa [prefixWord, tailWord_2804888, baseEnd_2804888] using wordTrace_append hprefix tailTrace_2804888
  have hstable : (prefixWord ++ tailWord_2804888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804888).length < 2 ^ (prefixWord ++ tailWord_2804888).sum := by decide
  have hdescent : baseEnd_2804888 < baseStart_2804888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804901 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 2, 5]
def baseStart_2804901 : Nat := 118140960795 + 2804901 * 2 ^ 59
def prefixEnd_2804901 : Nat := 4983230072969 + 3 ^ 40 * 2804901 * 2
def baseEnd_2804901 : Nat := 480087467092278515212667

theorem tailTrace_2804901 : CollatzResearch.WordTrace tailWord_2804901 prefixEnd_2804901 480087467092278515212667 := by
  unfold tailWord_2804901
  simp only [CollatzResearch.WordTrace]
  refine ⟨102303144011330190797670557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68202096007553460531780371 102303144011330190797670557)
  ·
    refine ⟨38363679004248821549126459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102303144011330190797670557 38363679004248821549126459)
    ·
      refine ⟨57545518506373232323689689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38363679004248821549126459 57545518506373232323689689)
      ·
        refine ⟨43159138879779924242767267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57545518506373232323689689 43159138879779924242767267)
        ·
          refine ⟨64738708319669886364150901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43159138879779924242767267 64738708319669886364150901)
          ·
            refine ⟨6069253904969051846639147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64738708319669886364150901 6069253904969051846639147)
            ·
              refine ⟨9103880857453577769958721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6069253904969051846639147 9103880857453577769958721)
              ·
                refine ⟨6827910643090183327469041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9103880857453577769958721 6827910643090183327469041)
                ·
                  refine ⟨5120932982317637495601781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6827910643090183327469041 5120932982317637495601781)
                  ·
                    refine ⟨480087467092278515212667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5120932982317637495601781 480087467092278515212667)
                    ·
                      rfl

theorem cell23_2804901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_2804901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804901 prefixEnd_2804901 := by exact prefixLift 2804901
  have htrace : WordTrace (prefixWord ++ tailWord_2804901) baseStart_2804901 baseEnd_2804901 := by
    simpa [prefixWord, tailWord_2804901, baseEnd_2804901] using wordTrace_append hprefix tailTrace_2804901
  have hstable : (prefixWord ++ tailWord_2804901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804901).length < 2 ^ (prefixWord ++ tailWord_2804901).sum := by decide
  have hdescent : baseEnd_2804901 < baseStart_2804901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804938 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 2, 1, 4]
def baseStart_2804938 : Nat := 118140960795 + 2804938 * 2 ^ 59
def prefixEnd_2804938 : Nat := 4983230072969 + 3 ^ 40 * 2804938 * 2
def baseEnd_2804938 : Nat := 1440281400061051900875331

theorem tailTrace_2804938 : CollatzResearch.WordTrace tailWord_2804938 prefixEnd_2804938 1440281400061051900875331 := by
  unfold tailWord_2804938
  simp only [CollatzResearch.WordTrace]
  refine ⟨25576123378049036529191867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68202995674797430744511645 25576123378049036529191867)
  ·
    refine ⟨38364185067073554793787801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25576123378049036529191867 38364185067073554793787801)
    ·
      refine ⟨28773138800305166095340851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38364185067073554793787801 28773138800305166095340851)
      ·
        refine ⟨43159708200457749143011277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28773138800305166095340851 43159708200457749143011277)
        ·
          refine ⟨16184890575171655928629229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43159708200457749143011277 16184890575171655928629229)
          ·
            refine ⟨6069333965689370973235961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16184890575171655928629229 6069333965689370973235961)
            ·
              refine ⟨4552000474267028229926971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6069333965689370973235961 4552000474267028229926971)
              ·
                refine ⟨6828000711400542344890457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4552000474267028229926971 6828000711400542344890457)
                ·
                  refine ⟨5121000533550406758667843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6828000711400542344890457 5121000533550406758667843)
                  ·
                    refine ⟨7681500800325610138001765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5121000533550406758667843 7681500800325610138001765)
                    ·
                      refine ⟨1440281400061051900875331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7681500800325610138001765 1440281400061051900875331)
                      ·
                        rfl

theorem cell23_2804938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_2804938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804938 prefixEnd_2804938 := by exact prefixLift 2804938
  have htrace : WordTrace (prefixWord ++ tailWord_2804938) baseStart_2804938 baseEnd_2804938 := by
    simpa [prefixWord, tailWord_2804938, baseEnd_2804938] using wordTrace_append hprefix tailTrace_2804938
  have hstable : (prefixWord ++ tailWord_2804938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804938).length < 2 ^ (prefixWord ++ tailWord_2804938).sum := by decide
  have hdescent : baseEnd_2804938 < baseStart_2804938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804961 : List Nat := [1, 2, 3, 1, 3, 2, 1, 4, 6]
def baseStart_2804961 : Nat := 118140960795 + 2804961 * 2 ^ 59
def prefixEnd_2804961 : Nat := 4983230072969 + 3 ^ 40 * 2804961 * 2
def baseEnd_2804961 : Nat := 160032578901789478987525

theorem tailTrace_2804961 : CollatzResearch.WordTrace tailWord_2804961 prefixEnd_2804961 160032578901789478987525 := by
  unfold tailWord_2804961
  simp only [CollatzResearch.WordTrace]
  refine ⟨102305332391112821044854737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68203554927408547363236491 102305332391112821044854737)
  ·
    refine ⟨76728999293334615783641053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102305332391112821044854737 76728999293334615783641053)
    ·
      refine ⟨28773374735000480918865395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76728999293334615783641053 28773374735000480918865395)
      ·
        refine ⟨43160062102500721378298093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28773374735000480918865395 43160062102500721378298093)
        ·
          refine ⟨16185023288437770516861785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43160062102500721378298093 16185023288437770516861785)
          ·
            refine ⟨12138767466328327887646339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16185023288437770516861785 12138767466328327887646339)
            ·
              refine ⟨18208151199492491831469509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12138767466328327887646339 18208151199492491831469509)
              ·
                refine ⟨3414028349904842218400533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18208151199492491831469509 3414028349904842218400533)
                ·
                  refine ⟨160032578901789478987525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3414028349904842218400533 160032578901789478987525)
                  ·
                    rfl

theorem cell23_2804961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 6].length) (baseStart_2804961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804961 prefixEnd_2804961 := by exact prefixLift 2804961
  have htrace : WordTrace (prefixWord ++ tailWord_2804961) baseStart_2804961 baseEnd_2804961 := by
    simpa [prefixWord, tailWord_2804961, baseEnd_2804961] using wordTrace_append hprefix tailTrace_2804961
  have hstable : (prefixWord ++ tailWord_2804961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804961).length < 2 ^ (prefixWord ++ tailWord_2804961).sum := by decide
  have hdescent : baseEnd_2804961 < baseStart_2804961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2804991 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 3, 5]
def baseStart_2804991 : Nat := 118140960795 + 2804991 * 2 ^ 59
def prefixEnd_2804991 : Nat := 4983230072969 + 3 ^ 40 * 2804991 * 2
def baseEnd_2804991 : Nat := 480102871511913397837529

theorem tailTrace_2804991 : CollatzResearch.WordTrace tailWord_2804991 prefixEnd_2804991 480102871511913397837529 := by
  unfold tailWord_2804991
  simp only [CollatzResearch.WordTrace]
  refine ⟨102306426581004136168446827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68204284387336090778964551 102306426581004136168446827)
  ·
    refine ⟨153459639871506204252670241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102306426581004136168446827 153459639871506204252670241)
    ·
      refine ⟨115094729903629653189502681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153459639871506204252670241 115094729903629653189502681)
      ·
        refine ⟨86321047427722239892127011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115094729903629653189502681 86321047427722239892127011)
        ·
          refine ⟨129481571141583359838190517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86321047427722239892127011 129481571141583359838190517)
          ·
            refine ⟨12138897294523439984830361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129481571141583359838190517 12138897294523439984830361)
            ·
              refine ⟨9104172970892579988622771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12138897294523439984830361 9104172970892579988622771)
              ·
                refine ⟨13656259456338869982934157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9104172970892579988622771 13656259456338869982934157)
                ·
                  refine ⟨5121097296127076243600309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13656259456338869982934157 5121097296127076243600309)
                  ·
                    refine ⟨480102871511913397837529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5121097296127076243600309 480102871511913397837529)
                    ·
                      rfl

theorem cell23_2804991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 5].length) (baseStart_2804991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2804991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2804991 prefixEnd_2804991 := by exact prefixLift 2804991
  have htrace : WordTrace (prefixWord ++ tailWord_2804991) baseStart_2804991 baseEnd_2804991 := by
    simpa [prefixWord, tailWord_2804991, baseEnd_2804991] using wordTrace_append hprefix tailTrace_2804991
  have hstable : (prefixWord ++ tailWord_2804991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2804991).length < 2 ^ (prefixWord ++ tailWord_2804991).sum := by decide
  have hdescent : baseEnd_2804991 < baseStart_2804991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2804991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805045 : List Nat := [1, 3, 3, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_2805045 : Nat := 118140960795 + 2805045 * 2 ^ 59
def prefixEnd_2805045 : Nat := 4983230072969 + 3 ^ 40 * 2805045 * 2
def baseEnd_2805045 : Nat := 1440336342491082982237339

theorem tailTrace_2805045 : CollatzResearch.WordTrace tailWord_2805045 prefixEnd_2805045 1440336342491082982237339 := by
  unfold tailWord_2805045
  simp only [CollatzResearch.WordTrace]
  refine ⟨102308396122808503390912589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68205597415205668927275059 102308396122808503390912589)
  ·
    refine ⟨38365648546053188771592221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102308396122808503390912589 38365648546053188771592221)
    ·
      refine ⟨14387118204769945789347083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38365648546053188771592221 14387118204769945789347083)
      ·
        refine ⟨21580677307154918684020625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14387118204769945789347083 21580677307154918684020625)
        ·
          refine ⟨16185507980366189013015469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21580677307154918684020625 16185507980366189013015469)
          ·
            refine ⟨6069565492637320879880801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16185507980366189013015469 6069565492637320879880801)
            ·
              refine ⟨4552174119477990659910601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6069565492637320879880801 4552174119477990659910601)
              ·
                refine ⟨3414130589608492994932951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4552174119477990659910601 3414130589608492994932951)
                ·
                  refine ⟨5121195884412739492399427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3414130589608492994932951 5121195884412739492399427)
                  ·
                    refine ⟨7681793826619109238599141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5121195884412739492399427 7681793826619109238599141)
                    ·
                      refine ⟨1440336342491082982237339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7681793826619109238599141 1440336342491082982237339)
                      ·
                        rfl

theorem cell23_2805045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_2805045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805045 prefixEnd_2805045 := by exact prefixLift 2805045
  have htrace : WordTrace (prefixWord ++ tailWord_2805045) baseStart_2805045 baseEnd_2805045 := by
    simpa [prefixWord, tailWord_2805045, baseEnd_2805045] using wordTrace_append hprefix tailTrace_2805045
  have hstable : (prefixWord ++ tailWord_2805045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805045).length < 2 ^ (prefixWord ++ tailWord_2805045).sum := by decide
  have hdescent : baseEnd_2805045 < baseStart_2805045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805152 : List Nat := [2, 1, 1, 4, 1, 2, 1, 5, 2, 2, 2]
def baseStart_2805152 : Nat := 118140960795 + 2805152 * 2 ^ 59
def prefixEnd_2805152 : Nat := 4983230072969 + 3 ^ 40 * 2805152 * 2
def baseEnd_2805152 : Nat := 1440391284921114063599347

theorem tailTrace_2805152 : CollatzResearch.WordTrace tailWord_2805152 prefixEnd_2805152 1440391284921114063599347 := by
  unfold tailWord_2805152
  simp only [CollatzResearch.WordTrace]
  refine ⟨51156149366710430332528855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68208199155613907110038473 51156149366710430332528855)
  ·
    refine ⟨76734224050065645498793283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51156149366710430332528855 76734224050065645498793283)
    ·
      refine ⟨115101336075098468248189925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76734224050065645498793283 115101336075098468248189925)
      ·
        refine ⟨21581500514080962796535611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115101336075098468248189925 21581500514080962796535611)
        ·
          refine ⟨32372250771121444194803417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21581500514080962796535611 32372250771121444194803417)
          ·
            refine ⟨24279188078341083146102563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32372250771121444194803417 24279188078341083146102563)
            ·
              refine ⟨36418782117511624719153845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24279188078341083146102563 36418782117511624719153845)
              ·
                refine ⟨3414260823516714817420673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36418782117511624719153845 3414260823516714817420673)
                ·
                  refine ⟨2560695617637536113065505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3414260823516714817420673 2560695617637536113065505)
                  ·
                    refine ⟨1920521713228152084799129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2560695617637536113065505 1920521713228152084799129)
                    ·
                      refine ⟨1440391284921114063599347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1920521713228152084799129 1440391284921114063599347)
                      ·
                        rfl

theorem cell23_2805152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_2805152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805152 prefixEnd_2805152 := by exact prefixLift 2805152
  have htrace : WordTrace (prefixWord ++ tailWord_2805152) baseStart_2805152 baseEnd_2805152 := by
    simpa [prefixWord, tailWord_2805152, baseEnd_2805152] using wordTrace_append hprefix tailTrace_2805152
  have hstable : (prefixWord ++ tailWord_2805152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805152).length < 2 ^ (prefixWord ++ tailWord_2805152).sum := by decide
  have hdescent : baseEnd_2805152 < baseStart_2805152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805175 : List Nat := [1, 1, 3, 1, 3, 2, 4, 3, 5]
def baseStart_2805175 : Nat := 118140960795 + 2805175 * 2 ^ 59
def prefixEnd_2805175 : Nat := 4983230072969 + 3 ^ 40 * 2805175 * 2
def baseEnd_2805175 : Nat := 160044788330685274845749

theorem tailTrace_2805175 : CollatzResearch.WordTrace tailWord_2805175 prefixEnd_2805175 160044788330685274845749 := by
  unfold tailWord_2805175
  simp only [CollatzResearch.WordTrace]
  refine ⟨102313137612337535593144979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68208758408225023728763319 102313137612337535593144979)
  ·
    refine ⟨153469706418506303389717469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102313137612337535593144979 153469706418506303389717469)
    ·
      refine ⟨57551139906939863771144051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153469706418506303389717469 57551139906939863771144051)
      ·
        refine ⟨86326709860409795656716077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57551139906939863771144051 86326709860409795656716077)
        ·
          refine ⟨32372516197653673371268529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86326709860409795656716077 32372516197653673371268529)
          ·
            refine ⟨24279387148240255028451397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32372516197653673371268529 24279387148240255028451397)
            ·
              refine ⟨4552385090295047817834637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24279387148240255028451397 4552385090295047817834637)
              ·
                refine ⟨1707144408860642931687989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4552385090295047817834637 1707144408860642931687989)
                ·
                  refine ⟨160044788330685274845749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1707144408860642931687989 160044788330685274845749)
                  ·
                    rfl

theorem cell23_2805175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 5].length) (baseStart_2805175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805175 prefixEnd_2805175 := by exact prefixLift 2805175
  have htrace : WordTrace (prefixWord ++ tailWord_2805175) baseStart_2805175 baseEnd_2805175 := by
    simpa [prefixWord, tailWord_2805175, baseEnd_2805175] using wordTrace_append hprefix tailTrace_2805175
  have hstable : (prefixWord ++ tailWord_2805175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805175).length < 2 ^ (prefixWord ++ tailWord_2805175).sum := by decide
  have hdescent : baseEnd_2805175 < baseStart_2805175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805198 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_2805198 : Nat := 118140960795 + 2805198 * 2 ^ 59
def prefixEnd_2805198 : Nat := 4983230072969 + 3 ^ 40 * 2805198 * 2
def baseEnd_2805198 : Nat := 1440414905031220883624135

theorem tailTrace_2805198 : CollatzResearch.WordTrace tailWord_2805198 prefixEnd_2805198 1440414905031220883624135 := by
  unfold tailWord_2805198
  simp only [CollatzResearch.WordTrace]
  refine ⟨12789247061406776315154031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68209317660836140347488165 12789247061406776315154031)
  ·
    refine ⟨19183870592110164472731047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12789247061406776315154031 19183870592110164472731047)
    ·
      refine ⟨28775805888165246709096571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19183870592110164472731047 28775805888165246709096571)
      ·
        refine ⟨43163708832247870063644857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28775805888165246709096571 43163708832247870063644857)
        ·
          refine ⟨32372781624185902547733643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43163708832247870063644857 32372781624185902547733643)
          ·
            refine ⟨48559172436278853821600465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32372781624185902547733643 48559172436278853821600465)
            ·
              refine ⟨36419379327209140366200349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48559172436278853821600465 36419379327209140366200349)
              ·
                refine ⟨13657267247703427637325131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36419379327209140366200349 13657267247703427637325131)
                ·
                  refine ⟨20485900871555141455987697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13657267247703427637325131 20485900871555141455987697)
                  ·
                    refine ⟨15364425653666356091990773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20485900871555141455987697 15364425653666356091990773)
                    ·
                      refine ⟨1440414905031220883624135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15364425653666356091990773 1440414905031220883624135)
                      ·
                        rfl

theorem cell23_2805198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_2805198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805198 prefixEnd_2805198 := by exact prefixLift 2805198
  have htrace : WordTrace (prefixWord ++ tailWord_2805198) baseStart_2805198 baseEnd_2805198 := by
    simpa [prefixWord, tailWord_2805198, baseEnd_2805198] using wordTrace_append hprefix tailTrace_2805198
  have hstable : (prefixWord ++ tailWord_2805198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805198).length < 2 ^ (prefixWord ++ tailWord_2805198).sum := by decide
  have hdescent : baseEnd_2805198 < baseStart_2805198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805208 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 1, 3, 4]
def baseStart_2805208 : Nat := 118140960795 + 2805208 * 2 ^ 59
def prefixEnd_2805208 : Nat := 4983230072969 + 3 ^ 40 * 2805208 * 2
def baseEnd_2805208 : Nat := 1440420039837765844499089

theorem tailTrace_2805208 : CollatzResearch.WordTrace tailWord_2805208 prefixEnd_2805208 1440420039837765844499089 := by
  unfold tailWord_2805208
  simp only [CollatzResearch.WordTrace]
  refine ⟨51157170610608991114548139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68209560814145321486064185 51157170610608991114548139)
  ·
    refine ⟨76735755915913486671822209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51157170610608991114548139 76735755915913486671822209)
    ·
      refine ⟨57551816936935115003866657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76735755915913486671822209 57551816936935115003866657)
      ·
        refine ⟨43163862702701336252899993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57551816936935115003866657 43163862702701336252899993)
        ·
          refine ⟨32372897027026002189674995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43163862702701336252899993 32372897027026002189674995)
          ·
            refine ⟨48559345540539003284512493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32372897027026002189674995 48559345540539003284512493)
            ·
              refine ⟨18209754577702126231692185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48559345540539003284512493 18209754577702126231692185)
              ·
                refine ⟨13657315933276594673769139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18209754577702126231692185 13657315933276594673769139)
                ·
                  refine ⟨20485973899914892010653709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13657315933276594673769139 20485973899914892010653709)
                  ·
                    refine ⟨7682240212468084503995141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20485973899914892010653709 7682240212468084503995141)
                    ·
                      refine ⟨1440420039837765844499089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7682240212468084503995141 1440420039837765844499089)
                      ·
                        rfl

theorem cell23_2805208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_2805208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805208 prefixEnd_2805208 := by exact prefixLift 2805208
  have htrace : WordTrace (prefixWord ++ tailWord_2805208) baseStart_2805208 baseEnd_2805208 := by
    simpa [prefixWord, tailWord_2805208, baseEnd_2805208] using wordTrace_append hprefix tailTrace_2805208
  have hstable : (prefixWord ++ tailWord_2805208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805208).length < 2 ^ (prefixWord ++ tailWord_2805208).sum := by decide
  have hdescent : baseEnd_2805208 < baseStart_2805208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805245 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 4, 2, 3]
def baseStart_2805245 : Nat := 118140960795 + 2805245 * 2 ^ 59
def prefixEnd_2805245 : Nat := 4983230072969 + 3 ^ 40 * 2805245 * 2
def baseEnd_2805245 : Nat := 1440439038621982199736419

theorem tailTrace_2805245 : CollatzResearch.WordTrace tailWord_2805245 prefixEnd_2805245 1440439038621982199736419 := by
  unfold tailWord_2805245
  simp only [CollatzResearch.WordTrace]
  refine ⟨102315690722083937548193189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68210460481389291698795459 102315690722083937548193189)
  ·
    refine ⟨19184192010390738290286223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102315690722083937548193189 19184192010390738290286223)
    ·
      refine ⟨28776288015586107435429335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19184192010390738290286223 28776288015586107435429335)
      ·
        refine ⟨43164432023379161153144003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28776288015586107435429335 43164432023379161153144003)
        ·
          refine ⟨64746648035068741729716005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43164432023379161153144003 64746648035068741729716005)
          ·
            refine ⟨12139996506575389074321751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64746648035068741729716005 12139996506575389074321751)
            ·
              refine ⟨18209994759863083611482627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12139996506575389074321751 18209994759863083611482627)
              ·
                refine ⟨27314992139794625417223941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18209994759863083611482627 27314992139794625417223941)
                ·
                  refine ⟨5121561026211492265729489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27314992139794625417223941 5121561026211492265729489)
                  ·
                    refine ⟨3841170769658619199297117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5121561026211492265729489 3841170769658619199297117)
                    ·
                      refine ⟨1440439038621982199736419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3841170769658619199297117 1440439038621982199736419)
                      ·
                        rfl

theorem cell23_2805245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_2805245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805245 prefixEnd_2805245 := by exact prefixLift 2805245
  have htrace : WordTrace (prefixWord ++ tailWord_2805245) baseStart_2805245 baseEnd_2805245 := by
    simpa [prefixWord, tailWord_2805245, baseEnd_2805245] using wordTrace_append hprefix tailTrace_2805245
  have hstable : (prefixWord ++ tailWord_2805245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805245).length < 2 ^ (prefixWord ++ tailWord_2805245).sum := by decide
  have hdescent : baseEnd_2805245 < baseStart_2805245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805254 : List Nat := [6, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_2805254 : Nat := 118140960795 + 2805254 * 2 ^ 59
def prefixEnd_2805254 : Nat := 4983230072969 + 3 ^ 40 * 2805254 * 2
def baseEnd_2805254 : Nat := 1440443659947872664523879

theorem tailTrace_2805254 : CollatzResearch.WordTrace tailWord_2805254 prefixEnd_2805254 1440443659947872664523879 := by
  unfold tailWord_2805254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3197375593095354127664713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68210679319367554723513877 3197375593095354127664713)
  ·
    refine ⟨2398031694821515595748535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3197375593095354127664713 2398031694821515595748535)
    ·
      refine ⟨3597047542232273393622803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2398031694821515595748535 3597047542232273393622803)
      ·
        refine ⟨5395571313348410090434205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3597047542232273393622803 5395571313348410090434205)
        ·
          refine ⟨2023339242505653783912827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5395571313348410090434205 2023339242505653783912827)
          ·
            refine ⟨3035008863758480675869241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2023339242505653783912827 3035008863758480675869241)
            ·
              refine ⟨2276256647818860506901931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3035008863758480675869241 2276256647818860506901931)
              ·
                refine ⟨3414384971728290760352897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2276256647818860506901931 3414384971728290760352897)
                ·
                  refine ⟨2560788728796218070264673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3414384971728290760352897 2560788728796218070264673)
                  ·
                    refine ⟨1920591546597163552698505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2560788728796218070264673 1920591546597163552698505)
                    ·
                      refine ⟨1440443659947872664523879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1920591546597163552698505 1440443659947872664523879)
                      ·
                        rfl

theorem cell23_2805254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_2805254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805254 prefixEnd_2805254 := by exact prefixLift 2805254
  have htrace : WordTrace (prefixWord ++ tailWord_2805254) baseStart_2805254 baseEnd_2805254 := by
    simpa [prefixWord, tailWord_2805254, baseEnd_2805254] using wordTrace_append hprefix tailTrace_2805254
  have hstable : (prefixWord ++ tailWord_2805254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805254).length < 2 ^ (prefixWord ++ tailWord_2805254).sum := by decide
  have hdescent : baseEnd_2805254 < baseStart_2805254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805315 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 4, 6, 2]
def baseStart_2805315 : Nat := 118140960795 + 2805315 * 2 ^ 59
def prefixEnd_2805315 : Nat := 4983230072969 + 3 ^ 40 * 2805315 * 2
def baseEnd_2805315 : Nat := 1440474982267796925861097

theorem tailTrace_2805315 : CollatzResearch.WordTrace tailWord_2805315 prefixEnd_2805315 1440474982267796925861097 := by
  unfold tailWord_2805315
  simp only [CollatzResearch.WordTrace]
  refine ⟨102318243831830339503241399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68212162554553559668827599 102318243831830339503241399)
  ·
    refine ⟨153477365747745509254862099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102318243831830339503241399 153477365747745509254862099)
    ·
      refine ⟨230216048621618263882293149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153477365747745509254862099 230216048621618263882293149)
      ·
        refine ⟨86331018233106848955859931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230216048621618263882293149 86331018233106848955859931)
        ·
          refine ⟨129496527349660273433789897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86331018233106848955859931 129496527349660273433789897)
          ·
            refine ⟨97122395512245205075342423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129496527349660273433789897 97122395512245205075342423)
            ·
              refine ⟨145683593268367807613013635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97122395512245205075342423 145683593268367807613013635)
              ·
                refine ⟨218525389902551711419520453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145683593268367807613013635 218525389902551711419520453)
                ·
                  refine ⟨40973510606728445891160085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 218525389902551711419520453 40973510606728445891160085)
                  ·
                    refine ⟨1920633309690395901148129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40973510606728445891160085 1920633309690395901148129)
                    ·
                      refine ⟨1440474982267796925861097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1920633309690395901148129 1440474982267796925861097)
                      ·
                        rfl

theorem cell23_2805315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 6, 2].length) (baseStart_2805315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805315 prefixEnd_2805315 := by exact prefixLift 2805315
  have htrace : WordTrace (prefixWord ++ tailWord_2805315) baseStart_2805315 baseEnd_2805315 := by
    simpa [prefixWord, tailWord_2805315, baseEnd_2805315] using wordTrace_append hprefix tailTrace_2805315
  have hstable : (prefixWord ++ tailWord_2805315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805315).length < 2 ^ (prefixWord ++ tailWord_2805315).sum := by decide
  have hdescent : baseEnd_2805315 < baseStart_2805315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805332 : List Nat := [2, 4, 1, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_2805332 : Nat := 118140960795 + 2805332 * 2 ^ 59
def prefixEnd_2805332 : Nat := 4983230072969 + 3 ^ 40 * 2805332 * 2
def baseEnd_2805332 : Nat := 1440483711438923359348519

theorem tailTrace_2805332 : CollatzResearch.WordTrace tailWord_2805332 prefixEnd_2805332 1440483711438923359348519 := by
  unfold tailWord_2805332
  simp only [CollatzResearch.WordTrace]
  refine ⟨51159431936384375703305125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68212575915179167604406833 51159431936384375703305125)
  ·
    refine ⟨9592393488072070444369711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51159431936384375703305125 9592393488072070444369711)
    ·
      refine ⟨14388590232108105666554567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9592393488072070444369711 14388590232108105666554567)
      ·
        refine ⟨21582885348162158499831851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14388590232108105666554567 21582885348162158499831851)
        ·
          refine ⟨32374328022243237749747777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21582885348162158499831851 32374328022243237749747777)
          ·
            refine ⟨24280746016682428312310833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32374328022243237749747777 24280746016682428312310833)
            ·
              refine ⟨18210559512511821234233125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24280746016682428312310833 18210559512511821234233125)
              ·
                refine ⟨3414479908595966481418711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18210559512511821234233125 3414479908595966481418711)
                ·
                  refine ⟨5121719862893949722128067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3414479908595966481418711 5121719862893949722128067)
                  ·
                    refine ⟨7682579794340924583192101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5121719862893949722128067 7682579794340924583192101)
                    ·
                      refine ⟨1440483711438923359348519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7682579794340924583192101 1440483711438923359348519)
                      ·
                        rfl

theorem cell23_2805332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_2805332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805332 prefixEnd_2805332 := by exact prefixLift 2805332
  have htrace : WordTrace (prefixWord ++ tailWord_2805332) baseStart_2805332 baseEnd_2805332 := by
    simpa [prefixWord, tailWord_2805332, baseEnd_2805332] using wordTrace_append hprefix tailTrace_2805332
  have hstable : (prefixWord ++ tailWord_2805332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805332).length < 2 ^ (prefixWord ++ tailWord_2805332).sum := by decide
  have hdescent : baseEnd_2805332 < baseStart_2805332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805338 : List Nat := [3, 1, 1, 2, 1, 1, 1, 13]
def baseStart_2805338 : Nat := 118140960795 + 2805338 * 2 ^ 59
def prefixEnd_2805338 : Nat := 4983230072969 + 3 ^ 40 * 2805338 * 2
def baseEnd_2805338 : Nat := 53351362678624086513833

theorem tailTrace_2805338 : CollatzResearch.WordTrace tailWord_2805338 prefixEnd_2805338 53351362678624086513833 := by
  unfold tailWord_2805338
  simp only [CollatzResearch.WordTrace]
  refine ⟨25579770677686753607832167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68212721807164676287552445 25579770677686753607832167)
  ·
    refine ⟨38369656016530130411748251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25579770677686753607832167 38369656016530130411748251)
    ·
      refine ⟨57554484024795195617622377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38369656016530130411748251 57554484024795195617622377)
      ·
        refine ⟨43165863018596396713216783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57554484024795195617622377 43165863018596396713216783)
        ·
          refine ⟨64748794527894595069825175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43165863018596396713216783 64748794527894595069825175)
          ·
            refine ⟨97123191791841892604737763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64748794527894595069825175 97123191791841892604737763)
            ·
              refine ⟨145684787687762838907106645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97123191791841892604737763 145684787687762838907106645)
              ·
                refine ⟨53351362678624086513833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 145684787687762838907106645 53351362678624086513833)
                ·
                  rfl

theorem cell23_2805338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 13].length) (baseStart_2805338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805338 prefixEnd_2805338 := by exact prefixLift 2805338
  have htrace : WordTrace (prefixWord ++ tailWord_2805338) baseStart_2805338 baseEnd_2805338 := by
    simpa [prefixWord, tailWord_2805338, baseEnd_2805338] using wordTrace_append hprefix tailTrace_2805338
  have hstable : (prefixWord ++ tailWord_2805338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805338).length < 2 ^ (prefixWord ++ tailWord_2805338).sum := by decide
  have hdescent : baseEnd_2805338 < baseStart_2805338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805345 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_2805345 : Nat := 118140960795 + 2805345 * 2 ^ 59
def prefixEnd_2805345 : Nat := 4983230072969 + 3 ^ 40 * 2805345 * 2
def baseEnd_2805345 : Nat := 1440490386687431808485959

theorem tailTrace_2805345 : CollatzResearch.WordTrace tailWord_2805345 prefixEnd_2805345 1440490386687431808485959 := by
  unfold tailWord_2805345
  simp only [CollatzResearch.WordTrace]
  refine ⟨102319338021721654626833489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68212892014481103084555659 102319338021721654626833489)
  ·
    refine ⟨76739503516291240970125117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102319338021721654626833489 76739503516291240970125117)
    ·
      refine ⟨28777313818609215363796919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76739503516291240970125117 28777313818609215363796919)
      ·
        refine ⟨43165970727913823045695379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28777313818609215363796919 43165970727913823045695379)
        ·
          refine ⟨64748956091870734568543069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43165970727913823045695379 64748956091870734568543069)
          ·
            refine ⟨24280858534451525463203651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64748956091870734568543069 24280858534451525463203651)
            ·
              refine ⟨36421287801677288194805477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24280858534451525463203651 36421287801677288194805477)
              ·
                refine ⟨6828991462814491536526027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36421287801677288194805477 6828991462814491536526027)
                ·
                  refine ⟨10243487194221737304789041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6828991462814491536526027 10243487194221737304789041)
                  ·
                    refine ⟨7682615395666302978591781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10243487194221737304789041 7682615395666302978591781)
                    ·
                      refine ⟨1440490386687431808485959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7682615395666302978591781 1440490386687431808485959)
                      ·
                        rfl

theorem cell23_2805345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_2805345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805345 prefixEnd_2805345 := by exact prefixLift 2805345
  have htrace : WordTrace (prefixWord ++ tailWord_2805345) baseStart_2805345 baseEnd_2805345 := by
    simpa [prefixWord, tailWord_2805345, baseEnd_2805345] using wordTrace_append hprefix tailTrace_2805345
  have hstable : (prefixWord ++ tailWord_2805345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805345).length < 2 ^ (prefixWord ++ tailWord_2805345).sum := by decide
  have hdescent : baseEnd_2805345 < baseStart_2805345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805349 : List Nat := [1, 3, 1, 3, 3, 1, 4, 1, 1, 1, 4]
def baseStart_2805349 : Nat := 118140960795 + 2805349 * 2 ^ 59
def prefixEnd_2805349 : Nat := 4983230072969 + 3 ^ 40 * 2805349 * 2
def baseEnd_2805349 : Nat := 1440492440610049792835941

theorem tailTrace_2805349 : CollatzResearch.WordTrace tailWord_2805349 prefixEnd_2805349 1440492440610049792835941 := by
  unfold tailWord_2805349
  simp only [CollatzResearch.WordTrace]
  refine ⟨102319483913707163309979101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68212989275804775539986067 102319483913707163309979101)
  ·
    refine ⟨38369806467640186241242163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102319483913707163309979101 38369806467640186241242163)
    ·
      refine ⟨57554709701460279361863245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38369806467640186241242163 57554709701460279361863245)
      ·
        refine ⟨21583016138047604760698717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57554709701460279361863245 21583016138047604760698717)
        ·
          refine ⟨8093631051767851785262019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21583016138047604760698717 8093631051767851785262019)
          ·
            refine ⟨12140446577651777677893029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8093631051767851785262019 12140446577651777677893029)
            ·
              refine ⟨2276333733309708314604943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12140446577651777677893029 2276333733309708314604943)
              ·
                refine ⟨3414500599964562471907415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2276333733309708314604943 3414500599964562471907415)
                ·
                  refine ⟨5121750899946843707861123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3414500599964562471907415 5121750899946843707861123)
                  ·
                    refine ⟨7682626349920265561791685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5121750899946843707861123 7682626349920265561791685)
                    ·
                      refine ⟨1440492440610049792835941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7682626349920265561791685 1440492440610049792835941)
                      ·
                        rfl

theorem cell23_2805349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_2805349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805349 prefixEnd_2805349 := by exact prefixLift 2805349
  have htrace : WordTrace (prefixWord ++ tailWord_2805349) baseStart_2805349 baseEnd_2805349 := by
    simpa [prefixWord, tailWord_2805349, baseEnd_2805349] using wordTrace_append hprefix tailTrace_2805349
  have hstable : (prefixWord ++ tailWord_2805349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805349).length < 2 ^ (prefixWord ++ tailWord_2805349).sum := by decide
  have hdescent : baseEnd_2805349 < baseStart_2805349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805366 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2]
def baseStart_2805366 : Nat := 118140960795 + 2805366 * 2 ^ 59
def prefixEnd_2805366 : Nat := 4983230072969 + 3 ^ 40 * 2805366 * 2
def baseEnd_2805366 : Nat := 1440501169781176226323363

theorem tailTrace_2805366 : CollatzResearch.WordTrace tailWord_2805366 prefixEnd_2805366 1440501169781176226323363 := by
  unfold tailWord_2805366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6395006497165348450834247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68213402636430383475565301 6395006497165348450834247)
  ·
    refine ⟨9592509745748022676251371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6395006497165348450834247 9592509745748022676251371)
    ·
      refine ⟨14388764618622034014377057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9592509745748022676251371 14388764618622034014377057)
      ·
        refine ⟨10791573463966525510782793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14388764618622034014377057 10791573463966525510782793)
        ·
          refine ⟨8093680097974894133087095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10791573463966525510782793 8093680097974894133087095)
          ·
            refine ⟨12140520146962341199630643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8093680097974894133087095 12140520146962341199630643)
            ·
              refine ⟨18210780220443511799445965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12140520146962341199630643 18210780220443511799445965)
              ·
                refine ⟨6829042582666316924792237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18210780220443511799445965 6829042582666316924792237)
                ·
                  refine ⟨2560890968499868846797089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6829042582666316924792237 2560890968499868846797089)
                  ·
                    refine ⟨1920668226374901635097817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2560890968499868846797089 1920668226374901635097817)
                    ·
                      refine ⟨1440501169781176226323363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1920668226374901635097817 1440501169781176226323363)
                      ·
                        rfl

theorem cell23_2805366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_2805366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805366 prefixEnd_2805366 := by exact prefixLift 2805366
  have htrace : WordTrace (prefixWord ++ tailWord_2805366) baseStart_2805366 baseEnd_2805366 := by
    simpa [prefixWord, tailWord_2805366, baseEnd_2805366] using wordTrace_append hprefix tailTrace_2805366
  have hstable : (prefixWord ++ tailWord_2805366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805366).length < 2 ^ (prefixWord ++ tailWord_2805366).sum := by decide
  have hdescent : baseEnd_2805366 < baseStart_2805366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805392 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 3, 3, 2]
def baseStart_2805392 : Nat := 118140960795 + 2805392 * 2 ^ 59
def prefixEnd_2805392 : Nat := 4983230072969 + 3 ^ 40 * 2805392 * 2
def baseEnd_2805392 : Nat := 1440514520278193124598243

theorem tailTrace_2805392 : CollatzResearch.WordTrace tailWord_2805392 prefixEnd_2805392 1440514520278193124598243 := by
  unfold tailWord_2805392
  simp only [CollatzResearch.WordTrace]
  refine ⟨51160526126275690826897215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68214034835034254435862953 51160526126275690826897215)
  ·
    refine ⟨76740789189413536240345823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51160526126275690826897215 76740789189413536240345823)
    ·
      refine ⟨115111183784120304360518735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76740789189413536240345823 115111183784120304360518735)
      ·
        refine ⟨172666775676180456540778103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115111183784120304360518735 172666775676180456540778103)
        ·
          refine ⟨259000163514270684811167155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172666775676180456540778103 259000163514270684811167155)
          ·
            refine ⟨388500245271406027216750733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259000163514270684811167155 388500245271406027216750733)
            ·
              refine ⟨145687591976777260206281525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 388500245271406027216750733 145687591976777260206281525)
              ·
                refine ⟨13658211747822868144338893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145687591976777260206281525 13658211747822868144338893)
                ·
                  refine ⟨5121829405433575554127085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13658211747822868144338893 5121829405433575554127085)
                  ·
                    refine ⟨1920686027037590832797657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5121829405433575554127085 1920686027037590832797657)
                    ·
                      refine ⟨1440514520278193124598243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1920686027037590832797657 1440514520278193124598243)
                      ·
                        rfl

theorem cell23_2805392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 3, 3, 2].length) (baseStart_2805392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805392 prefixEnd_2805392 := by exact prefixLift 2805392
  have htrace : WordTrace (prefixWord ++ tailWord_2805392) baseStart_2805392 baseEnd_2805392 := by
    simpa [prefixWord, tailWord_2805392, baseEnd_2805392] using wordTrace_append hprefix tailTrace_2805392
  have hstable : (prefixWord ++ tailWord_2805392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805392).length < 2 ^ (prefixWord ++ tailWord_2805392).sum := by decide
  have hdescent : baseEnd_2805392 < baseStart_2805392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805405 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_2805405 : Nat := 118140960795 + 2805405 * 2 ^ 59
def prefixEnd_2805405 : Nat := 4983230072969 + 3 ^ 40 * 2805405 * 2
def baseEnd_2805405 : Nat := 1440521195526701573735683

theorem tailTrace_2805405 : CollatzResearch.WordTrace tailWord_2805405 prefixEnd_2805405 1440521195526701573735683 := by
  unfold tailWord_2805405
  simp only [CollatzResearch.WordTrace]
  refine ⟨102321526401504284874017669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68214350934336189916011779 102321526401504284874017669)
  ·
    refine ⟨19185286200282053413878313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102321526401504284874017669 19185286200282053413878313)
    ·
      refine ⟨14388964650211540060408735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19185286200282053413878313 14388964650211540060408735)
      ·
        refine ⟨21583446975317310090613103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14388964650211540060408735 21583446975317310090613103)
        ·
          refine ⟨32375170462975965135919655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21583446975317310090613103 32375170462975965135919655)
          ·
            refine ⟨48562755694463947703879483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32375170462975965135919655 48562755694463947703879483)
            ·
              refine ⟨72844133541695921555819225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48562755694463947703879483 72844133541695921555819225)
              ·
                refine ⟨54633100156271941166864419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72844133541695921555819225 54633100156271941166864419)
                ·
                  refine ⟨81949650234407911750296629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54633100156271941166864419 81949650234407911750296629)
                  ·
                    refine ⟨7682779709475741726590309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81949650234407911750296629 7682779709475741726590309)
                    ·
                      refine ⟨1440521195526701573735683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7682779709475741726590309 1440521195526701573735683)
                      ·
                        rfl

theorem cell23_2805405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_2805405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805405 prefixEnd_2805405 := by exact prefixLift 2805405
  have htrace : WordTrace (prefixWord ++ tailWord_2805405) baseStart_2805405 baseEnd_2805405 := by
    simpa [prefixWord, tailWord_2805405, baseEnd_2805405] using wordTrace_append hprefix tailTrace_2805405
  have hstable : (prefixWord ++ tailWord_2805405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805405).length < 2 ^ (prefixWord ++ tailWord_2805405).sum := by decide
  have hdescent : baseEnd_2805405 < baseStart_2805405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805435 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 4]
def baseStart_2805435 : Nat := 118140960795 + 2805435 * 2 ^ 59
def prefixEnd_2805435 : Nat := 4983230072969 + 3 ^ 40 * 2805435 * 2
def baseEnd_2805435 : Nat := 1440536599946336456360545

theorem tailTrace_2805435 : CollatzResearch.WordTrace tailWord_2805435 prefixEnd_2805435 1440536599946336456360545 := by
  unfold tailWord_2805435
  simp only [CollatzResearch.WordTrace]
  refine ⟨102322620591395599997609759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68215080394263733331739839 102322620591395599997609759)
  ·
    refine ⟨153483930887093399996414639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102322620591395599997609759 153483930887093399996414639)
    ·
      refine ⟨230225896330640099994621959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153483930887093399996414639 230225896330640099994621959)
      ·
        refine ⟨345338844495960149991932939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230225896330640099994621959 345338844495960149991932939)
        ·
          refine ⟨518008266743940224987899409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345338844495960149991932939 518008266743940224987899409)
          ·
            refine ⟨388506200057955168740924557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 518008266743940224987899409 388506200057955168740924557)
            ·
              refine ⟨145689825021733188277846709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 388506200057955168740924557 145689825021733188277846709)
              ·
                refine ⟨13658421095787486401048129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145689825021733188277846709 13658421095787486401048129)
                ·
                  refine ⟨10243815821840614800786097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13658421095787486401048129 10243815821840614800786097)
                  ·
                    refine ⟨7682861866380461100589573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10243815821840614800786097 7682861866380461100589573)
                    ·
                      refine ⟨1440536599946336456360545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7682861866380461100589573 1440536599946336456360545)
                      ·
                        rfl

theorem cell23_2805435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 4].length) (baseStart_2805435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805435 prefixEnd_2805435 := by exact prefixLift 2805435
  have htrace : WordTrace (prefixWord ++ tailWord_2805435) baseStart_2805435 baseEnd_2805435 := by
    simpa [prefixWord, tailWord_2805435, baseEnd_2805435] using wordTrace_append hprefix tailTrace_2805435
  have hstable : (prefixWord ++ tailWord_2805435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805435).length < 2 ^ (prefixWord ++ tailWord_2805435).sum := by decide
  have hdescent : baseEnd_2805435 < baseStart_2805435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805473 : List Nat := [1, 2, 3, 1, 5, 1, 2, 2, 2, 2, 2]
def baseStart_2805473 : Nat := 118140960795 + 2805473 * 2 ^ 59
def prefixEnd_2805473 : Nat := 4983230072969 + 3 ^ 40 * 2805473 * 2
def baseEnd_2805473 : Nat := 1440556112211207307685371

theorem tailTrace_2805473 : CollatzResearch.WordTrace tailWord_2805473 prefixEnd_2805473 1440556112211207307685371 := by
  unfold tailWord_2805473
  simp only [CollatzResearch.WordTrace]
  refine ⟨102324006565257932487493073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68216004376838621658328715 102324006565257932487493073)
  ·
    refine ⟨76743004923943449365619805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102324006565257932487493073 76743004923943449365619805)
    ·
      refine ⟨28778626846478793512107427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76743004923943449365619805 28778626846478793512107427)
      ·
        refine ⟨43167940269718190268161141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28778626846478793512107427 43167940269718190268161141)
        ·
          refine ⟨4046994400286080337640107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43167940269718190268161141 4046994400286080337640107)
          ·
            refine ⟨6070491600429120506460161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4046994400286080337640107 6070491600429120506460161)
            ·
              refine ⟨4552868700321840379845121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6070491600429120506460161 4552868700321840379845121)
              ·
                refine ⟨3414651525241380284883841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4552868700321840379845121 3414651525241380284883841)
                ·
                  refine ⟨2560988643931035213662881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3414651525241380284883841 2560988643931035213662881)
                  ·
                    refine ⟨1920741482948276410247161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2560988643931035213662881 1920741482948276410247161)
                    ·
                      refine ⟨1440556112211207307685371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1920741482948276410247161 1440556112211207307685371)
                      ·
                        rfl

theorem cell23_2805473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_2805473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805473 prefixEnd_2805473 := by exact prefixLift 2805473
  have htrace : WordTrace (prefixWord ++ tailWord_2805473) baseStart_2805473 baseEnd_2805473 := by
    simpa [prefixWord, tailWord_2805473, baseEnd_2805473] using wordTrace_append hprefix tailTrace_2805473
  have hstable : (prefixWord ++ tailWord_2805473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805473).length < 2 ^ (prefixWord ++ tailWord_2805473).sum := by decide
  have hdescent : baseEnd_2805473 < baseStart_2805473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805512 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_2805512 : Nat := 118140960795 + 2805512 * 2 ^ 59
def prefixEnd_2805512 : Nat := 4983230072969 + 3 ^ 40 * 2805512 * 2
def baseEnd_2805512 : Nat := 1440576137956732655097691

theorem tailTrace_2805512 : CollatzResearch.WordTrace tailWord_2805512 prefixEnd_2805512 1440576137956732655097691 := by
  unfold tailWord_2805512
  simp only [CollatzResearch.WordTrace]
  refine ⟨51162714506058321074081395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68216952674744428098775193 51162714506058321074081395)
  ·
    refine ⟨76744071759087481611122093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51162714506058321074081395 76744071759087481611122093)
    ·
      refine ⟨28779026909657805604170785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76744071759087481611122093 28779026909657805604170785)
      ·
        refine ⟨21584270182243354203128089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28779026909657805604170785 21584270182243354203128089)
        ·
          refine ⟨16188202636682515652346067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21584270182243354203128089 16188202636682515652346067)
          ·
            refine ⟨24282303955023773478519101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16188202636682515652346067 24282303955023773478519101)
            ·
              refine ⟨9105863983133915054444663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24282303955023773478519101 9105863983133915054444663)
              ·
                refine ⟨13658795974700872581666995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9105863983133915054444663 13658795974700872581666995)
                ·
                  refine ⟨20488193962051308872500493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13658795974700872581666995 20488193962051308872500493)
                  ·
                    refine ⟨7683072735769240827187685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20488193962051308872500493 7683072735769240827187685)
                    ·
                      refine ⟨1440576137956732655097691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7683072735769240827187685 1440576137956732655097691)
                      ·
                        rfl

theorem cell23_2805512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_2805512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805512 prefixEnd_2805512 := by exact prefixLift 2805512
  have htrace : WordTrace (prefixWord ++ tailWord_2805512) baseStart_2805512 baseEnd_2805512 := by
    simpa [prefixWord, tailWord_2805512, baseEnd_2805512] using wordTrace_append hprefix tailTrace_2805512
  have hstable : (prefixWord ++ tailWord_2805512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805512).length < 2 ^ (prefixWord ++ tailWord_2805512).sum := by decide
  have hdescent : baseEnd_2805512 < baseStart_2805512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805524 : List Nat := [2, 4, 4, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_2805524 : Nat := 118140960795 + 2805524 * 2 ^ 59
def prefixEnd_2805524 : Nat := 4983230072969 + 3 ^ 40 * 2805524 * 2
def baseEnd_2805524 : Nat := 1440582299724586608147637

theorem tailTrace_2805524 : CollatzResearch.WordTrace tailWord_2805524 prefixEnd_2805524 1440582299724586608147637 := by
  unfold tailWord_2805524
  simp only [CollatzResearch.WordTrace]
  refine ⟨51162933344036584098799813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68217244458715445465066417 51162933344036584098799813)
  ·
    refine ⟨9593050002006859518524965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51162933344036584098799813 9593050002006859518524965)
    ·
      refine ⟨1798696875376286159723431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9593050002006859518524965 1798696875376286159723431)
      ·
        refine ⟨2698045313064429239585147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1798696875376286159723431 2698045313064429239585147)
        ·
          refine ⟨4047067969596643859377721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2698045313064429239585147 4047067969596643859377721)
          ·
            refine ⟨3035300977197482894533291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4047067969596643859377721 3035300977197482894533291)
            ·
              refine ⟨4552951465796224341799937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3035300977197482894533291 4552951465796224341799937)
              ·
                refine ⟨3414713599347168256349953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4552951465796224341799937 3414713599347168256349953)
                ·
                  refine ⟨2561035199510376192262465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3414713599347168256349953 2561035199510376192262465)
                  ·
                    refine ⟨1920776399632782144196849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2561035199510376192262465 1920776399632782144196849)
                    ·
                      refine ⟨1440582299724586608147637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1920776399632782144196849 1440582299724586608147637)
                      ·
                        rfl

theorem cell23_2805524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_2805524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805524 prefixEnd_2805524 := by exact prefixLift 2805524
  have htrace : WordTrace (prefixWord ++ tailWord_2805524) baseStart_2805524 baseEnd_2805524 := by
    simpa [prefixWord, tailWord_2805524, baseEnd_2805524] using wordTrace_append hprefix tailTrace_2805524
  have hstable : (prefixWord ++ tailWord_2805524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805524).length < 2 ^ (prefixWord ++ tailWord_2805524).sum := by decide
  have hdescent : baseEnd_2805524 < baseStart_2805524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805556 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_2805556 : Nat := 118140960795 + 2805556 * 2 ^ 59
def prefixEnd_2805556 : Nat := 4983230072969 + 3 ^ 40 * 2805556 * 2
def baseEnd_2805556 : Nat := 480199577035176827649163

theorem tailTrace_2805556 : CollatzResearch.WordTrace tailWord_2805556 prefixEnd_2805556 480199577035176827649163 := by
  unfold tailWord_2805556
  simp only [CollatzResearch.WordTrace]
  refine ⟨51163516911978618831382261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68218022549304825108509681 51163516911978618831382261)
  ·
    refine ⟨4796579710497995515442087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51163516911978618831382261 4796579710497995515442087)
    ·
      refine ⟨7194869565746993273163131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4796579710497995515442087 7194869565746993273163131)
      ·
        refine ⟨10792304348620489909744697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7194869565746993273163131 10792304348620489909744697)
        ·
          refine ⟨8094228261465367432308523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10792304348620489909744697 8094228261465367432308523)
          ·
            refine ⟨12141342392198051148462785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8094228261465367432308523 12141342392198051148462785)
            ·
              refine ⟨9106006794148538361347089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12141342392198051148462785 9106006794148538361347089)
              ·
                refine ⟨6829505095611403771010317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9106006794148538361347089 6829505095611403771010317)
                ·
                  refine ⟨2561064410854276414128869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6829505095611403771010317 2561064410854276414128869)
                  ·
                    refine ⟨480199577035176827649163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2561064410854276414128869 480199577035176827649163)
                    ·
                      rfl

theorem cell23_2805556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_2805556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805556 prefixEnd_2805556 := by exact prefixLift 2805556
  have htrace : WordTrace (prefixWord ++ tailWord_2805556) baseStart_2805556 baseEnd_2805556 := by
    simpa [prefixWord, tailWord_2805556, baseEnd_2805556] using wordTrace_append hprefix tailTrace_2805556
  have hstable : (prefixWord ++ tailWord_2805556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805556).length < 2 ^ (prefixWord ++ tailWord_2805556).sum := by decide
  have hdescent : baseEnd_2805556 < baseStart_2805556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805582 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 7, 5]
def baseStart_2805582 : Nat := 118140960795 + 2805582 * 2 ^ 59
def prefixEnd_2805582 : Nat := 4983230072969 + 3 ^ 40 * 2805582 * 2
def baseEnd_2805582 : Nat := 480204027200849127074123

theorem tailTrace_2805582 : CollatzResearch.WordTrace tailWord_2805582 prefixEnd_2805582 480204027200849127074123 := by
  unfold tailWord_2805582
  simp only [CollatzResearch.WordTrace]
  refine ⟨12790997765232880512901375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68218654747908696068807333 12790997765232880512901375)
  ·
    refine ⟨19186496647849320769352063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12790997765232880512901375 19186496647849320769352063)
    ·
      refine ⟨28779744971773981154028095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19186496647849320769352063 28779744971773981154028095)
      ·
        refine ⟨43169617457660971731042143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28779744971773981154028095 43169617457660971731042143)
        ·
          refine ⟨64754426186491457596563215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43169617457660971731042143 64754426186491457596563215)
          ·
            refine ⟨97131639279737186394844823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64754426186491457596563215 97131639279737186394844823)
            ·
              refine ⟨145697458919605779592267235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97131639279737186394844823 145697458919605779592267235)
              ·
                refine ⟨218546188379408669388400853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145697458919605779592267235 218546188379408669388400853)
                ·
                  refine ⟨5122176290142390688790645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 218546188379408669388400853 5122176290142390688790645)
                  ·
                    refine ⟨480204027200849127074123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5122176290142390688790645 480204027200849127074123)
                    ·
                      rfl

theorem cell23_2805582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_2805582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805582 prefixEnd_2805582 := by exact prefixLift 2805582
  have htrace : WordTrace (prefixWord ++ tailWord_2805582) baseStart_2805582 baseEnd_2805582 := by
    simpa [prefixWord, tailWord_2805582, baseEnd_2805582] using wordTrace_append hprefix tailTrace_2805582
  have hstable : (prefixWord ++ tailWord_2805582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805582).length < 2 ^ (prefixWord ++ tailWord_2805582).sum := by decide
  have hdescent : baseEnd_2805582 < baseStart_2805582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805603 : List Nat := [1, 1, 1, 5, 5, 1, 2, 1, 6]
def baseStart_2805603 : Nat := 118140960795 + 2805603 * 2 ^ 59
def prefixEnd_2805603 : Nat := 4983230072969 + 3 ^ 40 * 2805603 * 2
def baseEnd_2805603 : Nat := 160069207188476866562197

theorem tailTrace_2805603 : CollatzResearch.WordTrace tailWord_2805603 prefixEnd_2805603 160069207188476866562197 := by
  unfold tailWord_2805603
  simp only [CollatzResearch.WordTrace]
  refine ⟨102328748054786964689725463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68219165369857976459816975 102328748054786964689725463)
  ·
    refine ⟨153493122082180447034588195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102328748054786964689725463 153493122082180447034588195)
    ·
      refine ⟨230239683123270670551882293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153493122082180447034588195 230239683123270670551882293)
      ·
        refine ⟨21584970292806625364238965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 230239683123270670551882293 21584970292806625364238965)
        ·
          refine ⟨2023590964950621127897403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21584970292806625364238965 2023590964950621127897403)
          ·
            refine ⟨3035386447425931691846105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2023590964950621127897403 3035386447425931691846105)
            ·
              refine ⟨2276539835569448768884579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3035386447425931691846105 2276539835569448768884579)
              ·
                refine ⟨3414809753354173153326869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2276539835569448768884579 3414809753354173153326869)
                ·
                  refine ⟨160069207188476866562197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3414809753354173153326869 160069207188476866562197)
                  ·
                    rfl

theorem cell23_2805603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 6].length) (baseStart_2805603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805603 prefixEnd_2805603 := by exact prefixLift 2805603
  have htrace : WordTrace (prefixWord ++ tailWord_2805603) baseStart_2805603 baseEnd_2805603 := by
    simpa [prefixWord, tailWord_2805603, baseEnd_2805603] using wordTrace_append hprefix tailTrace_2805603
  have hstable : (prefixWord ++ tailWord_2805603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805603).length < 2 ^ (prefixWord ++ tailWord_2805603).sum := by decide
  have hdescent : baseEnd_2805603 < baseStart_2805603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805642 : List Nat := [3, 1, 2, 4, 13]
def baseStart_2805642 : Nat := 118140960795 + 2805642 * 2 ^ 59
def prefixEnd_2805642 : Nat := 4983230072969 + 3 ^ 40 * 2805642 * 2
def baseEnd_2805642 : Nat := 1976190521868061929317

theorem tailTrace_2805642 : CollatzResearch.WordTrace tailWord_2805642 prefixEnd_2805642 1976190521868061929317 := by
  unfold tailWord_2805642
  simp only [CollatzResearch.WordTrace]
  refine ⟨25582542625411418587598795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68220113667763782900263453 25582542625411418587598795)
  ·
    refine ⟨38373813938117127881398193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25582542625411418587598795 38373813938117127881398193)
    ·
      refine ⟨28780360453587845911048645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38373813938117127881398193 28780360453587845911048645)
      ·
        refine ⟨5396317585047721108321621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28780360453587845911048645 5396317585047721108321621)
        ·
          refine ⟨1976190521868061929317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 5396317585047721108321621 1976190521868061929317)
          ·
            rfl

theorem cell23_2805642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 13].length) (baseStart_2805642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805642 prefixEnd_2805642 := by exact prefixLift 2805642
  have htrace : WordTrace (prefixWord ++ tailWord_2805642) baseStart_2805642 baseEnd_2805642 := by
    simpa [prefixWord, tailWord_2805642, baseEnd_2805642] using wordTrace_append hprefix tailTrace_2805642
  have hstable : (prefixWord ++ tailWord_2805642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805642).length < 2 ^ (prefixWord ++ tailWord_2805642).sum := by decide
  have hdescent : baseEnd_2805642 < baseStart_2805642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805729 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 2, 4, 3]
def baseStart_2805729 : Nat := 118140960795 + 2805729 * 2 ^ 59
def prefixEnd_2805729 : Nat := 4983230072969 + 3 ^ 40 * 2805729 * 2
def baseEnd_2805729 : Nat := 1440687563258758306084193

theorem tailTrace_2805729 : CollatzResearch.WordTrace tailWord_2805729 prefixEnd_2805729 1440687563258758306084193 := by
  unfold tailWord_2805729
  simp only [CollatzResearch.WordTrace]
  refine ⟨102333343652330488208812241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68222229101553658805874827 102333343652330488208812241)
  ·
    refine ⟨76750007739247866156609181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102333343652330488208812241 76750007739247866156609181)
    ·
      refine ⟨28781252902217949808728443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76750007739247866156609181 28781252902217949808728443)
      ·
        refine ⟨43171879353326924713092665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28781252902217949808728443 43171879353326924713092665)
        ·
          refine ⟨32378909514995193534819499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43171879353326924713092665 32378909514995193534819499)
          ·
            refine ⟨48568364272492790302229249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32378909514995193534819499 48568364272492790302229249)
            ·
              refine ⟨36426273204369592726671937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48568364272492790302229249 36426273204369592726671937)
              ·
                refine ⟨27319704903277194545003953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36426273204369592726671937 27319704903277194545003953)
                ·
                  refine ⟨20489778677457895908752965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27319704903277194545003953 20489778677457895908752965)
                  ·
                    refine ⟨3841833502023355482891181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20489778677457895908752965 3841833502023355482891181)
                    ·
                      refine ⟨1440687563258758306084193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3841833502023355482891181 1440687563258758306084193)
                      ·
                        rfl

theorem cell23_2805729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_2805729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805729 prefixEnd_2805729 := by exact prefixLift 2805729
  have htrace : WordTrace (prefixWord ++ tailWord_2805729) baseStart_2805729 baseEnd_2805729 := by
    simpa [prefixWord, tailWord_2805729, baseEnd_2805729] using wordTrace_append hprefix tailTrace_2805729
  have hstable : (prefixWord ++ tailWord_2805729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805729).length < 2 ^ (prefixWord ++ tailWord_2805729).sum := by decide
  have hdescent : baseEnd_2805729 < baseStart_2805729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805759 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 3]
def baseStart_2805759 : Nat := 118140960795 + 2805759 * 2 ^ 59
def prefixEnd_2805759 : Nat := 4983230072969 + 3 ^ 40 * 2805759 * 2
def baseEnd_2805759 : Nat := 1440702967678393188709055

theorem tailTrace_2805759 : CollatzResearch.WordTrace tailWord_2805759 prefixEnd_2805759 1440702967678393188709055 := by
  unfold tailWord_2805759
  simp only [CollatzResearch.WordTrace]
  refine ⟨102334437842221803332404331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68222958561481202221602887 102334437842221803332404331)
  ·
    refine ⟨153501656763332704998606497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102334437842221803332404331 153501656763332704998606497)
    ·
      refine ⟨115126242572499528748954873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153501656763332704998606497 115126242572499528748954873)
      ·
        refine ⟨86344681929374646561716155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115126242572499528748954873 86344681929374646561716155)
        ·
          refine ⟨129517022894061969842574233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86344681929374646561716155 129517022894061969842574233)
          ·
            refine ⟨97137767170546477381930675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129517022894061969842574233 97137767170546477381930675)
            ·
              refine ⟨145706650755819716072896013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97137767170546477381930675 145706650755819716072896013)
              ·
                refine ⟨54639994033432393527336005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145706650755819716072896013 54639994033432393527336005)
                ·
                  refine ⟨10244998881268573786375501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54639994033432393527336005 10244998881268573786375501)
                  ·
                    refine ⟨3841874580475715169890813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10244998881268573786375501 3841874580475715169890813)
                    ·
                      refine ⟨1440702967678393188709055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3841874580475715169890813 1440702967678393188709055)
                      ·
                        rfl

theorem cell23_2805759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_2805759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805759 prefixEnd_2805759 := by exact prefixLift 2805759
  have htrace : WordTrace (prefixWord ++ tailWord_2805759) baseStart_2805759 baseEnd_2805759 := by
    simpa [prefixWord, tailWord_2805759, baseEnd_2805759] using wordTrace_append hprefix tailTrace_2805759
  have hstable : (prefixWord ++ tailWord_2805759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805759).length < 2 ^ (prefixWord ++ tailWord_2805759).sum := by decide
  have hdescent : baseEnd_2805759 < baseStart_2805759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805806 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_2805806 : Nat := 118140960795 + 2805806 * 2 ^ 59
def prefixEnd_2805806 : Nat := 4983230072969 + 3 ^ 40 * 2805806 * 2
def baseEnd_2805806 : Nat := 1440727101269154504821339

theorem tailTrace_2805806 : CollatzResearch.WordTrace tailWord_2805806 prefixEnd_2805806 1440727101269154504821339 := by
  unfold tailWord_2805806
  simp only [CollatzResearch.WordTrace]
  refine ⟨12792019009131441294920659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68224101382034353572910181 12792019009131441294920659)
  ·
    refine ⟨19188028513697161942380989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12792019009131441294920659 19188028513697161942380989)
    ·
      refine ⟨7195510692636435728392871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19188028513697161942380989 7195510692636435728392871)
      ·
        refine ⟨10793266038954653592589307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7195510692636435728392871 10793266038954653592589307)
        ·
          refine ⟨16189899058431980388883961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10793266038954653592589307 16189899058431980388883961)
          ·
            refine ⟨12142424293823985291662971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16189899058431980388883961 12142424293823985291662971)
            ·
              refine ⟨18213636440735977937494457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12142424293823985291662971 18213636440735977937494457)
              ·
                refine ⟨13660227330551983453120843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18213636440735977937494457 13660227330551983453120843)
                ·
                  refine ⟨20490340995827975179681265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13660227330551983453120843 20490340995827975179681265)
                  ·
                    refine ⟨15367755746870981384760949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20490340995827975179681265 15367755746870981384760949)
                    ·
                      refine ⟨1440727101269154504821339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15367755746870981384760949 1440727101269154504821339)
                      ·
                        rfl

theorem cell23_2805806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_2805806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805806 prefixEnd_2805806 := by exact prefixLift 2805806
  have htrace : WordTrace (prefixWord ++ tailWord_2805806) baseStart_2805806 baseEnd_2805806 := by
    simpa [prefixWord, tailWord_2805806, baseEnd_2805806] using wordTrace_append hprefix tailTrace_2805806
  have hstable : (prefixWord ++ tailWord_2805806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805806).length < 2 ^ (prefixWord ++ tailWord_2805806).sum := by decide
  have hdescent : baseEnd_2805806 < baseStart_2805806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805817 : List Nat := [1, 2, 1, 5, 4, 1, 2, 2, 5]
def baseStart_2805817 : Nat := 118140960795 + 2805817 * 2 ^ 59
def prefixEnd_2805817 : Nat := 4983230072969 + 3 ^ 40 * 2805817 * 2
def baseEnd_2805817 : Nat := 160081416617372662420421

theorem tailTrace_2805817 : CollatzResearch.WordTrace tailWord_2805817 prefixEnd_2805817 160081416617372662420421 := by
  unfold tailWord_2805817
  simp only [CollatzResearch.WordTrace]
  refine ⟨102336553276011679238015705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68224368850674452825343803 102336553276011679238015705)
  ·
    refine ⟨76752414957008759428511779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102336553276011679238015705 76752414957008759428511779)
    ·
      refine ⟨115128622435513139142767669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76752414957008759428511779 115128622435513139142767669)
      ·
        refine ⟨10793308353329356794634469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115128622435513139142767669 10793308353329356794634469)
        ·
          refine ⟨2023745316249254398993963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10793308353329356794634469 2023745316249254398993963)
          ·
            refine ⟨3035617974373881598490945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2023745316249254398993963 3035617974373881598490945)
            ·
              refine ⟨2276713480780411198868209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3035617974373881598490945 2276713480780411198868209)
              ·
                refine ⟨1707535110585308399151157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2276713480780411198868209 1707535110585308399151157)
                ·
                  refine ⟨160081416617372662420421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1707535110585308399151157 160081416617372662420421)
                  ·
                    rfl

theorem cell23_2805817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 5].length) (baseStart_2805817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805817 prefixEnd_2805817 := by exact prefixLift 2805817
  have htrace : WordTrace (prefixWord ++ tailWord_2805817) baseStart_2805817 baseEnd_2805817 := by
    simpa [prefixWord, tailWord_2805817, baseEnd_2805817] using wordTrace_append hprefix tailTrace_2805817
  have hstable : (prefixWord ++ tailWord_2805817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805817).length < 2 ^ (prefixWord ++ tailWord_2805817).sum := by decide
  have hdescent : baseEnd_2805817 < baseStart_2805817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805829 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 2, 4, 4]
def baseStart_2805829 : Nat := 118140960795 + 2805829 * 2 ^ 59
def prefixEnd_2805829 : Nat := 4983230072969 + 3 ^ 40 * 2805829 * 2
def baseEnd_2805829 : Nat := 1440738911324207914833733

theorem tailTrace_2805829 : CollatzResearch.WordTrace tailWord_2805829 prefixEnd_2805829 1440738911324207914833733 := by
  unfold tailWord_2805829
  simp only [CollatzResearch.WordTrace]
  refine ⟨102336990951968205287452541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68224660634645470191635027 102336990951968205287452541)
  ·
    refine ⟨38376371606988076982794703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102336990951968205287452541 38376371606988076982794703)
    ·
      refine ⟨57564557410482115474192055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38376371606988076982794703 57564557410482115474192055)
      ·
        refine ⟨86346836115723173211288083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57564557410482115474192055 86346836115723173211288083)
        ·
          refine ⟨129520254173584759816932125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86346836115723173211288083 129520254173584759816932125)
          ·
            refine ⟨48570095315094284931349547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129520254173584759816932125 48570095315094284931349547)
            ·
              refine ⟨72855142972641427397024321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48570095315094284931349547 72855142972641427397024321)
              ·
                refine ⟨54641357229481070547768241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72855142972641427397024321 54641357229481070547768241)
                ·
                  refine ⟨40981017922110802910826181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54641357229481070547768241 40981017922110802910826181)
                  ·
                    refine ⟨7683940860395775545779909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40981017922110802910826181 7683940860395775545779909)
                    ·
                      refine ⟨1440738911324207914833733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7683940860395775545779909 1440738911324207914833733)
                      ·
                        rfl

theorem cell23_2805829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_2805829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805829 prefixEnd_2805829 := by exact prefixLift 2805829
  have htrace : WordTrace (prefixWord ++ tailWord_2805829) baseStart_2805829 baseEnd_2805829 := by
    simpa [prefixWord, tailWord_2805829, baseEnd_2805829] using wordTrace_append hprefix tailTrace_2805829
  have hstable : (prefixWord ++ tailWord_2805829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805829).length < 2 ^ (prefixWord ++ tailWord_2805829).sum := by decide
  have hdescent : baseEnd_2805829 < baseStart_2805829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805836 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 4, 2, 3]
def baseStart_2805836 : Nat := 118140960795 + 2805836 * 2 ^ 59
def prefixEnd_2805836 : Nat := 4983230072969 + 3 ^ 40 * 2805836 * 2
def baseEnd_2805836 : Nat := 1440742505688789387446201

theorem tailTrace_2805836 : CollatzResearch.WordTrace tailWord_2805836 prefixEnd_2805836 1440742505688789387446201 := by
  unfold tailWord_2805836
  simp only [CollatzResearch.WordTrace]
  refine ⟨51168623131471422741478681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68224830841961896988638241 51168623131471422741478681)
  ·
    refine ⟨38376467348603567056109011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51168623131471422741478681 38376467348603567056109011)
    ·
      refine ⟨57564701022905350584163517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38376467348603567056109011 57564701022905350584163517)
      ·
        refine ⟨21586762883589506469061319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57564701022905350584163517 21586762883589506469061319)
        ·
          refine ⟨32380144325384259703591979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21586762883589506469061319 32380144325384259703591979)
          ·
            refine ⟨48570216488076389555387969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32380144325384259703591979 48570216488076389555387969)
            ·
              refine ⟨36427662366057292166540977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48570216488076389555387969 36427662366057292166540977)
              ·
                refine ⟨27320746774542969124905733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36427662366057292166540977 27320746774542969124905733)
                ·
                  refine ⟨5122640020226806710919825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27320746774542969124905733 5122640020226806710919825)
                  ·
                    refine ⟨3841980015170105033189869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5122640020226806710919825 3841980015170105033189869)
                    ·
                      refine ⟨1440742505688789387446201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3841980015170105033189869 1440742505688789387446201)
                      ·
                        rfl

theorem cell23_2805836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_2805836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805836 prefixEnd_2805836 := by exact prefixLift 2805836
  have htrace : WordTrace (prefixWord ++ tailWord_2805836) baseStart_2805836 baseEnd_2805836 := by
    simpa [prefixWord, tailWord_2805836, baseEnd_2805836] using wordTrace_append hprefix tailTrace_2805836
  have hstable : (prefixWord ++ tailWord_2805836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805836).length < 2 ^ (prefixWord ++ tailWord_2805836).sum := by decide
  have hdescent : baseEnd_2805836 < baseStart_2805836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805893 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 1, 5, 2]
def baseStart_2805893 : Nat := 118140960795 + 2805893 * 2 ^ 59
def prefixEnd_2805893 : Nat := 4983230072969 + 3 ^ 40 * 2805893 * 2
def baseEnd_2805893 : Nat := 1440771774086095664433439

theorem tailTrace_2805893 : CollatzResearch.WordTrace tailWord_2805893 prefixEnd_2805893 1440771774086095664433439 := by
  unfold tailWord_2805893
  simp only [CollatzResearch.WordTrace]
  refine ⟨102339325223736344217782333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68226216815824229478521555 102339325223736344217782333)
  ·
    refine ⟨38377246958901129081668375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102339325223736344217782333 38377246958901129081668375)
    ·
      refine ⟨57565870438351693622502563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38377246958901129081668375 57565870438351693622502563)
      ·
        refine ⟨86348805657527540433753845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57565870438351693622502563 86348805657527540433753845)
        ·
          refine ⟨8095200530393206915664423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86348805657527540433753845 8095200530393206915664423)
          ·
            refine ⟨12142800795589810373496635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8095200530393206915664423 12142800795589810373496635)
            ·
              refine ⟨18214201193384715560244953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12142800795589810373496635 18214201193384715560244953)
              ·
                refine ⟨13660650895038536670183715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18214201193384715560244953 13660650895038536670183715)
                ·
                  refine ⟨20490976342557805005275573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13660650895038536670183715 20490976342557805005275573)
                  ·
                    refine ⟨1921029032114794219244585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20490976342557805005275573 1921029032114794219244585)
                    ·
                      refine ⟨1440771774086095664433439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1921029032114794219244585 1440771774086095664433439)
                      ·
                        rfl

theorem cell23_2805893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 5, 2].length) (baseStart_2805893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805893 prefixEnd_2805893 := by exact prefixLift 2805893
  have htrace : WordTrace (prefixWord ++ tailWord_2805893) baseStart_2805893 baseEnd_2805893 := by
    simpa [prefixWord, tailWord_2805893, baseEnd_2805893] using wordTrace_append hprefix tailTrace_2805893
  have hstable : (prefixWord ++ tailWord_2805893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805893).length < 2 ^ (prefixWord ++ tailWord_2805893).sum := by decide
  have hdescent : baseEnd_2805893 < baseStart_2805893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805916 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 3, 6]
def baseStart_2805916 : Nat := 118140960795 + 2805916 * 2 ^ 59
def prefixEnd_2805916 : Nat := 4983230072969 + 3 ^ 40 * 2805916 * 2
def baseEnd_2805916 : Nat := 480261194713716358148611

theorem tailTrace_2805916 : CollatzResearch.WordTrace tailWord_2805916 prefixEnd_2805916 480261194713716358148611 := by
  unfold tailWord_2805916
  simp only [CollatzResearch.WordTrace]
  refine ⟨51170082051326509572934801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68226776068435346097246401 51170082051326509572934801)
  ·
    refine ⟨38377561538494882179701101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51170082051326509572934801 38377561538494882179701101)
    ·
      refine ⟨14391585576935580817387913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38377561538494882179701101 14391585576935580817387913)
      ·
        refine ⟨10793689182701685613040935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14391585576935580817387913 10793689182701685613040935)
        ·
          refine ⟨16190533774052528419561403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10793689182701685613040935 16190533774052528419561403)
          ·
            refine ⟨24285800661078792629342105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16190533774052528419561403 24285800661078792629342105)
            ·
              refine ⟨18214350495809094472006579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24285800661078792629342105 18214350495809094472006579)
              ·
                refine ⟨27321525743713641708009869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18214350495809094472006579 27321525743713641708009869)
                ·
                  refine ⟨10245572153892615640503701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27321525743713641708009869 10245572153892615640503701)
                  ·
                    refine ⟨480261194713716358148611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10245572153892615640503701 480261194713716358148611)
                    ·
                      rfl

theorem cell23_2805916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_2805916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805916 prefixEnd_2805916 := by exact prefixLift 2805916
  have htrace : WordTrace (prefixWord ++ tailWord_2805916) baseStart_2805916 baseEnd_2805916 := by
    simpa [prefixWord, tailWord_2805916, baseEnd_2805916] using wordTrace_append hprefix tailTrace_2805916
  have hstable : (prefixWord ++ tailWord_2805916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805916).length < 2 ^ (prefixWord ++ tailWord_2805916).sum := by decide
  have hdescent : baseEnd_2805916 < baseStart_2805916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805917 : List Nat := [1, 4, 2, 1, 1, 3, 3, 3, 1, 1, 3]
def baseStart_2805917 : Nat := 118140960795 + 2805917 * 2 ^ 59
def prefixEnd_2805917 : Nat := 4983230072969 + 3 ^ 40 * 2805917 * 2
def baseEnd_2805917 : Nat := 1440784097621803570533329

theorem tailTrace_2805917 : CollatzResearch.WordTrace tailWord_2805917 prefixEnd_2805917 1440784097621803570533329 := by
  unfold tailWord_2805917
  simp only [CollatzResearch.WordTrace]
  refine ⟨102340200575649396316656005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68226800383766264211104003 102340200575649396316656005)
  ·
    refine ⟨19188787607934261809373001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102340200575649396316656005 19188787607934261809373001)
    ·
      refine ⟨14391590705950696357029751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19188787607934261809373001 14391590705950696357029751)
      ·
        refine ⟨21587386058926044535544627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14391590705950696357029751 21587386058926044535544627)
        ·
          refine ⟨32381079088389066803316941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21587386058926044535544627 32381079088389066803316941)
          ·
            refine ⟨12142904658145900051243853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32381079088389066803316941 12142904658145900051243853)
            ·
              refine ⟨4553589246804712519216445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12142904658145900051243853 4553589246804712519216445)
              ·
                refine ⟨1707595967551767194706167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4553589246804712519216445 1707595967551767194706167)
                ·
                  refine ⟨2561393951327650792059251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1707595967551767194706167 2561393951327650792059251)
                  ·
                    refine ⟨3842090926991476188088877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2561393951327650792059251 3842090926991476188088877)
                    ·
                      refine ⟨1440784097621803570533329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3842090926991476188088877 1440784097621803570533329)
                      ·
                        rfl

theorem cell23_2805917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_2805917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805917 prefixEnd_2805917 := by exact prefixLift 2805917
  have htrace : WordTrace (prefixWord ++ tailWord_2805917) baseStart_2805917 baseEnd_2805917 := by
    simpa [prefixWord, tailWord_2805917, baseEnd_2805917] using wordTrace_append hprefix tailTrace_2805917
  have hstable : (prefixWord ++ tailWord_2805917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805917).length < 2 ^ (prefixWord ++ tailWord_2805917).sum := by decide
  have hdescent : baseEnd_2805917 < baseStart_2805917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805927 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_2805927 : Nat := 118140960795 + 2805927 * 2 ^ 59
def prefixEnd_2805927 : Nat := 4983230072969 + 3 ^ 40 * 2805927 * 2
def baseEnd_2805927 : Nat := 1440789232428348531408283

theorem tailTrace_2805927 : CollatzResearch.WordTrace tailWord_2805927 prefixEnd_2805927 1440789232428348531408283 := by
  unfold tailWord_2805927
  simp only [CollatzResearch.WordTrace]
  refine ⟨102340565305613168024520035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68227043537075445349680023 102340565305613168024520035)
  ·
    refine ⟨153510847958419752036780053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102340565305613168024520035 153510847958419752036780053)
    ·
      refine ⟨7195820998050925876724065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 153510847958419752036780053 7195820998050925876724065)
      ·
        refine ⟨5396865748538194407543049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7195820998050925876724065 5396865748538194407543049)
        ·
          refine ⟨4047649311403645805657287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5396865748538194407543049 4047649311403645805657287)
          ·
            refine ⟨6071473967105468708485931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4047649311403645805657287 6071473967105468708485931)
            ·
              refine ⟨9107210950658203062728897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6071473967105468708485931 9107210950658203062728897)
              ·
                refine ⟨6830408212993652297046673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9107210950658203062728897 6830408212993652297046673)
                ·
                  refine ⟨5122806159745239222785005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6830408212993652297046673 5122806159745239222785005)
                  ·
                    refine ⟨1921052309904464708544377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5122806159745239222785005 1921052309904464708544377)
                    ·
                      refine ⟨1440789232428348531408283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1921052309904464708544377 1440789232428348531408283)
                      ·
                        rfl

theorem cell23_2805927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_2805927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805927 prefixEnd_2805927 := by exact prefixLift 2805927
  have htrace : WordTrace (prefixWord ++ tailWord_2805927) baseStart_2805927 baseEnd_2805927 := by
    simpa [prefixWord, tailWord_2805927, baseEnd_2805927] using wordTrace_append hprefix tailTrace_2805927
  have hstable : (prefixWord ++ tailWord_2805927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805927).length < 2 ^ (prefixWord ++ tailWord_2805927).sum := by decide
  have hdescent : baseEnd_2805927 < baseStart_2805927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805954 : List Nat := [3, 5, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_2805954 : Nat := 118140960795 + 2805954 * 2 ^ 59
def prefixEnd_2805954 : Nat := 4983230072969 + 3 ^ 40 * 2805954 * 2
def baseEnd_2805954 : Nat := 480267698802006641923553

theorem tailTrace_2805954 : CollatzResearch.WordTrace tailWord_2805954 prefixEnd_2805954 480267698802006641923553 := by
  unfold tailWord_2805954
  simp only [CollatzResearch.WordTrace]
  refine ⟨25585387519128837908938229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68227700051010234423835277 25585387519128837908938229)
  ·
    refine ⟨2398630079918328553962959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25585387519128837908938229 2398630079918328553962959)
    ·
      refine ⟨3597945119877492830944439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2398630079918328553962959 3597945119877492830944439)
      ·
        refine ⟨5396917679816239246416659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3597945119877492830944439 5396917679816239246416659)
        ·
          refine ⟨8095376519724358869624989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5396917679816239246416659 8095376519724358869624989)
          ·
            refine ⟨3035766194896634576109371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8095376519724358869624989 3035766194896634576109371)
            ·
              refine ⟨4553649292344951864164057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3035766194896634576109371 4553649292344951864164057)
              ·
                refine ⟨3415236969258713898123043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4553649292344951864164057 3415236969258713898123043)
                ·
                  refine ⟨5122855453888070847184565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3415236969258713898123043 5122855453888070847184565)
                  ·
                    refine ⟨480267698802006641923553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5122855453888070847184565 480267698802006641923553)
                    ·
                      rfl

theorem cell23_2805954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_2805954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805954 prefixEnd_2805954 := by exact prefixLift 2805954
  have htrace : WordTrace (prefixWord ++ tailWord_2805954) baseStart_2805954 baseEnd_2805954 := by
    simpa [prefixWord, tailWord_2805954, baseEnd_2805954] using wordTrace_append hprefix tailTrace_2805954
  have hstable : (prefixWord ++ tailWord_2805954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805954).length < 2 ^ (prefixWord ++ tailWord_2805954).sum := by decide
  have hdescent : baseEnd_2805954 < baseStart_2805954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805974 : List Nat := [5, 2, 1, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_2805974 : Nat := 118140960795 + 2805974 * 2 ^ 59
def prefixEnd_2805974 : Nat := 4983230072969 + 3 ^ 40 * 2805974 * 2
def baseEnd_2805974 : Nat := 1440813366019109847520567

theorem tailTrace_2805974 : CollatzResearch.WordTrace tailWord_2805974 prefixEnd_2805974 1440813366019109847520567 := by
  unfold tailWord_2805974
  simp only [CollatzResearch.WordTrace]
  refine ⟨6396392471027680940717561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68228186357628596700987317 6396392471027680940717561)
  ·
    refine ⟨4797294353270760705538171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6396392471027680940717561 4797294353270760705538171)
    ·
      refine ⟨7195941529906141058307257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4797294353270760705538171 7195941529906141058307257)
      ·
        refine ⟨5396956147429605793730443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7195941529906141058307257 5396956147429605793730443)
        ·
          refine ⟨8095434221144408690595665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5396956147429605793730443 8095434221144408690595665)
          ·
            refine ⟨6071575665858306517946749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8095434221144408690595665 6071575665858306517946749)
            ·
              refine ⟨2276840874696864944230031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6071575665858306517946749 2276840874696864944230031)
              ·
                refine ⟨3415261312045297416345047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2276840874696864944230031 3415261312045297416345047)
                ·
                  refine ⟨5122891968067946124517571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3415261312045297416345047 5122891968067946124517571)
                  ·
                    refine ⟨7684337952101919186776357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5122891968067946124517571 7684337952101919186776357)
                    ·
                      refine ⟨1440813366019109847520567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7684337952101919186776357 1440813366019109847520567)
                      ·
                        rfl

theorem cell23_2805974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_2805974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805974 prefixEnd_2805974 := by exact prefixLift 2805974
  have htrace : WordTrace (prefixWord ++ tailWord_2805974) baseStart_2805974 baseEnd_2805974 := by
    simpa [prefixWord, tailWord_2805974, baseEnd_2805974] using wordTrace_append hprefix tailTrace_2805974
  have hstable : (prefixWord ++ tailWord_2805974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805974).length < 2 ^ (prefixWord ++ tailWord_2805974).sum := by decide
  have hdescent : baseEnd_2805974 < baseStart_2805974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805980 : List Nat := [2, 2, 5, 2, 2, 10]
def baseStart_2805980 : Nat := 118140960795 + 2805980 * 2 ^ 59
def prefixEnd_2805980 : Nat := 4983230072969 + 3 ^ 40 * 2805980 * 2
def baseEnd_2805980 : Nat := 5929285789724431374673

theorem tailTrace_2805980 : CollatzResearch.WordTrace tailWord_2805980 prefixEnd_2805980 5929285789724431374673 := by
  unfold tailWord_2805980
  simp only [CollatzResearch.WordTrace]
  refine ⟨51171249187210579038099697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68228332249614105384132929 51171249187210579038099697)
  ·
    refine ⟨38378436890407934278574773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51171249187210579038099697 38378436890407934278574773)
    ·
      refine ⟨3597978458475743838616385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38378436890407934278574773 3597978458475743838616385)
      ·
        refine ⟨2698483843856807878962289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3597978458475743838616385 2698483843856807878962289)
        ·
          refine ⟨2023862882892605909221717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2698483843856807878962289 2023862882892605909221717)
          ·
            refine ⟨5929285789724431374673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2023862882892605909221717 5929285789724431374673)
            ·
              rfl

theorem cell23_2805980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 10].length) (baseStart_2805980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805980 prefixEnd_2805980 := by exact prefixLift 2805980
  have htrace : WordTrace (prefixWord ++ tailWord_2805980) baseStart_2805980 baseEnd_2805980 := by
    simpa [prefixWord, tailWord_2805980, baseEnd_2805980] using wordTrace_append hprefix tailTrace_2805980
  have hstable : (prefixWord ++ tailWord_2805980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805980).length < 2 ^ (prefixWord ++ tailWord_2805980).sum := by decide
  have hdescent : baseEnd_2805980 < baseStart_2805980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805991 : List Nat := [1, 1, 5, 3, 1, 1, 4, 2, 1, 2, 2]
def baseStart_2805991 : Nat := 118140960795 + 2805991 * 2 ^ 59
def prefixEnd_2805991 : Nat := 4983230072969 + 3 ^ 40 * 2805991 * 2
def baseEnd_2805991 : Nat := 1440822095190236281007989

theorem tailTrace_2805991 : CollatzResearch.WordTrace tailWord_2805991 prefixEnd_2805991 1440822095190236281007989 := by
  unfold tailWord_2805991
  simp only [CollatzResearch.WordTrace]
  refine ⟨102342899577381306954849827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68228599718254204636566551 102342899577381306954849827)
  ·
    refine ⟨153514349366071960432274741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102342899577381306954849827 153514349366071960432274741)
    ·
      refine ⟨14391970253069246290525757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153514349366071960432274741 14391970253069246290525757)
      ·
        refine ⟨5396988844900967358947159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14391970253069246290525757 5396988844900967358947159)
        ·
          refine ⟨8095483267351451038420739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5396988844900967358947159 8095483267351451038420739)
          ·
            refine ⟨12143224901027176557631109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8095483267351451038420739 12143224901027176557631109)
            ·
              refine ⟨2276854668942595604555833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12143224901027176557631109 2276854668942595604555833)
              ·
                refine ⟨1707641001706946703416875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2276854668942595604555833 1707641001706946703416875)
                ·
                  refine ⟨2561461502560420055125313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1707641001706946703416875 2561461502560420055125313)
                  ·
                    refine ⟨1921096126920315041343985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2561461502560420055125313 1921096126920315041343985)
                    ·
                      refine ⟨1440822095190236281007989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1921096126920315041343985 1440822095190236281007989)
                      ·
                        rfl

theorem cell23_2805991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_2805991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805991 prefixEnd_2805991 := by exact prefixLift 2805991
  have htrace : WordTrace (prefixWord ++ tailWord_2805991) baseStart_2805991 baseEnd_2805991 := by
    simpa [prefixWord, tailWord_2805991, baseEnd_2805991] using wordTrace_append hprefix tailTrace_2805991
  have hstable : (prefixWord ++ tailWord_2805991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805991).length < 2 ^ (prefixWord ++ tailWord_2805991).sum := by decide
  have hdescent : baseEnd_2805991 < baseStart_2805991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2805996 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 4]
def baseStart_2805996 : Nat := 118140960795 + 2805996 * 2 ^ 59
def prefixEnd_2805996 : Nat := 4983230072969 + 3 ^ 40 * 2805996 * 2
def baseEnd_2805996 : Nat := 1440824662593508761445465

theorem tailTrace_2805996 : CollatzResearch.WordTrace tailWord_2805996 prefixEnd_2805996 1440824662593508761445465 := by
  unfold tailWord_2805996
  simp only [CollatzResearch.WordTrace]
  refine ⟨51171540971181596404390921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68228721294908795205854561 51171540971181596404390921)
  ·
    refine ⟨38378655728386197303293191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51171540971181596404390921 38378655728386197303293191)
    ·
      refine ⟨57567983592579295954939787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38378655728386197303293191 57567983592579295954939787)
      ·
        refine ⟨86351975388868943932409681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57567983592579295954939787 86351975388868943932409681)
        ·
          refine ⟨64763981541651707949307261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86351975388868943932409681 64763981541651707949307261)
          ·
            refine ⟨24286493078119390480990223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64763981541651707949307261 24286493078119390480990223)
            ·
              refine ⟨36429739617179085721485335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24286493078119390480990223 36429739617179085721485335)
              ·
                refine ⟨54644609425768628582228003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36429739617179085721485335 54644609425768628582228003)
                ·
                  refine ⟨81966914138652942873342005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54644609425768628582228003 81966914138652942873342005)
                  ·
                    refine ⟨7684398200498713394375813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81966914138652942873342005 7684398200498713394375813)
                    ·
                      refine ⟨1440824662593508761445465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7684398200498713394375813 1440824662593508761445465)
                      ·
                        rfl

theorem cell23_2805996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_2805996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2805996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2805996 prefixEnd_2805996 := by exact prefixLift 2805996
  have htrace : WordTrace (prefixWord ++ tailWord_2805996) baseStart_2805996 baseEnd_2805996 := by
    simpa [prefixWord, tailWord_2805996, baseEnd_2805996] using wordTrace_append hprefix tailTrace_2805996
  have hstable : (prefixWord ++ tailWord_2805996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2805996).length < 2 ^ (prefixWord ++ tailWord_2805996).sum := by decide
  have hdescent : baseEnd_2805996 < baseStart_2805996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2805996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806016 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 5]
def baseStart_2806016 : Nat := 118140960795 + 2806016 * 2 ^ 59
def prefixEnd_2806016 : Nat := 4983230072969 + 3 ^ 40 * 2806016 * 2
def baseEnd_2806016 : Nat := 1440834932206598683195373

theorem tailTrace_2806016 : CollatzResearch.WordTrace tailWord_2806016 prefixEnd_2806016 1440834932206598683195373 := by
  unfold tailWord_2806016
  simp only [CollatzResearch.WordTrace]
  refine ⟨51171905701145368112254951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68229207601527157483006601 51171905701145368112254951)
  ·
    refine ⟨76757858551718052168382427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51171905701145368112254951 76757858551718052168382427)
    ·
      refine ⟨115136787827577078252573641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76757858551718052168382427 115136787827577078252573641)
      ·
        refine ⟨86352590870682808689430231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115136787827577078252573641 86352590870682808689430231)
        ·
          refine ⟨129528886306024213034145347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86352590870682808689430231 129528886306024213034145347)
          ·
            refine ⟨194293329459036319551218021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129528886306024213034145347 194293329459036319551218021)
            ·
              refine ⟨36429999273569309915853379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194293329459036319551218021 36429999273569309915853379)
              ·
                refine ⟨54644998910353964873780069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36429999273569309915853379 54644998910353964873780069)
                ·
                  refine ⟨10245937295691368413833763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54644998910353964873780069 10245937295691368413833763)
                  ·
                    refine ⟨15368905943537052620750645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10245937295691368413833763 15368905943537052620750645)
                    ·
                      refine ⟨1440834932206598683195373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15368905943537052620750645 1440834932206598683195373)
                      ·
                        rfl

theorem cell23_2806016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_2806016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806016 prefixEnd_2806016 := by exact prefixLift 2806016
  have htrace : WordTrace (prefixWord ++ tailWord_2806016) baseStart_2806016 baseEnd_2806016 := by
    simpa [prefixWord, tailWord_2806016, baseEnd_2806016] using wordTrace_append hprefix tailTrace_2806016
  have hstable : (prefixWord ++ tailWord_2806016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806016).length < 2 ^ (prefixWord ++ tailWord_2806016).sum := by decide
  have hdescent : baseEnd_2806016 < baseStart_2806016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806030 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2]
def baseStart_2806030 : Nat := 118140960795 + 2806030 * 2 ^ 59
def prefixEnd_2806030 : Nat := 4983230072969 + 3 ^ 40 * 2806030 * 2
def baseEnd_2806030 : Nat := 1440842120935761628420309

theorem tailTrace_2806030 : CollatzResearch.WordTrace tailWord_2806030 prefixEnd_2806030 1440842120935761628420309 := by
  unfold tailWord_2806030
  simp only [CollatzResearch.WordTrace]
  refine ⟨12793040253030002076939943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68229548016160011077013029 12793040253030002076939943)
  ·
    refine ⟨19189560379545003115409915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12793040253030002076939943 19189560379545003115409915)
    ·
      refine ⟨28784340569317504673114873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19189560379545003115409915 28784340569317504673114873)
      ·
        refine ⟨21588255426988128504836155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28784340569317504673114873 21588255426988128504836155)
        ·
          refine ⟨32382383140482192757254233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21588255426988128504836155 32382383140482192757254233)
          ·
            refine ⟨24286787355361644567940675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32382383140482192757254233 24286787355361644567940675)
            ·
              refine ⟨36430181033042466851911013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24286787355361644567940675 36430181033042466851911013)
              ·
                refine ⟨6830658943695462534733315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36430181033042466851911013 6830658943695462534733315)
                ·
                  refine ⟨10245988415543193802099973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6830658943695462534733315 10245988415543193802099973)
                  ·
                    refine ⟨1921122827914348837893745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10245988415543193802099973 1921122827914348837893745)
                    ·
                      refine ⟨1440842120935761628420309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1921122827914348837893745 1440842120935761628420309)
                      ·
                        rfl

theorem cell23_2806030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_2806030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806030 prefixEnd_2806030 := by exact prefixLift 2806030
  have htrace : WordTrace (prefixWord ++ tailWord_2806030) baseStart_2806030 baseEnd_2806030 := by
    simpa [prefixWord, tailWord_2806030, baseEnd_2806030] using wordTrace_append hprefix tailTrace_2806030
  have hstable : (prefixWord ++ tailWord_2806030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806030).length < 2 ^ (prefixWord ++ tailWord_2806030).sum := by decide
  have hdescent : baseEnd_2806030 < baseStart_2806030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806047 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 4, 2, 2]
def baseStart_2806047 : Nat := 118140960795 + 2806047 * 2 ^ 59
def prefixEnd_2806047 : Nat := 4983230072969 + 3 ^ 40 * 2806047 * 2
def baseEnd_2806047 : Nat := 1440850850106888061907731

theorem tailTrace_2806047 : CollatzResearch.WordTrace tailWord_2806047 prefixEnd_2806047 1440850850106888061907731 := by
  unfold tailWord_2806047
  simp only [CollatzResearch.WordTrace]
  refine ⟨102344942065178428518888395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68229961376785619012592263 102344942065178428518888395)
  ·
    refine ⟨153517413097767642778332593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102344942065178428518888395 153517413097767642778332593)
    ·
      refine ⟨115138059823325732083749445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153517413097767642778332593 115138059823325732083749445)
      ·
        refine ⟨21588386216873574765703021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115138059823325732083749445 21588386216873574765703021)
        ·
          refine ⟨8095644831327590537138633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21588386216873574765703021 8095644831327590537138633)
          ·
            refine ⟨6071733623495692902853975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8095644831327590537138633 6071733623495692902853975)
            ·
              refine ⟨9107600435243539354280963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6071733623495692902853975 9107600435243539354280963)
              ·
                refine ⟨13661400652865309031421445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9107600435243539354280963 13661400652865309031421445)
                ·
                  refine ⟨2561512622412245443391521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13661400652865309031421445 2561512622412245443391521)
                  ·
                    refine ⟨1921134466809184082543641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2561512622412245443391521 1921134466809184082543641)
                    ·
                      refine ⟨1440850850106888061907731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1921134466809184082543641 1440850850106888061907731)
                      ·
                        rfl

theorem cell23_2806047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_2806047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806047 prefixEnd_2806047 := by exact prefixLift 2806047
  have htrace : WordTrace (prefixWord ++ tailWord_2806047) baseStart_2806047 baseEnd_2806047 := by
    simpa [prefixWord, tailWord_2806047, baseEnd_2806047] using wordTrace_append hprefix tailTrace_2806047
  have hstable : (prefixWord ++ tailWord_2806047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806047).length < 2 ^ (prefixWord ++ tailWord_2806047).sum := by decide
  have hdescent : baseEnd_2806047 < baseStart_2806047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806063 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 3]
def baseStart_2806063 : Nat := 118140960795 + 2806063 * 2 ^ 59
def prefixEnd_2806063 : Nat := 4983230072969 + 3 ^ 40 * 2806063 * 2
def baseEnd_2806063 : Nat := 1440859065797359999307657

theorem tailTrace_2806063 : CollatzResearch.WordTrace tailWord_2806063 prefixEnd_2806063 1440859065797359999307657 := by
  unfold tailWord_2806063
  simp only [CollatzResearch.WordTrace]
  refine ⟨102345525633120463251470843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68230350422080308834313895 102345525633120463251470843)
  ·
    refine ⟨153518288449680694877206265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102345525633120463251470843 153518288449680694877206265)
    ·
      refine ⟨115138716337260521157904699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153518288449680694877206265 115138716337260521157904699)
      ·
        refine ⟨172708074505890781736857049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115138716337260521157904699 172708074505890781736857049)
        ·
          refine ⟨129531055879418086302642787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172708074505890781736857049 129531055879418086302642787)
          ·
            refine ⟨194296583819127129453964181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129531055879418086302642787 194296583819127129453964181)
            ·
              refine ⟨9107652366521584193154571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 194296583819127129453964181 9107652366521584193154571)
              ·
                refine ⟨13661478549782376289731857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9107652366521584193154571 13661478549782376289731857)
                ·
                  refine ⟨10246108912336782217298893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13661478549782376289731857 10246108912336782217298893)
                  ·
                    refine ⟨3842290842126293331487085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10246108912336782217298893 3842290842126293331487085)
                    ·
                      refine ⟨1440859065797359999307657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3842290842126293331487085 1440859065797359999307657)
                      ·
                        rfl

theorem cell23_2806063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 3].length) (baseStart_2806063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806063 prefixEnd_2806063 := by exact prefixLift 2806063
  have htrace : WordTrace (prefixWord ++ tailWord_2806063) baseStart_2806063 baseEnd_2806063 := by
    simpa [prefixWord, tailWord_2806063, baseEnd_2806063] using wordTrace_append hprefix tailTrace_2806063
  have hstable : (prefixWord ++ tailWord_2806063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806063).length < 2 ^ (prefixWord ++ tailWord_2806063).sum := by decide
  have hdescent : baseEnd_2806063 < baseStart_2806063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806100 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_2806100 : Nat := 118140960795 + 2806100 * 2 ^ 59
def prefixEnd_2806100 : Nat := 4983230072969 + 3 ^ 40 * 2806100 * 2
def baseEnd_2806100 : Nat := 480292688193858784848329

theorem tailTrace_2806100 : CollatzResearch.WordTrace tailWord_2806100 prefixEnd_2806100 480292688193858784848329 := by
  unfold tailWord_2806100
  simp only [CollatzResearch.WordTrace]
  refine ⟨51173437566993209285283877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68231250089324279047045169 51173437566993209285283877)
  ·
    refine ⟨9595019543811226740990727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51173437566993209285283877 9595019543811226740990727)
    ·
      refine ⟨14392529315716840111486091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9595019543811226740990727 14392529315716840111486091)
      ·
        refine ⟨21588793973575260167229137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14392529315716840111486091 21588793973575260167229137)
        ·
          refine ⟨16191595480181445125421853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21588793973575260167229137 16191595480181445125421853)
          ·
            refine ⟨6071848305068041922033195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16191595480181445125421853 6071848305068041922033195)
            ·
              refine ⟨9107772457602062883049793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6071848305068041922033195 9107772457602062883049793)
              ·
                refine ⟨6830829343201547162287345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9107772457602062883049793 6830829343201547162287345)
                ·
                  refine ⟨5123122007401160371715509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6830829343201547162287345 5123122007401160371715509)
                  ·
                    refine ⟨480292688193858784848329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5123122007401160371715509 480292688193858784848329)
                    ·
                      rfl

theorem cell23_2806100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_2806100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806100 prefixEnd_2806100 := by exact prefixLift 2806100
  have htrace : WordTrace (prefixWord ++ tailWord_2806100) baseStart_2806100 baseEnd_2806100 := by
    simpa [prefixWord, tailWord_2806100, baseEnd_2806100] using wordTrace_append hprefix tailTrace_2806100
  have hstable : (prefixWord ++ tailWord_2806100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806100).length < 2 ^ (prefixWord ++ tailWord_2806100).sum := by decide
  have hdescent : baseEnd_2806100 < baseStart_2806100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806134 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_2806134 : Nat := 118140960795 + 2806134 * 2 ^ 59
def prefixEnd_2806134 : Nat := 4983230072969 + 3 ^ 40 * 2806134 * 2
def baseEnd_2806134 : Nat := 480298507641276407173277

theorem tailTrace_2806134 : CollatzResearch.WordTrace tailWord_2806134 prefixEnd_2806134 480298507641276407173277 := by
  unfold tailWord_2806134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6396757200991452648581591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68232076810575494918203637 6396757200991452648581591)
  ·
    refine ⟨9595135801487178972872387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6396757200991452648581591 9595135801487178972872387)
    ·
      refine ⟨14392703702230768459308581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9595135801487178972872387 14392703702230768459308581)
      ·
        refine ⟨2698631944168269086120359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14392703702230768459308581 2698631944168269086120359)
        ·
          refine ⟨4047947916252403629180539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2698631944168269086120359 4047947916252403629180539)
          ·
            refine ⟨6071921874378605443770809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4047947916252403629180539 6071921874378605443770809)
            ·
              refine ⟨4553941405783954082828107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6071921874378605443770809 4553941405783954082828107)
              ·
                refine ⟨6830912108675931124242161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4553941405783954082828107 6830912108675931124242161)
                ·
                  refine ⟨5123184081506948343181621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6830912108675931124242161 5123184081506948343181621)
                  ·
                    refine ⟨480298507641276407173277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5123184081506948343181621 480298507641276407173277)
                    ·
                      rfl

theorem cell23_2806134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_2806134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806134 prefixEnd_2806134 := by exact prefixLift 2806134
  have htrace : WordTrace (prefixWord ++ tailWord_2806134) baseStart_2806134 baseEnd_2806134 := by
    simpa [prefixWord, tailWord_2806134, baseEnd_2806134] using wordTrace_append hprefix tailTrace_2806134
  have hstable : (prefixWord ++ tailWord_2806134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806134).length < 2 ^ (prefixWord ++ tailWord_2806134).sum := by decide
  have hdescent : baseEnd_2806134 < baseStart_2806134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806213 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 7, 1, 5]
def baseStart_2806213 : Nat := 118140960795 + 2806213 * 2 ^ 59
def prefixEnd_2806213 : Nat := 4983230072969 + 3 ^ 40 * 2806213 * 2
def baseEnd_2806213 : Nat := 1440936087895534412431967

theorem tailTrace_2806213 : CollatzResearch.WordTrace tailWord_2806213 prefixEnd_2806213 1440936087895534412431967 := by
  unfold tailWord_2806213
  simp only [CollatzResearch.WordTrace]
  refine ⟨102350996582577038869431293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68233997721718025912954195 102350996582577038869431293)
  ·
    refine ⟨38381623718466389576036735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102350996582577038869431293 38381623718466389576036735)
    ·
      refine ⟨57572435577699584364055103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38381623718466389576036735 57572435577699584364055103)
      ·
        refine ⟨86358653366549376546082655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57572435577699584364055103 86358653366549376546082655)
        ·
          refine ⟨129537980049824064819123983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86358653366549376546082655 129537980049824064819123983)
          ·
            refine ⟨194306970074736097228685975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129537980049824064819123983 194306970074736097228685975)
            ·
              refine ⟨291460455112104145843028963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194306970074736097228685975 291460455112104145843028963)
              ·
                refine ⟨437190682668156218764543445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291460455112104145843028963 437190682668156218764543445)
                ·
                  refine ⟨10246656625034911377293987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 437190682668156218764543445 10246656625034911377293987)
                  ·
                    refine ⟨15369984937552367065940981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10246656625034911377293987 15369984937552367065940981)
                    ·
                      refine ⟨1440936087895534412431967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15369984937552367065940981 1440936087895534412431967)
                      ·
                        rfl

theorem cell23_2806213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_2806213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806213 prefixEnd_2806213 := by exact prefixLift 2806213
  have htrace : WordTrace (prefixWord ++ tailWord_2806213) baseStart_2806213 baseEnd_2806213 := by
    simpa [prefixWord, tailWord_2806213, baseEnd_2806213] using wordTrace_append hprefix tailTrace_2806213
  have hstable : (prefixWord ++ tailWord_2806213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806213).length < 2 ^ (prefixWord ++ tailWord_2806213).sum := by decide
  have hdescent : baseEnd_2806213 < baseStart_2806213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806223 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 6]
def baseStart_2806223 : Nat := 118140960795 + 2806223 * 2 ^ 59
def prefixEnd_2806223 : Nat := 4983230072969 + 3 ^ 40 * 2806223 * 2
def baseEnd_2806223 : Nat := 1440941222702079373306921

theorem tailTrace_2806223 : CollatzResearch.WordTrace tailWord_2806223 prefixEnd_2806223 1440941222702079373306921 := by
  unfold tailWord_2806223
  simp only [CollatzResearch.WordTrace]
  refine ⟨102351361312540810577295323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68234240875027207051530215 102351361312540810577295323)
  ·
    refine ⟨153527041968811215865942985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102351361312540810577295323 153527041968811215865942985)
    ·
      refine ⟨115145281476608411899457239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153527041968811215865942985 115145281476608411899457239)
      ·
        refine ⟨172717922214912617849185859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115145281476608411899457239 172717922214912617849185859)
        ·
          refine ⟨259076883322368926773778789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172717922214912617849185859 259076883322368926773778789)
          ·
            refine ⟨48576915622944173770083523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 259076883322368926773778789 48576915622944173770083523)
            ·
              refine ⟨72865373434416260655125285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48576915622944173770083523 72865373434416260655125285)
              ·
                refine ⟨13662257518953048872835991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72865373434416260655125285 13662257518953048872835991)
                ·
                  refine ⟨20493386278429573309253987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13662257518953048872835991 20493386278429573309253987)
                  ·
                    refine ⟨30740079417644359963880981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20493386278429573309253987 30740079417644359963880981)
                    ·
                      refine ⟨1440941222702079373306921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30740079417644359963880981 1440941222702079373306921)
                      ·
                        rfl

theorem cell23_2806223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_2806223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806223 prefixEnd_2806223 := by exact prefixLift 2806223
  have htrace : WordTrace (prefixWord ++ tailWord_2806223) baseStart_2806223 baseEnd_2806223 := by
    simpa [prefixWord, tailWord_2806223, baseEnd_2806223] using wordTrace_append hprefix tailTrace_2806223
  have hstable : (prefixWord ++ tailWord_2806223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806223).length < 2 ^ (prefixWord ++ tailWord_2806223).sum := by decide
  have hdescent : baseEnd_2806223 < baseStart_2806223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806233 : List Nat := [1, 2, 1, 2, 4, 1, 2, 10]
def baseStart_2806233 : Nat := 118140960795 + 2806233 * 2 ^ 59
def prefixEnd_2806233 : Nat := 4983230072969 + 3 ^ 40 * 2806233 * 2
def baseEnd_2806233 : Nat := 53368383611430530895625

theorem tailTrace_2806233 : CollatzResearch.WordTrace tailWord_2806233 prefixEnd_2806233 53368383611430530895625 := by
  unfold tailWord_2806233
  simp only [CollatzResearch.WordTrace]
  refine ⟨102351726042504582285159353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68234484028336388190106235 102351726042504582285159353)
  ·
    refine ⟨76763794531878436713869515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102351726042504582285159353 76763794531878436713869515)
    ·
      refine ⟨115145691797817655070804273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76763794531878436713869515 115145691797817655070804273)
      ·
        refine ⟨86359268848363241303103205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115145691797817655070804273 86359268848363241303103205)
        ·
          refine ⟨16192362909068107744331851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86359268848363241303103205 16192362909068107744331851)
          ·
            refine ⟨24288544363602161616497777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16192362909068107744331851 24288544363602161616497777)
            ·
              refine ⟨18216408272701621212373333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24288544363602161616497777 18216408272701621212373333)
              ·
                refine ⟨53368383611430530895625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18216408272701621212373333 53368383611430530895625)
                ·
                  rfl

theorem cell23_2806233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 10].length) (baseStart_2806233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806233 prefixEnd_2806233 := by exact prefixLift 2806233
  have htrace : WordTrace (prefixWord ++ tailWord_2806233) baseStart_2806233 baseEnd_2806233 := by
    simpa [prefixWord, tailWord_2806233, baseEnd_2806233] using wordTrace_append hprefix tailTrace_2806233
  have hstable : (prefixWord ++ tailWord_2806233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806233).length < 2 ^ (prefixWord ++ tailWord_2806233).sum := by decide
  have hdescent : baseEnd_2806233 < baseStart_2806233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806250 : List Nat := [3, 1, 3, 1, 3, 2, 1, 9]
def baseStart_2806250 : Nat := 118140960795 + 2806250 * 2 ^ 59
def prefixEnd_2806250 : Nat := 4983230072969 + 3 ^ 40 * 2806250 * 2
def baseEnd_2806250 : Nat := 53368706914064843247011

theorem tailTrace_2806250 : CollatzResearch.WordTrace tailWord_2806250 prefixEnd_2806250 53368706914064843247011 := by
  unfold tailWord_2806250
  simp only [CollatzResearch.WordTrace]
  refine ⟨25588086520860748547132051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68234897388961996125685469 25588086520860748547132051)
  ·
    refine ⟨38382129781291122820698077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25588086520860748547132051 38382129781291122820698077)
    ·
      refine ⟨14393298667984171057761779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38382129781291122820698077 14393298667984171057761779)
      ·
        refine ⟨21589948001976256586642669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14393298667984171057761779 21589948001976256586642669)
        ·
          refine ⟨8096230500741096219991001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21589948001976256586642669 8096230500741096219991001)
          ·
            refine ⟨6072172875555822164993251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8096230500741096219991001 6072172875555822164993251)
            ·
              refine ⟨9108259313333733247489877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6072172875555822164993251 9108259313333733247489877)
              ·
                refine ⟨53368706914064843247011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9108259313333733247489877 53368706914064843247011)
                ·
                  rfl

theorem cell23_2806250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 9].length) (baseStart_2806250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806250 prefixEnd_2806250 := by exact prefixLift 2806250
  have htrace : WordTrace (prefixWord ++ tailWord_2806250) baseStart_2806250 baseEnd_2806250 := by
    simpa [prefixWord, tailWord_2806250, baseEnd_2806250] using wordTrace_append hprefix tailTrace_2806250
  have hstable : (prefixWord ++ tailWord_2806250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806250).length < 2 ^ (prefixWord ++ tailWord_2806250).sum := by decide
  have hdescent : baseEnd_2806250 < baseStart_2806250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806277 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 4, 1, 3]
def baseStart_2806277 : Nat := 118140960795 + 2806277 * 2 ^ 59
def prefixEnd_2806277 : Nat := 4983230072969 + 3 ^ 40 * 2806277 * 2
def baseEnd_2806277 : Nat := 1440968950657422162031673

theorem tailTrace_2806277 : CollatzResearch.WordTrace tailWord_2806277 prefixEnd_2806277 1440968950657422162031673 := by
  unfold tailWord_2806277
  simp only [CollatzResearch.WordTrace]
  refine ⟨102353330854345177799761085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68235553902896785199840723 102353330854345177799761085)
  ·
    refine ⟨38382499070379441674910407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102353330854345177799761085 38382499070379441674910407)
    ·
      refine ⟨57573748605569162512365611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38382499070379441674910407 57573748605569162512365611)
      ·
        refine ⟨86360622908353743768548417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57573748605569162512365611 86360622908353743768548417)
        ·
          refine ⟨64770467181265307826411313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86360622908353743768548417 64770467181265307826411313)
          ·
            refine ⟨48577850385948980869808485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64770467181265307826411313 48577850385948980869808485)
            ·
              refine ⟨9108346947365433913089091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48577850385948980869808485 9108346947365433913089091)
              ·
                refine ⟨13662520421048150869633637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9108346947365433913089091 13662520421048150869633637)
                ·
                  refine ⟨2561722578946528288056307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13662520421048150869633637 2561722578946528288056307)
                  ·
                    refine ⟨3842583868419792432084461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2561722578946528288056307 3842583868419792432084461)
                    ·
                      refine ⟨1440968950657422162031673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3842583868419792432084461 1440968950657422162031673)
                      ·
                        rfl

theorem cell23_2806277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_2806277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806277 prefixEnd_2806277 := by exact prefixLift 2806277
  have htrace : WordTrace (prefixWord ++ tailWord_2806277) baseStart_2806277 baseEnd_2806277 := by
    simpa [prefixWord, tailWord_2806277, baseEnd_2806277] using wordTrace_append hprefix tailTrace_2806277
  have hstable : (prefixWord ++ tailWord_2806277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806277).length < 2 ^ (prefixWord ++ tailWord_2806277).sum := by decide
  have hdescent : baseEnd_2806277 < baseStart_2806277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806311 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2806311 : Nat := 118140960795 + 2806311 * 2 ^ 59
def prefixEnd_2806311 : Nat := 4983230072969 + 3 ^ 40 * 2806311 * 2
def baseEnd_2806311 : Nat := 1440986408999675029006517

theorem tailTrace_2806311 : CollatzResearch.WordTrace tailWord_2806311 prefixEnd_2806311 1440986408999675029006517 := by
  unfold tailWord_2806311
  simp only [CollatzResearch.WordTrace]
  refine ⟨102354570936222001606498787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68236380624148001070999191 102354570936222001606498787)
  ·
    refine ⟨153531856404333002409748181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102354570936222001606498787 153531856404333002409748181)
    ·
      refine ⟨3598402884476554743978473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 153531856404333002409748181 3598402884476554743978473)
      ·
        refine ⟨2698802163357416057983855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3598402884476554743978473 2698802163357416057983855)
        ·
          refine ⟨4048203245036124086975783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2698802163357416057983855 4048203245036124086975783)
          ·
            refine ⟨6072304867554186130463675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4048203245036124086975783 6072304867554186130463675)
            ·
              refine ⟨9108457301331279195695513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6072304867554186130463675 9108457301331279195695513)
              ·
                refine ⟨6831342975998459396771635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9108457301331279195695513 6831342975998459396771635)
                ·
                  refine ⟨10247014463997689095157453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6831342975998459396771635 10247014463997689095157453)
                  ·
                    refine ⟨3842630423999133410684045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10247014463997689095157453 3842630423999133410684045)
                    ·
                      refine ⟨1440986408999675029006517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3842630423999133410684045 1440986408999675029006517)
                      ·
                        rfl

theorem cell23_2806311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2806311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806311 prefixEnd_2806311 := by exact prefixLift 2806311
  have htrace : WordTrace (prefixWord ++ tailWord_2806311) baseStart_2806311 baseEnd_2806311 := by
    simpa [prefixWord, tailWord_2806311, baseEnd_2806311] using wordTrace_append hprefix tailTrace_2806311
  have hstable : (prefixWord ++ tailWord_2806311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806311).length < 2 ^ (prefixWord ++ tailWord_2806311).sum := by decide
  have hdescent : baseEnd_2806311 < baseStart_2806311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806320 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 5]
def baseStart_2806320 : Nat := 118140960795 + 2806320 * 2 ^ 59
def prefixEnd_2806320 : Nat := 4983230072969 + 3 ^ 40 * 2806320 * 2
def baseEnd_2806320 : Nat := 1440991030325565493793975

theorem tailTrace_2806320 : CollatzResearch.WordTrace tailWord_2806320 prefixEnd_2806320 1440991030325565493793975 := by
  unfold tailWord_2806320
  simp only [CollatzResearch.WordTrace]
  refine ⟨51177449596594698071788207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68236599462126264095717609 51177449596594698071788207)
  ·
    refine ⟨76766174394892047107682311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51177449596594698071788207 76766174394892047107682311)
    ·
      refine ⟨115149261592338070661523467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76766174394892047107682311 115149261592338070661523467)
      ·
        refine ⟨172723892388507105992285201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115149261592338070661523467 172723892388507105992285201)
        ·
          refine ⟨129542919291380329494213901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172723892388507105992285201 129542919291380329494213901)
          ·
            refine ⟨48578594734267623560330213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129542919291380329494213901 48578594734267623560330213)
            ·
              refine ⟨9108486512675179417561915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48578594734267623560330213 9108486512675179417561915)
              ·
                refine ⟨13662729769012769126342873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9108486512675179417561915 13662729769012769126342873)
                ·
                  refine ⟨10247047326759576844757155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13662729769012769126342873 10247047326759576844757155)
                  ·
                    refine ⟨15370570990139365267135733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10247047326759576844757155 15370570990139365267135733)
                    ·
                      refine ⟨1440991030325565493793975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15370570990139365267135733 1440991030325565493793975)
                      ·
                        rfl

theorem cell23_2806320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_2806320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806320 prefixEnd_2806320 := by exact prefixLift 2806320
  have htrace : WordTrace (prefixWord ++ tailWord_2806320) baseStart_2806320 baseEnd_2806320 := by
    simpa [prefixWord, tailWord_2806320, baseEnd_2806320] using wordTrace_append hprefix tailTrace_2806320
  have hstable : (prefixWord ++ tailWord_2806320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806320).length < 2 ^ (prefixWord ++ tailWord_2806320).sum := by decide
  have hdescent : baseEnd_2806320 < baseStart_2806320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806337 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_2806337 : Nat := 118140960795 + 2806337 * 2 ^ 59
def prefixEnd_2806337 : Nat := 4983230072969 + 3 ^ 40 * 2806337 * 2
def baseEnd_2806337 : Nat := 1440999759496691927281397

theorem tailTrace_2806337 : CollatzResearch.WordTrace tailWord_2806337 prefixEnd_2806337 1440999759496691927281397 := by
  unfold tailWord_2806337
  simp only [CollatzResearch.WordTrace]
  refine ⟨102355519234127808046945265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68237012822751872031296843 102355519234127808046945265)
  ·
    refine ⟨76766639425595856035208949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102355519234127808046945265 76766639425595856035208949)
    ·
      refine ⟨7196872446149611503300839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76766639425595856035208949 7196872446149611503300839)
      ·
        refine ⟨10795308669224417254951259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7196872446149611503300839 10795308669224417254951259)
        ·
          refine ⟨16192963003836625882426889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10795308669224417254951259 16192963003836625882426889)
          ·
            refine ⟨12144722252877469411820167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16192963003836625882426889 12144722252877469411820167)
            ·
              refine ⟨18217083379316204117730251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12144722252877469411820167 18217083379316204117730251)
              ·
                refine ⟨27325625068974306176595377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18217083379316204117730251 27325625068974306176595377)
                ·
                  refine ⟨20494218801730729632446533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27325625068974306176595377 20494218801730729632446533)
                  ·
                    refine ⟨3842666025324511806083725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20494218801730729632446533 3842666025324511806083725)
                    ·
                      refine ⟨1440999759496691927281397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3842666025324511806083725 1440999759496691927281397)
                      ·
                        rfl

theorem cell23_2806337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_2806337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806337 prefixEnd_2806337 := by exact prefixLift 2806337
  have htrace : WordTrace (prefixWord ++ tailWord_2806337) baseStart_2806337 baseEnd_2806337 := by
    simpa [prefixWord, tailWord_2806337, baseEnd_2806337] using wordTrace_append hprefix tailTrace_2806337
  have hstable : (prefixWord ++ tailWord_2806337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806337).length < 2 ^ (prefixWord ++ tailWord_2806337).sum := by decide
  have hdescent : baseEnd_2806337 < baseStart_2806337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806380 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 5]
def baseStart_2806380 : Nat := 118140960795 + 2806380 * 2 ^ 59
def prefixEnd_2806380 : Nat := 4983230072969 + 3 ^ 40 * 2806380 * 2
def baseEnd_2806380 : Nat := 1441021839164835259043699

theorem tailTrace_2806380 : CollatzResearch.WordTrace tailWord_2806380 prefixEnd_2806380 1441021839164835259043699 := by
  unfold tailWord_2806380
  simp only [CollatzResearch.WordTrace]
  refine ⟨51178543786486013195380297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68238058381981350927173729 51178543786486013195380297)
  ·
    refine ⟨38383907839864509896535223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51178543786486013195380297 38383907839864509896535223)
    ·
      refine ⟨57575861759796764844802835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38383907839864509896535223 57575861759796764844802835)
      ·
        refine ⟨86363792639695147267204253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57575861759796764844802835 86363792639695147267204253)
        ·
          refine ⟨32386422239885680225201595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86363792639695147267204253 32386422239885680225201595)
          ·
            refine ⟨48579633359828520337802393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32386422239885680225201595 48579633359828520337802393)
            ·
              refine ⟨36434725019871390253351795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48579633359828520337802393 36434725019871390253351795)
              ·
                refine ⟨54652087529807085380027693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36434725019871390253351795 54652087529807085380027693)
                ·
                  refine ⟨20494532823677657017510385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54652087529807085380027693 20494532823677657017510385)
                  ·
                    refine ⟨15370899617758242763132789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20494532823677657017510385 15370899617758242763132789)
                    ·
                      refine ⟨1441021839164835259043699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15370899617758242763132789 1441021839164835259043699)
                      ·
                        rfl

theorem cell23_2806380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_2806380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806380 prefixEnd_2806380 := by exact prefixLift 2806380
  have htrace : WordTrace (prefixWord ++ tailWord_2806380) baseStart_2806380 baseEnd_2806380 := by
    simpa [prefixWord, tailWord_2806380, baseEnd_2806380] using wordTrace_append hprefix tailTrace_2806380
  have hstable : (prefixWord ++ tailWord_2806380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806380).length < 2 ^ (prefixWord ++ tailWord_2806380).sum := by decide
  have hdescent : baseEnd_2806380 < baseStart_2806380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806402 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_2806402 : Nat := 118140960795 + 2806402 * 2 ^ 59
def prefixEnd_2806402 : Nat := 4983230072969 + 3 ^ 40 * 2806402 * 2
def baseEnd_2806402 : Nat := 1441033135739234172968599

theorem tailTrace_2806402 : CollatzResearch.WordTrace tailWord_2806402 prefixEnd_2806402 1441033135739234172968599 := by
  unfold tailWord_2806402
  simp only [CollatzResearch.WordTrace]
  refine ⟨25589472494723081037015365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68238593319261549432040973 25589472494723081037015365)
  ·
    refine ⟨4798026092760577694440381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25589472494723081037015365 4798026092760577694440381)
    ·
      refine ⟨1799259784785216635415143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4798026092760577694440381 1799259784785216635415143)
      ·
        refine ⟨2698889677177824953122715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1799259784785216635415143 2698889677177824953122715)
        ·
          refine ⟨4048334515766737429684073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2698889677177824953122715 4048334515766737429684073)
          ·
            refine ⟨3036250886825053072263055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4048334515766737429684073 3036250886825053072263055)
            ·
              refine ⟨4554376330237579608394583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3036250886825053072263055 4554376330237579608394583)
              ·
                refine ⟨6831564495356369412591875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4554376330237579608394583 6831564495356369412591875)
                ·
                  refine ⟨10247346743034554118887813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6831564495356369412591875 10247346743034554118887813)
                  ·
                    refine ⟨1921377514318978897291465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10247346743034554118887813 1921377514318978897291465)
                    ·
                      refine ⟨1441033135739234172968599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1921377514318978897291465 1441033135739234172968599)
                      ·
                        rfl

theorem cell23_2806402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_2806402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806402 prefixEnd_2806402 := by exact prefixLift 2806402
  have htrace : WordTrace (prefixWord ++ tailWord_2806402) baseStart_2806402 baseEnd_2806402 := by
    simpa [prefixWord, tailWord_2806402, baseEnd_2806402] using wordTrace_append hprefix tailTrace_2806402
  have hstable : (prefixWord ++ tailWord_2806402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806402).length < 2 ^ (prefixWord ++ tailWord_2806402).sum := by decide
  have hdescent : baseEnd_2806402 < baseStart_2806402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806464 : List Nat := [2, 1, 1, 2, 4, 2, 4, 1, 6]
def baseStart_2806464 : Nat := 118140960795 + 2806464 * 2 ^ 59
def prefixEnd_2806464 : Nat := 4983230072969 + 3 ^ 40 * 2806464 * 2
def baseEnd_2806464 : Nat := 160118330171090325599257

theorem tailTrace_2806464 : CollatzResearch.WordTrace tailWord_2806464 prefixEnd_2806464 160118330171090325599257 := by
  unfold tailWord_2806464
  simp only [CollatzResearch.WordTrace]
  refine ⟨51180075652333854368409223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68240100869778472491212297 51180075652333854368409223)
  ·
    refine ⟨76770113478500781552613835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51180075652333854368409223 76770113478500781552613835)
    ·
      refine ⟨115155170217751172328920753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76770113478500781552613835 115155170217751172328920753)
      ·
        refine ⟨86366377663313379246690565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115155170217751172328920753 86366377663313379246690565)
        ·
          refine ⟨16193695811871258608754481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86366377663313379246690565 16193695811871258608754481)
          ·
            refine ⟨12145271858903443956565861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16193695811871258608754481 12145271858903443956565861)
            ·
              refine ⟨2277238473544395741856099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12145271858903443956565861 2277238473544395741856099)
              ·
                refine ⟨3415857710316593612784149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2277238473544395741856099 3415857710316593612784149)
                ·
                  refine ⟨160118330171090325599257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3415857710316593612784149 160118330171090325599257)
                  ·
                    rfl

theorem cell23_2806464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 6].length) (baseStart_2806464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806464 prefixEnd_2806464 := by exact prefixLift 2806464
  have htrace : WordTrace (prefixWord ++ tailWord_2806464) baseStart_2806464 baseEnd_2806464 := by
    simpa [prefixWord, tailWord_2806464, baseEnd_2806464] using wordTrace_append hprefix tailTrace_2806464
  have hstable : (prefixWord ++ tailWord_2806464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806464).length < 2 ^ (prefixWord ++ tailWord_2806464).sum := by decide
  have hdescent : baseEnd_2806464 < baseStart_2806464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806501 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 2, 3, 2]
def baseStart_2806501 : Nat := 118140960795 + 2806501 * 2 ^ 59
def prefixEnd_2806501 : Nat := 4983230072969 + 3 ^ 40 * 2806501 * 2
def baseEnd_2806501 : Nat := 1441083970324029285630643

theorem tailTrace_2806501 : CollatzResearch.WordTrace tailWord_2806501 prefixEnd_2806501 1441083970324029285630643 := by
  unfold tailWord_2806501
  simp only [CollatzResearch.WordTrace]
  refine ⟨102361500805533664055915357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68241000537022442703943571 102361500805533664055915357)
  ·
    refine ⟨38385562802075124020968259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102361500805533664055915357 38385562802075124020968259)
    ·
      refine ⟨57578344203112686031452389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38385562802075124020968259 57578344203112686031452389)
      ·
        refine ⟨10795939538083628630897323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57578344203112686031452389 10795939538083628630897323)
        ·
          refine ⟨16193909307125442946345985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10795939538083628630897323 16193909307125442946345985)
          ·
            refine ⟨12145431980344082209759489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16193909307125442946345985 12145431980344082209759489)
            ·
              refine ⟨9109073985258061657319617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12145431980344082209759489 9109073985258061657319617)
              ·
                refine ⟨6831805488943546242989713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9109073985258061657319617 6831805488943546242989713)
                ·
                  refine ⟨5123854116707659682242285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6831805488943546242989713 5123854116707659682242285)
                  ·
                    refine ⟨1921445293765372380840857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5123854116707659682242285 1921445293765372380840857)
                    ·
                      refine ⟨1441083970324029285630643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1921445293765372380840857 1441083970324029285630643)
                      ·
                        rfl

theorem cell23_2806501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_2806501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806501 prefixEnd_2806501 := by exact prefixLift 2806501
  have htrace : WordTrace (prefixWord ++ tailWord_2806501) baseStart_2806501 baseEnd_2806501 := by
    simpa [prefixWord, tailWord_2806501, baseEnd_2806501] using wordTrace_append hprefix tailTrace_2806501
  have hstable : (prefixWord ++ tailWord_2806501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806501).length < 2 ^ (prefixWord ++ tailWord_2806501).sum := by decide
  have hdescent : baseEnd_2806501 < baseStart_2806501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806514 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_2806514 : Nat := 118140960795 + 2806514 * 2 ^ 59
def prefixEnd_2806514 : Nat := 4983230072969 + 3 ^ 40 * 2806514 * 2
def baseEnd_2806514 : Nat := 1441090645572537734768083

theorem tailTrace_2806514 : CollatzResearch.WordTrace tailWord_2806514 prefixEnd_2806514 1441090645572537734768083 := by
  unfold tailWord_2806514
  simp only [CollatzResearch.WordTrace]
  refine ⟨25590493738621641819034649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68241316636324378184092397 25590493738621641819034649)
  ·
    refine ⟨19192870303966231364275987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25590493738621641819034649 19192870303966231364275987)
    ·
      refine ⟨28789305455949347046413981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19192870303966231364275987 28789305455949347046413981)
      ·
        refine ⟨10795989545981005142405243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28789305455949347046413981 10795989545981005142405243)
        ·
          refine ⟨16193984318971507713607865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10795989545981005142405243 16193984318971507713607865)
          ·
            refine ⟨12145488239228630785205899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16193984318971507713607865 12145488239228630785205899)
            ·
              refine ⟨18218232358842946177808849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12145488239228630785205899 18218232358842946177808849)
              ·
                refine ⟨13663674269132209633356637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18218232358842946177808849 13663674269132209633356637)
                ·
                  refine ⟨5123877850924578612508739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13663674269132209633356637 5123877850924578612508739)
                  ·
                    refine ⟨7685816776386867918763109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5123877850924578612508739 7685816776386867918763109)
                    ·
                      refine ⟨1441090645572537734768083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7685816776386867918763109 1441090645572537734768083)
                      ·
                        rfl

theorem cell23_2806514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_2806514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806514 prefixEnd_2806514 := by exact prefixLift 2806514
  have htrace : WordTrace (prefixWord ++ tailWord_2806514) baseStart_2806514 baseEnd_2806514 := by
    simpa [prefixWord, tailWord_2806514, baseEnd_2806514] using wordTrace_append hprefix tailTrace_2806514
  have hstable : (prefixWord ++ tailWord_2806514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806514).length < 2 ^ (prefixWord ++ tailWord_2806514).sum := by decide
  have hdescent : baseEnd_2806514 < baseStart_2806514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806524 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 1, 6]
def baseStart_2806524 : Nat := 118140960795 + 2806524 * 2 ^ 59
def prefixEnd_2806524 : Nat := 4983230072969 + 3 ^ 40 * 2806524 * 2
def baseEnd_2806524 : Nat := 480365260126360898547679

theorem tailTrace_2806524 : CollatzResearch.WordTrace tailWord_2806524 prefixEnd_2806524 480365260126360898547679 := by
  unfold tailWord_2806524
  simp only [CollatzResearch.WordTrace]
  refine ⟨51181169842225169492001313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68241559789633559322668417 51181169842225169492001313)
  ·
    refine ⟨38385877381668877119000985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51181169842225169492001313 38385877381668877119000985)
    ·
      refine ⟨28789408036251657839250739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38385877381668877119000985 28789408036251657839250739)
      ·
        refine ⟨43184112054377486758876109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28789408036251657839250739 43184112054377486758876109)
        ·
          refine ⟨16194042020391557534578541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43184112054377486758876109 16194042020391557534578541)
          ·
            refine ⟨6072765757646834075466953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16194042020391557534578541 6072765757646834075466953)
            ·
              refine ⟨4554574318235125556600215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6072765757646834075466953 4554574318235125556600215)
              ·
                refine ⟨6831861477352688334900323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4554574318235125556600215 6831861477352688334900323)
                ·
                  refine ⟨10247792216029032502350485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6831861477352688334900323 10247792216029032502350485)
                  ·
                    refine ⟨480365260126360898547679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10247792216029032502350485 480365260126360898547679)
                    ·
                      rfl

theorem cell23_2806524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_2806524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806524 prefixEnd_2806524 := by exact prefixLift 2806524
  have htrace : WordTrace (prefixWord ++ tailWord_2806524) baseStart_2806524 baseEnd_2806524 := by
    simpa [prefixWord, tailWord_2806524, baseEnd_2806524] using wordTrace_append hprefix tailTrace_2806524
  have hstable : (prefixWord ++ tailWord_2806524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806524).length < 2 ^ (prefixWord ++ tailWord_2806524).sum := by decide
  have hdescent : baseEnd_2806524 < baseStart_2806524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806581 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_2806581 : Nat := 118140960795 + 2806581 * 2 ^ 59
def prefixEnd_2806581 : Nat := 4983230072969 + 3 ^ 40 * 2806581 * 2
def baseEnd_2806581 : Nat := 1441125048776388972630275

theorem tailTrace_2806581 : CollatzResearch.WordTrace tailWord_2806581 prefixEnd_2806581 1441125048776388972630275 := by
  unfold tailWord_2806581
  simp only [CollatzResearch.WordTrace]
  refine ⟨102364418645243837718827597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68242945763495891812551731 102364418645243837718827597)
  ·
    refine ⟨38386656991966439144560349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102364418645243837718827597 38386656991966439144560349)
    ·
      refine ⟨14394996371987414679210131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38386656991966439144560349 14394996371987414679210131)
      ·
        refine ⟨21592494557981122018815197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14394996371987414679210131 21592494557981122018815197)
        ·
          refine ⟨8097185459242920757055699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21592494557981122018815197 8097185459242920757055699)
          ·
            refine ⟨12145778188864381135583549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8097185459242920757055699 12145778188864381135583549)
            ·
              refine ⟨4554666820824142925843831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12145778188864381135583549 4554666820824142925843831)
              ·
                refine ⟨6832000231236214388765747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4554666820824142925843831 6832000231236214388765747)
                ·
                  refine ⟨10248000346854321583148621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6832000231236214388765747 10248000346854321583148621)
                  ·
                    refine ⟨3843000130070370593680733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10248000346854321583148621 3843000130070370593680733)
                    ·
                      refine ⟨1441125048776388972630275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3843000130070370593680733 1441125048776388972630275)
                      ·
                        rfl

theorem cell23_2806581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_2806581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806581 prefixEnd_2806581 := by exact prefixLift 2806581
  have htrace : WordTrace (prefixWord ++ tailWord_2806581) baseStart_2806581 baseEnd_2806581 := by
    simpa [prefixWord, tailWord_2806581, baseEnd_2806581] using wordTrace_append hprefix tailTrace_2806581
  have hstable : (prefixWord ++ tailWord_2806581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806581).length < 2 ^ (prefixWord ++ tailWord_2806581).sum := by decide
  have hdescent : baseEnd_2806581 < baseStart_2806581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806597 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 4, 6]
def baseStart_2806597 : Nat := 118140960795 + 2806597 * 2 ^ 59
def prefixEnd_2806597 : Nat := 4983230072969 + 3 ^ 40 * 2806597 * 2
def baseEnd_2806597 : Nat := 480377754822286970010067

theorem tailTrace_2806597 : CollatzResearch.WordTrace tailWord_2806597 prefixEnd_2806597 480377754822286970010067 := by
  unfold tailWord_2806597
  simp only [CollatzResearch.WordTrace]
  refine ⟨102365002213185872451410045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68243334808790581634273363 102365002213185872451410045)
  ·
    refine ⟨38386875829944702169278767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102365002213185872451410045 38386875829944702169278767)
    ·
      refine ⟨57580313744917053253918151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38386875829944702169278767 57580313744917053253918151)
      ·
        refine ⟨86370470617375579880877227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57580313744917053253918151 86370470617375579880877227)
        ·
          refine ⟨129555705926063369821315841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86370470617375579880877227 129555705926063369821315841)
          ·
            refine ⟨97166779444547527365986881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129555705926063369821315841 97166779444547527365986881)
            ·
              refine ⟨72875084583410645524490161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97166779444547527365986881 72875084583410645524490161)
              ·
                refine ⟨54656313437557984143367621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72875084583410645524490161 54656313437557984143367621)
                ·
                  refine ⟨10248058769542122026881429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54656313437557984143367621 10248058769542122026881429)
                  ·
                    refine ⟨480377754822286970010067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10248058769542122026881429 480377754822286970010067)
                    ·
                      rfl

theorem cell23_2806597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_2806597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806597 prefixEnd_2806597 := by exact prefixLift 2806597
  have htrace : WordTrace (prefixWord ++ tailWord_2806597) baseStart_2806597 baseEnd_2806597 := by
    simpa [prefixWord, tailWord_2806597, baseEnd_2806597] using wordTrace_append hprefix tailTrace_2806597
  have hstable : (prefixWord ++ tailWord_2806597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806597).length < 2 ^ (prefixWord ++ tailWord_2806597).sum := by decide
  have hdescent : baseEnd_2806597 < baseStart_2806597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806624 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 3]
def baseStart_2806624 : Nat := 118140960795 + 2806624 * 2 ^ 59
def prefixEnd_2806624 : Nat := 4983230072969 + 3 ^ 40 * 2806624 * 2
def baseEnd_2806624 : Nat := 1441147128444532304392577

theorem tailTrace_2806624 : CollatzResearch.WordTrace tailWord_2806624 prefixEnd_2806624 1441147128444532304392577 := by
  unfold tailWord_2806624
  simp only [CollatzResearch.WordTrace]
  refine ⟨51182993492044028031321463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68243991322725370708428617 51182993492044028031321463)
  ·
    refine ⟨76774490238066042046982195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51182993492044028031321463 76774490238066042046982195)
    ·
      refine ⟨115161735357099063070473293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76774490238066042046982195 115161735357099063070473293)
      ·
        refine ⟨43185650758912148651427485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115161735357099063070473293 43185650758912148651427485)
        ·
          refine ⟨16194619034592055744285307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43185650758912148651427485 16194619034592055744285307)
          ·
            refine ⟨24291928551888083616427961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16194619034592055744285307 24291928551888083616427961)
            ·
              refine ⟨18218946413916062712320971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24291928551888083616427961 18218946413916062712320971)
              ·
                refine ⟨27328419620874094068481457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18218946413916062712320971 27328419620874094068481457)
                ·
                  refine ⟨20496314715655570551361093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27328419620874094068481457 20496314715655570551361093)
                  ·
                    refine ⟨3843059009185419478380205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20496314715655570551361093 3843059009185419478380205)
                    ·
                      refine ⟨1441147128444532304392577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3843059009185419478380205 1441147128444532304392577)
                      ·
                        rfl

theorem cell23_2806624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_2806624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806624 prefixEnd_2806624 := by exact prefixLift 2806624
  have htrace : WordTrace (prefixWord ++ tailWord_2806624) baseStart_2806624 baseEnd_2806624 := by
    simpa [prefixWord, tailWord_2806624, baseEnd_2806624] using wordTrace_append hprefix tailTrace_2806624
  have hstable : (prefixWord ++ tailWord_2806624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806624).length < 2 ^ (prefixWord ++ tailWord_2806624).sum := by decide
  have hdescent : baseEnd_2806624 < baseStart_2806624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806647 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 8]
def baseStart_2806647 : Nat := 118140960795 + 2806647 * 2 ^ 59
def prefixEnd_2806647 : Nat := 4983230072969 + 3 ^ 40 * 2806647 * 2
def baseEnd_2806647 : Nat := 1441158938499585714404971

theorem tailTrace_2806647 : CollatzResearch.WordTrace tailWord_2806647 prefixEnd_2806647 1441158938499585714404971 := by
  unfold tailWord_2806647
  simp only [CollatzResearch.WordTrace]
  refine ⟨102366825863004730990730195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68244550575336487327153463 102366825863004730990730195)
  ·
    refine ⟨153550238794507096486095293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102366825863004730990730195 153550238794507096486095293)
    ·
      refine ⟨57581339547940161182285735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153550238794507096486095293 57581339547940161182285735)
      ·
        refine ⟨86372009321910241773428603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57581339547940161182285735 86372009321910241773428603)
        ·
          refine ⟨129558013982865362660142905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86372009321910241773428603 129558013982865362660142905)
          ·
            refine ⟨97168510487149021995107179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129558013982865362660142905 97168510487149021995107179)
            ·
              refine ⟨145752765730723532992660769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97168510487149021995107179 145752765730723532992660769)
              ·
                refine ⟨109314574298042649744495577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145752765730723532992660769 109314574298042649744495577)
                ·
                  refine ⟨81985930723531987308371683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109314574298042649744495577 81985930723531987308371683)
                  ·
                    refine ⟨122978896085297980962557525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81985930723531987308371683 122978896085297980962557525)
                    ·
                      refine ⟨1441158938499585714404971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 122978896085297980962557525 1441158938499585714404971)
                      ·
                        rfl

theorem cell23_2806647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_2806647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806647 prefixEnd_2806647 := by exact prefixLift 2806647
  have htrace : WordTrace (prefixWord ++ tailWord_2806647) baseStart_2806647 baseEnd_2806647 := by
    simpa [prefixWord, tailWord_2806647, baseEnd_2806647] using wordTrace_append hprefix tailTrace_2806647
  have hstable : (prefixWord ++ tailWord_2806647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806647).length < 2 ^ (prefixWord ++ tailWord_2806647).sum := by decide
  have hdescent : baseEnd_2806647 < baseStart_2806647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806708 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_2806708 : Nat := 118140960795 + 2806708 * 2 ^ 59
def prefixEnd_2806708 : Nat := 4983230072969 + 3 ^ 40 * 2806708 * 2
def baseEnd_2806708 : Nat := 480396753606503325247397

theorem tailTrace_2806708 : CollatzResearch.WordTrace tailWord_2806708 prefixEnd_2806708 480396753606503325247397 := by
  unfold tailWord_2806708
  simp only [CollatzResearch.WordTrace]
  refine ⟨51184525357891869204350389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68246033810522492272467185 51184525357891869204350389)
  ·
    refine ⟨4798549252302362737907849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51184525357891869204350389 4798549252302362737907849)
    ·
      refine ⟨3598911939226772053430887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4798549252302362737907849 3598911939226772053430887)
      ·
        refine ⟨5398367908840158080146331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3598911939226772053430887 5398367908840158080146331)
        ·
          refine ⟨8097551863260237120219497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5398367908840158080146331 8097551863260237120219497)
          ·
            refine ⟨6073163897445177840164623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8097551863260237120219497 6073163897445177840164623)
            ·
              refine ⟨9109745846167766760246935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6073163897445177840164623 9109745846167766760246935)
              ·
                refine ⟨13664618769251650140370403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9109745846167766760246935 13664618769251650140370403)
                ·
                  refine ⟨20496928153877475210555605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13664618769251650140370403 20496928153877475210555605)
                  ·
                    refine ⟨480396753606503325247397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20496928153877475210555605 480396753606503325247397)
                    ·
                      rfl

theorem cell23_2806708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_2806708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806708 prefixEnd_2806708 := by exact prefixLift 2806708
  have htrace : WordTrace (prefixWord ++ tailWord_2806708) baseStart_2806708 baseEnd_2806708 := by
    simpa [prefixWord, tailWord_2806708, baseEnd_2806708] using wordTrace_append hprefix tailTrace_2806708
  have hstable : (prefixWord ++ tailWord_2806708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806708).length < 2 ^ (prefixWord ++ tailWord_2806708).sum := by decide
  have hdescent : baseEnd_2806708 < baseStart_2806708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806711 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 4]
def baseStart_2806711 : Nat := 118140960795 + 2806711 * 2 ^ 59
def prefixEnd_2806711 : Nat := 4983230072969 + 3 ^ 40 * 2806711 * 2
def baseEnd_2806711 : Nat := 1441191801261473464004677

theorem tailTrace_2806711 : CollatzResearch.WordTrace tailWord_2806711 prefixEnd_2806711 1441191801261473464004677 := by
  unfold tailWord_2806711
  simp only [CollatzResearch.WordTrace]
  refine ⟨102369160134772869921059987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68246106756515246614039991 102369160134772869921059987)
  ·
    refine ⟨153553740202159304881589981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102369160134772869921059987 153553740202159304881589981)
    ·
      refine ⟨57582652575809739330596243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153553740202159304881589981 57582652575809739330596243)
      ·
        refine ⟨86373978863714608995894365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57582652575809739330596243 86373978863714608995894365)
        ·
          refine ⟨32390242073892978373460387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86373978863714608995894365 32390242073892978373460387)
          ·
            refine ⟨48585363110839467560190581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32390242073892978373460387 48585363110839467560190581)
            ·
              refine ⟨4554877791641200083767867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48585363110839467560190581 4554877791641200083767867)
              ·
                refine ⟨6832316687461800125651801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4554877791641200083767867 6832316687461800125651801)
                ·
                  refine ⟨5124237515596350094238851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6832316687461800125651801 5124237515596350094238851)
                  ·
                    refine ⟨7686356273394525141358277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5124237515596350094238851 7686356273394525141358277)
                    ·
                      refine ⟨1441191801261473464004677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7686356273394525141358277 1441191801261473464004677)
                      ·
                        rfl

theorem cell23_2806711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_2806711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806711 prefixEnd_2806711 := by exact prefixLift 2806711
  have htrace : WordTrace (prefixWord ++ tailWord_2806711) baseStart_2806711 baseEnd_2806711 := by
    simpa [prefixWord, tailWord_2806711, baseEnd_2806711] using wordTrace_append hprefix tailTrace_2806711
  have hstable : (prefixWord ++ tailWord_2806711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806711).length < 2 ^ (prefixWord ++ tailWord_2806711).sum := by decide
  have hdescent : baseEnd_2806711 < baseStart_2806711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806738 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 3, 4]
def baseStart_2806738 : Nat := 118140960795 + 2806738 * 2 ^ 59
def prefixEnd_2806738 : Nat := 4983230072969 + 3 ^ 40 * 2806738 * 2
def baseEnd_2806738 : Nat := 480401888413048286122351

theorem tailTrace_2806738 : CollatzResearch.WordTrace tailWord_2806738 prefixEnd_2806738 480401888413048286122351 := by
  unfold tailWord_2806738
  simp only [CollatzResearch.WordTrace]
  refine ⟨25592536226418763383073217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68246763270450035688195245 25592536226418763383073217)
  ·
    refine ⟨19194402169814072537304913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25592536226418763383073217 19194402169814072537304913)
    ·
      refine ⟨14395801627360554402978685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19194402169814072537304913 14395801627360554402978685)
      ·
        refine ⟨5398425610260207901117007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14395801627360554402978685 5398425610260207901117007)
        ·
          refine ⟨8097638415390311851675511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5398425610260207901117007 8097638415390311851675511)
          ·
            refine ⟨12146457623085467777513267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8097638415390311851675511 12146457623085467777513267)
            ·
              refine ⟨18219686434628201666269901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12146457623085467777513267 18219686434628201666269901)
              ·
                refine ⟨6832382412985575624851213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18219686434628201666269901 6832382412985575624851213)
                ·
                  refine ⟨2562143404869590859319205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6832382412985575624851213 2562143404869590859319205)
                  ·
                    refine ⟨480401888413048286122351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2562143404869590859319205 480401888413048286122351)
                    ·
                      rfl

theorem cell23_2806738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_2806738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806738 prefixEnd_2806738 := by exact prefixLift 2806738
  have htrace : WordTrace (prefixWord ++ tailWord_2806738) baseStart_2806738 baseEnd_2806738 := by
    simpa [prefixWord, tailWord_2806738, baseEnd_2806738] using wordTrace_append hprefix tailTrace_2806738
  have hstable : (prefixWord ++ tailWord_2806738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806738).length < 2 ^ (prefixWord ++ tailWord_2806738).sum := by decide
  have hdescent : baseEnd_2806738 < baseStart_2806738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806784 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 4]
def baseStart_2806784 : Nat := 118140960795 + 2806784 * 2 ^ 59
def prefixEnd_2806784 : Nat := 4983230072969 + 3 ^ 40 * 2806784 * 2
def baseEnd_2806784 : Nat := 1441229285349251678391841

theorem tailTrace_2806784 : CollatzResearch.WordTrace tailWord_2806784 prefixEnd_2806784 1441229285349251678391841 := by
  unfold tailWord_2806784
  simp only [CollatzResearch.WordTrace]
  refine ⟨51185911331754201694233703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68247881775672268925644937 51185911331754201694233703)
  ·
    refine ⟨76778866997631302541350555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51185911331754201694233703 76778866997631302541350555)
    ·
      refine ⟨115168300496446953812025833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76778866997631302541350555 115168300496446953812025833)
      ·
        refine ⟨86376225372335215359019375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115168300496446953812025833 86376225372335215359019375)
        ·
          refine ⟨129564338058502823038529063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86376225372335215359019375 129564338058502823038529063)
          ·
            refine ⟨194346507087754234557793595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129564338058502823038529063 194346507087754234557793595)
            ·
              refine ⟨291519760631631351836690393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194346507087754234557793595 291519760631631351836690393)
              ·
                refine ⟨218639820473723513877517795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291519760631631351836690393 218639820473723513877517795)
                ·
                  refine ⟨327959730710585270816276693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218639820473723513877517795 327959730710585270816276693)
                  ·
                    refine ⟨7686556188529342284756485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 327959730710585270816276693 7686556188529342284756485)
                    ·
                      refine ⟨1441229285349251678391841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7686556188529342284756485 1441229285349251678391841)
                      ·
                        rfl

theorem cell23_2806784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_2806784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806784 prefixEnd_2806784 := by exact prefixLift 2806784
  have htrace : WordTrace (prefixWord ++ tailWord_2806784) baseStart_2806784 baseEnd_2806784 := by
    simpa [prefixWord, tailWord_2806784, baseEnd_2806784] using wordTrace_append hprefix tailTrace_2806784
  have hstable : (prefixWord ++ tailWord_2806784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806784).length < 2 ^ (prefixWord ++ tailWord_2806784).sum := by decide
  have hdescent : baseEnd_2806784 < baseStart_2806784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806795 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 3, 1, 3]
def baseStart_2806795 : Nat := 118140960795 + 2806795 * 2 ^ 59
def prefixEnd_2806795 : Nat := 4983230072969 + 3 ^ 40 * 2806795 * 2
def baseEnd_2806795 : Nat := 1441234933636451135354291

theorem tailTrace_2806795 : CollatzResearch.WordTrace tailWord_2806795 prefixEnd_2806795 1441234933636451135354291 := by
  unfold tailWord_2806795
  simp only [CollatzResearch.WordTrace]
  refine ⟨102372223866468552267117839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68248149244312368178078559 102372223866468552267117839)
  ·
    refine ⟨153558335799702828400676759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102372223866468552267117839 153558335799702828400676759)
    ·
      refine ⟨230337503699554242601015139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153558335799702828400676759 230337503699554242601015139)
      ·
        refine ⟨345506255549331363901522709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230337503699554242601015139 345506255549331363901522709)
        ·
          refine ⟨16195605728874907682883877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 345506255549331363901522709 16195605728874907682883877)
          ·
            refine ⟨3036676074164045190540727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16195605728874907682883877 3036676074164045190540727)
            ·
              refine ⟨4555014111246067785811091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3036676074164045190540727 4555014111246067785811091)
              ·
                refine ⟨6832521166869101678716637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555014111246067785811091 6832521166869101678716637)
                ·
                  refine ⟨2562195437575913129518739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6832521166869101678716637 2562195437575913129518739)
                  ·
                    refine ⟨3843293156363869694278109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2562195437575913129518739 3843293156363869694278109)
                    ·
                      refine ⟨1441234933636451135354291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3843293156363869694278109 1441234933636451135354291)
                      ·
                        rfl

theorem cell23_2806795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 1, 3].length) (baseStart_2806795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806795 prefixEnd_2806795 := by exact prefixLift 2806795
  have htrace : WordTrace (prefixWord ++ tailWord_2806795) baseStart_2806795 baseEnd_2806795 := by
    simpa [prefixWord, tailWord_2806795, baseEnd_2806795] using wordTrace_append hprefix tailTrace_2806795
  have hstable : (prefixWord ++ tailWord_2806795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806795).length < 2 ^ (prefixWord ++ tailWord_2806795).sum := by decide
  have hdescent : baseEnd_2806795 < baseStart_2806795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806802 : List Nat := [3, 2, 5, 1, 1, 1, 1, 3, 6]
def baseStart_2806802 : Nat := 118140960795 + 2806802 * 2 ^ 59
def prefixEnd_2806802 : Nat := 4983230072969 + 3 ^ 40 * 2806802 * 2
def baseEnd_2806802 : Nat := 160137614222336956440751

theorem tailTrace_2806802 : CollatzResearch.WordTrace tailWord_2806802 prefixEnd_2806802 160137614222336956440751 := by
  unfold tailWord_2806802
  simp only [CollatzResearch.WordTrace]
  refine ⟨25593119794360798115655665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68248319451628794975081773 25593119794360798115655665)
  ·
    refine ⟨19194839845770598586741749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25593119794360798115655665 19194839845770598586741749)
    ·
      refine ⟨1799516235540993617507039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19194839845770598586741749 1799516235540993617507039)
      ·
        refine ⟨2699274353311490426260559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1799516235540993617507039 2699274353311490426260559)
        ·
          refine ⟨4048911529967235639390839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2699274353311490426260559 4048911529967235639390839)
          ·
            refine ⟨6073367294950853459086259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4048911529967235639390839 6073367294950853459086259)
            ·
              refine ⟨9110050942426280188629389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6073367294950853459086259 9110050942426280188629389)
              ·
                refine ⟨3416269103409855070736021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9110050942426280188629389 3416269103409855070736021)
                ·
                  refine ⟨160137614222336956440751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3416269103409855070736021 160137614222336956440751)
                  ·
                    rfl

theorem cell23_2806802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_2806802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806802 prefixEnd_2806802 := by exact prefixLift 2806802
  have htrace : WordTrace (prefixWord ++ tailWord_2806802) baseStart_2806802 baseEnd_2806802 := by
    simpa [prefixWord, tailWord_2806802, baseEnd_2806802] using wordTrace_append hprefix tailTrace_2806802
  have hstable : (prefixWord ++ tailWord_2806802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806802).length < 2 ^ (prefixWord ++ tailWord_2806802).sum := by decide
  have hdescent : baseEnd_2806802 < baseStart_2806802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806818 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_2806818 : Nat := 118140960795 + 2806818 * 2 ^ 59
def prefixEnd_2806818 : Nat := 4983230072969 + 3 ^ 40 * 2806818 * 2
def baseEnd_2806818 : Nat := 1441246743691504545366685

theorem tailTrace_2806818 : CollatzResearch.WordTrace tailWord_2806818 prefixEnd_2806818 1441246743691504545366685 := by
  unfold tailWord_2806818
  simp only [CollatzResearch.WordTrace]
  refine ⟨25593265686346306798801277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68248708496923484796803405 25593265686346306798801277)
  ·
    refine ⟨9597474632379865049550479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25593265686346306798801277 9597474632379865049550479)
    ·
      refine ⟨14396211948569797574325719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9597474632379865049550479 14396211948569797574325719)
      ·
        refine ⟨21594317922854696361488579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14396211948569797574325719 21594317922854696361488579)
        ·
          refine ⟨32391476884282044542232869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21594317922854696361488579 32391476884282044542232869)
          ·
            refine ⟨6073401915802883351668663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32391476884282044542232869 6073401915802883351668663)
            ·
              refine ⟨9110102873704325027502995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6073401915802883351668663 9110102873704325027502995)
              ·
                refine ⟨13665154310556487541254493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9110102873704325027502995 13665154310556487541254493)
                ·
                  refine ⟨5124432866458682827970435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13665154310556487541254493 5124432866458682827970435)
                  ·
                    refine ⟨7686649299688024241955653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5124432866458682827970435 7686649299688024241955653)
                    ·
                      refine ⟨1441246743691504545366685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7686649299688024241955653 1441246743691504545366685)
                      ·
                        rfl

theorem cell23_2806818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_2806818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806818 prefixEnd_2806818 := by exact prefixLift 2806818
  have htrace : WordTrace (prefixWord ++ tailWord_2806818) baseStart_2806818 baseEnd_2806818 := by
    simpa [prefixWord, tailWord_2806818, baseEnd_2806818] using wordTrace_append hprefix tailTrace_2806818
  have hstable : (prefixWord ++ tailWord_2806818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806818).length < 2 ^ (prefixWord ++ tailWord_2806818).sum := by decide
  have hdescent : baseEnd_2806818 < baseStart_2806818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806845 : List Nat := [1, 4, 1, 3, 1, 3, 2, 2, 2, 4]
def baseStart_2806845 : Nat := 118140960795 + 2806845 * 2 ^ 59
def prefixEnd_2806845 : Nat := 4983230072969 + 3 ^ 40 * 2806845 * 2
def baseEnd_2806845 : Nat := 480420202556391979909687

theorem tailTrace_2806845 : CollatzResearch.WordTrace tailWord_2806845 prefixEnd_2806845 480420202556391979909687 := by
  unfold tailWord_2806845
  simp only [CollatzResearch.WordTrace]
  refine ⟨102374047516287410806437989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68249365010858273870958659 102374047516287410806437989)
  ·
    refine ⟨19195133909303889526207123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102374047516287410806437989 19195133909303889526207123)
    ·
      refine ⟨28792700863955834289310685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19195133909303889526207123 28792700863955834289310685)
      ·
        refine ⟨10797262823983437858491507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28792700863955834289310685 10797262823983437858491507)
        ·
          refine ⟨16195894235975156787737261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10797262823983437858491507 16195894235975156787737261)
          ·
            refine ⟨6073460338490683795401473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16195894235975156787737261 6073460338490683795401473)
            ·
              refine ⟨4555095253868012846551105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6073460338490683795401473 4555095253868012846551105)
              ·
                refine ⟨3416321440401009634913329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4555095253868012846551105 3416321440401009634913329)
                ·
                  refine ⟨2562241080300757226184997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3416321440401009634913329 2562241080300757226184997)
                  ·
                    refine ⟨480420202556391979909687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2562241080300757226184997 480420202556391979909687)
                    ·
                      rfl

theorem cell23_2806845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_2806845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806845 prefixEnd_2806845 := by exact prefixLift 2806845
  have htrace : WordTrace (prefixWord ++ tailWord_2806845) baseStart_2806845 baseEnd_2806845 := by
    simpa [prefixWord, tailWord_2806845, baseEnd_2806845] using wordTrace_append hprefix tailTrace_2806845
  have hstable : (prefixWord ++ tailWord_2806845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806845).length < 2 ^ (prefixWord ++ tailWord_2806845).sum := by decide
  have hdescent : baseEnd_2806845 < baseStart_2806845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806846 : List Nat := [4, 2, 1, 3, 1, 3, 2, 2, 1, 1, 3]
def baseStart_2806846 : Nat := 118140960795 + 2806846 * 2 ^ 59
def prefixEnd_2806846 : Nat := 4983230072969 + 3 ^ 40 * 2806846 * 2
def baseEnd_2806846 : Nat := 1441261121149830435816557

theorem tailTrace_2806846 : CollatzResearch.WordTrace tailWord_2806846 prefixEnd_2806846 1441261121149830435816557 := by
  unfold tailWord_2806846
  simp only [CollatzResearch.WordTrace]
  refine ⟨12796760498660473497153049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68249389326189191984816261 12796760498660473497153049)
  ·
    refine ⟨9597570373995355122864787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12796760498660473497153049 9597570373995355122864787)
    ·
      refine ⟨14396355560993032684297181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9597570373995355122864787 14396355560993032684297181)
      ·
        refine ⟨5398633335372387256611443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14396355560993032684297181 5398633335372387256611443)
        ·
          refine ⟨8097950003058580884917165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5398633335372387256611443 8097950003058580884917165)
          ·
            refine ⟨3036731251146967831843937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8097950003058580884917165 3036731251146967831843937)
            ·
              refine ⟨2277548438360225873882953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3036731251146967831843937 2277548438360225873882953)
              ·
                refine ⟨1708161328770169405412215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2277548438360225873882953 1708161328770169405412215)
                ·
                  refine ⟨2562241993155254108118323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1708161328770169405412215 2562241993155254108118323)
                  ·
                    refine ⟨3843362989732881162177485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2562241993155254108118323 3843362989732881162177485)
                    ·
                      refine ⟨1441261121149830435816557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3843362989732881162177485 1441261121149830435816557)
                      ·
                        rfl

theorem cell23_2806846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_2806846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806846 prefixEnd_2806846 := by exact prefixLift 2806846
  have htrace : WordTrace (prefixWord ++ tailWord_2806846) baseStart_2806846 baseEnd_2806846 := by
    simpa [prefixWord, tailWord_2806846, baseEnd_2806846] using wordTrace_append hprefix tailTrace_2806846
  have hstable : (prefixWord ++ tailWord_2806846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806846).length < 2 ^ (prefixWord ++ tailWord_2806846).sum := by decide
  have hdescent : baseEnd_2806846 < baseStart_2806846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806851 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 3]
def baseStart_2806851 : Nat := 118140960795 + 2806851 * 2 ^ 59
def prefixEnd_2806851 : Nat := 4983230072969 + 3 ^ 40 * 2806851 * 2
def baseEnd_2806851 : Nat := 1441263688553102916254033

theorem tailTrace_2806851 : CollatzResearch.WordTrace tailWord_2806851 prefixEnd_2806851 1441263688553102916254033 := by
  unfold tailWord_2806851
  simp only [CollatzResearch.WordTrace]
  refine ⟨102374266354265673831156407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68249510902843782554104271 102374266354265673831156407)
  ·
    refine ⟨153561399531398510746734611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102374266354265673831156407 153561399531398510746734611)
    ·
      refine ⟨230342099297097766120101917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153561399531398510746734611 230342099297097766120101917)
      ·
        refine ⟨86378287236411662295038219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230342099297097766120101917 86378287236411662295038219)
        ·
          refine ⟨129567430854617493442557329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86378287236411662295038219 129567430854617493442557329)
          ·
            refine ⟨97175573140963120081917997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129567430854617493442557329 97175573140963120081917997)
            ·
              refine ⟨36440839927861170030719249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97175573140963120081917997 36440839927861170030719249)
              ·
                refine ⟨27330629945895877523039437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36440839927861170030719249 27330629945895877523039437)
                ·
                  refine ⟨10248986229710954071139789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27330629945895877523039437 10248986229710954071139789)
                  ·
                    refine ⟨3843369836141607776677421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10248986229710954071139789 3843369836141607776677421)
                    ·
                      refine ⟨1441263688553102916254033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3843369836141607776677421 1441263688553102916254033)
                      ·
                        rfl

theorem cell23_2806851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_2806851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806851 prefixEnd_2806851 := by exact prefixLift 2806851
  have htrace : WordTrace (prefixWord ++ tailWord_2806851) baseStart_2806851 baseEnd_2806851 := by
    simpa [prefixWord, tailWord_2806851, baseEnd_2806851] using wordTrace_append hprefix tailTrace_2806851
  have hstable : (prefixWord ++ tailWord_2806851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806851).length < 2 ^ (prefixWord ++ tailWord_2806851).sum := by decide
  have hdescent : baseEnd_2806851 < baseStart_2806851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806868 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_2806868 : Nat := 118140960795 + 2806868 * 2 ^ 59
def prefixEnd_2806868 : Nat := 4983230072969 + 3 ^ 40 * 2806868 * 2
def baseEnd_2806868 : Nat := 1441272417724229349741455

theorem tailTrace_2806868 : CollatzResearch.WordTrace tailWord_2806868 prefixEnd_2806868 1441272417724229349741455 := by
  unfold tailWord_2806868
  simp only [CollatzResearch.WordTrace]
  refine ⟨51187443197602042867262629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68249924263469390489683505 51187443197602042867262629)
  ·
    refine ⟨9597645599550383037611743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51187443197602042867262629 9597645599550383037611743)
    ·
      refine ⟨14396468399325574556417615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9597645599550383037611743 14396468399325574556417615)
      ·
        refine ⟨21594702598988361834626423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14396468399325574556417615 21594702598988361834626423)
        ·
          refine ⟨32392053898482542751939635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21594702598988361834626423 32392053898482542751939635)
          ·
            refine ⟨48588080847723814127909453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32392053898482542751939635 48588080847723814127909453)
            ·
              refine ⟨18220530317896430297966045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48588080847723814127909453 18220530317896430297966045)
              ·
                refine ⟨6832698869211161361737267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18220530317896430297966045 6832698869211161361737267)
                ·
                  refine ⟨10249048303816742042605901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6832698869211161361737267 10249048303816742042605901)
                  ·
                    refine ⟨3843393113931278265977213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10249048303816742042605901 3843393113931278265977213)
                    ·
                      refine ⟨1441272417724229349741455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3843393113931278265977213 1441272417724229349741455)
                      ·
                        rfl

theorem cell23_2806868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_2806868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806868 prefixEnd_2806868 := by exact prefixLift 2806868
  have htrace : WordTrace (prefixWord ++ tailWord_2806868) baseStart_2806868 baseEnd_2806868 := by
    simpa [prefixWord, tailWord_2806868, baseEnd_2806868] using wordTrace_append hprefix tailTrace_2806868
  have hstable : (prefixWord ++ tailWord_2806868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806868).length < 2 ^ (prefixWord ++ tailWord_2806868).sum := by decide
  have hdescent : baseEnd_2806868 < baseStart_2806868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806895 : List Nat := [1, 1, 2, 1, 3, 3, 3, 3, 1, 3, 2]
def baseStart_2806895 : Nat := 118140960795 + 2806895 * 2 ^ 59
def prefixEnd_2806895 : Nat := 4983230072969 + 3 ^ 40 * 2806895 * 2
def baseEnd_2806895 : Nat := 1441286281701900744103831

theorem tailTrace_2806895 : CollatzResearch.WordTrace tailWord_2806895 prefixEnd_2806895 1441286281701900744103831 := by
  unfold tailWord_2806895
  simp only [CollatzResearch.WordTrace]
  refine ⟨102375871166106269345758139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68250580777404179563838759 102375871166106269345758139)
  ·
    refine ⟨153563806749159404018637209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102375871166106269345758139 153563806749159404018637209)
    ·
      refine ⟨115172855061869553013977907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153563806749159404018637209 115172855061869553013977907)
      ·
        refine ⟨172759282592804329520966861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115172855061869553013977907 172759282592804329520966861)
        ·
          refine ⟨64784730972301623570362573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172759282592804329520966861 64784730972301623570362573)
          ·
            refine ⟨24294274114613108838885965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64784730972301623570362573 24294274114613108838885965)
            ·
              refine ⟨9110352792979915814582237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24294274114613108838885965 9110352792979915814582237)
              ·
                refine ⟨3416382297367468430468339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9110352792979915814582237 3416382297367468430468339)
                ·
                  refine ⟨5124573446051202645702509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3416382297367468430468339 5124573446051202645702509)
                  ·
                    refine ⟨1921715042269200992138441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5124573446051202645702509 1921715042269200992138441)
                    ·
                      refine ⟨1441286281701900744103831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1921715042269200992138441 1441286281701900744103831)
                      ·
                        rfl

theorem cell23_2806895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 3, 2].length) (baseStart_2806895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806895 prefixEnd_2806895 := by exact prefixLift 2806895
  have htrace : WordTrace (prefixWord ++ tailWord_2806895) baseStart_2806895 baseEnd_2806895 := by
    simpa [prefixWord, tailWord_2806895, baseEnd_2806895] using wordTrace_append hprefix tailTrace_2806895
  have hstable : (prefixWord ++ tailWord_2806895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806895).length < 2 ^ (prefixWord ++ tailWord_2806895).sum := by decide
  have hdescent : baseEnd_2806895 < baseStart_2806895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806931 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 7]
def baseStart_2806931 : Nat := 118140960795 + 2806931 * 2 ^ 59
def prefixEnd_2806931 : Nat := 4983230072969 + 3 ^ 40 * 2806931 * 2
def baseEnd_2806931 : Nat := 160144974111718067028185

theorem tailTrace_2806931 : CollatzResearch.WordTrace tailWord_2806931 prefixEnd_2806931 160144974111718067028185 := by
  unfold tailWord_2806931
  simp only [CollatzResearch.WordTrace]
  refine ⟨102377184193975847494068647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68251456129317231662712431 102377184193975847494068647)
  ·
    refine ⟨153565776290963771241102971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102377184193975847494068647 153565776290963771241102971)
    ·
      refine ⟨230348664436445656861654457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153565776290963771241102971 230348664436445656861654457)
      ·
        refine ⟨172761498327334242646240843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230348664436445656861654457 172761498327334242646240843)
        ·
          refine ⟨259142247491001363969361265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172761498327334242646240843 259142247491001363969361265)
          ·
            refine ⟨194356685618251022977020949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259142247491001363969361265 194356685618251022977020949)
            ·
              refine ⟨9110469638355516702047857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 194356685618251022977020949 9110469638355516702047857)
              ·
                refine ⟨6832852228766637526535893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9110469638355516702047857 6832852228766637526535893)
                ·
                  refine ⟨160144974111718067028185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6832852228766637526535893 160144974111718067028185)
                  ·
                    rfl

theorem cell23_2806931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 7].length) (baseStart_2806931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806931 prefixEnd_2806931 := by exact prefixLift 2806931
  have htrace : WordTrace (prefixWord ++ tailWord_2806931) baseStart_2806931 baseEnd_2806931 := by
    simpa [prefixWord, tailWord_2806931, baseEnd_2806931] using wordTrace_append hprefix tailTrace_2806931
  have hstable : (prefixWord ++ tailWord_2806931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806931).length < 2 ^ (prefixWord ++ tailWord_2806931).sum := by decide
  have hdescent : baseEnd_2806931 < baseStart_2806931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2806976 : List Nat := [2, 1, 1, 2, 6, 2, 2, 1, 2, 2, 2]
def baseStart_2806976 : Nat := 118140960795 + 2806976 * 2 ^ 59
def prefixEnd_2806976 : Nat := 4983230072969 + 3 ^ 40 * 2806976 * 2
def baseEnd_2806976 : Nat := 1441327873634914927190959

theorem tailTrace_2806976 : CollatzResearch.WordTrace tailWord_2806976 prefixEnd_2806976 1441327873634914927190959 := by
  unfold tailWord_2806976
  simp only [CollatzResearch.WordTrace]
  refine ⟨51189412739406410089728391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68252550319208546786304521 51189412739406410089728391)
  ·
    refine ⟨76784119109109615134592587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51189412739406410089728391 76784119109109615134592587)
    ·
      refine ⟨115176178663664422701888881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76784119109109615134592587 115176178663664422701888881)
      ·
        refine ⟨86382133997748317026416661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115176178663664422701888881 86382133997748317026416661)
        ·
          refine ⟨4049162531144452360613281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86382133997748317026416661 4049162531144452360613281)
          ·
            refine ⟨3036871898358339270459961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4049162531144452360613281 3036871898358339270459961)
            ·
              refine ⟨2277653923768754452844971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3036871898358339270459961 2277653923768754452844971)
              ·
                refine ⟨3416480885653131679267457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2277653923768754452844971 3416480885653131679267457)
                ·
                  refine ⟨2562360664239848759450593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3416480885653131679267457 2562360664239848759450593)
                  ·
                    refine ⟨1921770498179886569587945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2562360664239848759450593 1921770498179886569587945)
                    ·
                      refine ⟨1441327873634914927190959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1921770498179886569587945 1441327873634914927190959)
                      ·
                        rfl

theorem cell23_2806976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 2, 2, 2].length) (baseStart_2806976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2806976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2806976 prefixEnd_2806976 := by exact prefixLift 2806976
  have htrace : WordTrace (prefixWord ++ tailWord_2806976) baseStart_2806976 baseEnd_2806976 := by
    simpa [prefixWord, tailWord_2806976, baseEnd_2806976] using wordTrace_append hprefix tailTrace_2806976
  have hstable : (prefixWord ++ tailWord_2806976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2806976).length < 2 ^ (prefixWord ++ tailWord_2806976).sum := by decide
  have hdescent : baseEnd_2806976 < baseStart_2806976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2806976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807052 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 2, 2, 3]
def baseStart_2807052 : Nat := 118140960795 + 2807052 * 2 ^ 59
def prefixEnd_2807052 : Nat := 4983230072969 + 3 ^ 40 * 2807052 * 2
def baseEnd_2807052 : Nat := 1441366898164656629840609

theorem tailTrace_2807052 : CollatzResearch.WordTrace tailWord_2807052 prefixEnd_2807052 1441366898164656629840609 := by
  unfold tailWord_2807052
  simp only [CollatzResearch.WordTrace]
  refine ⟨51190798713268742579611705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68254398284358323439482273 51190798713268742579611705)
  ·
    refine ⟨38393099034951556934708779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51190798713268742579611705 38393099034951556934708779)
    ·
      refine ⟨57589648552427335402063169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38393099034951556934708779 57589648552427335402063169)
      ·
        refine ⟨43192236414320501551547377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57589648552427335402063169 43192236414320501551547377)
        ·
          refine ⟨32394177310740376163660533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43192236414320501551547377 32394177310740376163660533)
          ·
            refine ⟨3036954122881910265343175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32394177310740376163660533 3036954122881910265343175)
            ·
              refine ⟨4555431184322865398014763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3036954122881910265343175 4555431184322865398014763)
              ·
                refine ⟨6833146776484298097022145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555431184322865398014763 6833146776484298097022145)
                ·
                  refine ⟨5124860082363223572766609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6833146776484298097022145 5124860082363223572766609)
                  ·
                    refine ⟨3843645061772417679574957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5124860082363223572766609 3843645061772417679574957)
                    ·
                      refine ⟨1441366898164656629840609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3843645061772417679574957 1441366898164656629840609)
                      ·
                        rfl

theorem cell23_2807052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_2807052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807052 prefixEnd_2807052 := by exact prefixLift 2807052
  have htrace : WordTrace (prefixWord ++ tailWord_2807052) baseStart_2807052 baseEnd_2807052 := by
    simpa [prefixWord, tailWord_2807052, baseEnd_2807052] using wordTrace_append hprefix tailTrace_2807052
  have hstable : (prefixWord ++ tailWord_2807052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807052).length < 2 ^ (prefixWord ++ tailWord_2807052).sum := by decide
  have hdescent : baseEnd_2807052 < baseStart_2807052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807072 : List Nat := [2, 1, 1, 5, 3, 2, 1, 2, 6]
def baseStart_2807072 : Nat := 118140960795 + 2807072 * 2 ^ 59
def prefixEnd_2807072 : Nat := 4983230072969 + 3 ^ 40 * 2807072 * 2
def baseEnd_2807072 : Nat := 160153018641971839065613

theorem tailTrace_2807072 : CollatzResearch.WordTrace tailWord_2807072 prefixEnd_2807072 160153018641971839065613 := by
  unfold tailWord_2807072
  simp only [CollatzResearch.WordTrace]
  refine ⟨51191163443232514287475735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68254884590976685716634313 51191163443232514287475735)
  ·
    refine ⟨76786745164848771431213603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51191163443232514287475735 76786745164848771431213603)
    ·
      refine ⟨115180117747273157146820405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76786745164848771431213603 115180117747273157146820405)
      ·
        refine ⟨10798136038806858482514413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115180117747273157146820405 10798136038806858482514413)
        ·
          refine ⟨4049301014552571930942905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10798136038806858482514413 4049301014552571930942905)
          ·
            refine ⟨3036975760914428948207179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4049301014552571930942905 3036975760914428948207179)
            ·
              refine ⟨4555463641371643422310769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3036975760914428948207179 4555463641371643422310769)
              ·
                refine ⟨3416597731028732566733077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4555463641371643422310769 3416597731028732566733077)
                ·
                  refine ⟨160153018641971839065613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3416597731028732566733077 160153018641971839065613)
                  ·
                    rfl

theorem cell23_2807072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 6].length) (baseStart_2807072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807072 prefixEnd_2807072 := by exact prefixLift 2807072
  have htrace : WordTrace (prefixWord ++ tailWord_2807072) baseStart_2807072 baseEnd_2807072 := by
    simpa [prefixWord, tailWord_2807072, baseEnd_2807072] using wordTrace_append hprefix tailTrace_2807072
  have hstable : (prefixWord ++ tailWord_2807072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807072).length < 2 ^ (prefixWord ++ tailWord_2807072).sum := by decide
  have hdescent : baseEnd_2807072 < baseStart_2807072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807092 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_2807092 : Nat := 118140960795 + 2807092 * 2 ^ 59
def prefixEnd_2807092 : Nat := 4983230072969 + 3 ^ 40 * 2807092 * 2
def baseEnd_2807092 : Nat := 1441387437390836473340425

theorem tailTrace_2807092 : CollatzResearch.WordTrace tailWord_2807092 prefixEnd_2807092 1441387437390836473340425 := by
  unfold tailWord_2807092
  simp only [CollatzResearch.WordTrace]
  refine ⟨51191528173196285995339765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68255370897595047993786353 51191528173196285995339765)
  ·
    refine ⟨4799205766237151812063103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51191528173196285995339765 4799205766237151812063103)
    ·
      refine ⟨7198808649355727718094655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4799205766237151812063103 7198808649355727718094655)
      ·
        refine ⟨10798212974033591577141983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7198808649355727718094655 10798212974033591577141983)
        ·
          refine ⟨16197319461050387365712975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10798212974033591577141983 16197319461050387365712975)
          ·
            refine ⟨24295979191575581048569463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16197319461050387365712975 24295979191575581048569463)
            ·
              refine ⟨36443968787363371572854195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24295979191575581048569463 36443968787363371572854195)
              ·
                refine ⟨54665953181045057359281293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36443968787363371572854195 54665953181045057359281293)
                ·
                  refine ⟨20499732442891896509730485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54665953181045057359281293 20499732442891896509730485)
                  ·
                    refine ⟨1921849916521115297787233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20499732442891896509730485 1921849916521115297787233)
                    ·
                      refine ⟨1441387437390836473340425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1921849916521115297787233 1441387437390836473340425)
                      ·
                        rfl

theorem cell23_2807092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_2807092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807092 prefixEnd_2807092 := by exact prefixLift 2807092
  have htrace : WordTrace (prefixWord ++ tailWord_2807092) baseStart_2807092 baseEnd_2807092 := by
    simpa [prefixWord, tailWord_2807092, baseEnd_2807092] using wordTrace_append hprefix tailTrace_2807092
  have hstable : (prefixWord ++ tailWord_2807092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807092).length < 2 ^ (prefixWord ++ tailWord_2807092).sum := by decide
  have hdescent : baseEnd_2807092 < baseStart_2807092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807102 : List Nat := [4, 2, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_2807102 : Nat := 118140960795 + 2807102 * 2 ^ 59
def prefixEnd_2807102 : Nat := 4983230072969 + 3 ^ 40 * 2807102 * 2
def baseEnd_2807102 : Nat := 480464190732460478071793

theorem tailTrace_2807102 : CollatzResearch.WordTrace tailWord_2807102 prefixEnd_2807102 480464190732460478071793 := by
  unfold tailWord_2807102
  simp only [CollatzResearch.WordTrace]
  refine ⟨12797927634544542962317945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68255614050904229132362373 12797927634544542962317945)
  ·
    refine ⟨9598445725908407221738459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12797927634544542962317945 9598445725908407221738459)
    ·
      refine ⟨14397668588862610832607689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9598445725908407221738459 14397668588862610832607689)
      ·
        refine ⟨10798251441646958124455767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14397668588862610832607689 10798251441646958124455767)
        ·
          refine ⟨16197377162470437186683651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10798251441646958124455767 16197377162470437186683651)
          ·
            refine ⟨24296065743705655780025477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16197377162470437186683651 24296065743705655780025477)
            ·
              refine ⟨4555512326944810458754777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24296065743705655780025477 4555512326944810458754777)
              ·
                refine ⟨3416634245208607844066083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4555512326944810458754777 3416634245208607844066083)
                ·
                  refine ⟨5124951367812911766099125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3416634245208607844066083 5124951367812911766099125)
                  ·
                    refine ⟨480464190732460478071793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5124951367812911766099125 480464190732460478071793)
                    ·
                      rfl

theorem cell23_2807102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_2807102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807102 prefixEnd_2807102 := by exact prefixLift 2807102
  have htrace : WordTrace (prefixWord ++ tailWord_2807102) baseStart_2807102 baseEnd_2807102 := by
    simpa [prefixWord, tailWord_2807102, baseEnd_2807102] using wordTrace_append hprefix tailTrace_2807102
  have hstable : (prefixWord ++ tailWord_2807102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807102).length < 2 ^ (prefixWord ++ tailWord_2807102).sum := by decide
  have hdescent : baseEnd_2807102 < baseStart_2807102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807110 : List Nat := [6, 1, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_2807110 : Nat := 118140960795 + 2807110 * 2 ^ 59
def prefixEnd_2807110 : Nat := 4983230072969 + 3 ^ 40 * 2807110 * 2
def baseEnd_2807110 : Nat := 480465560014205800971781

theorem tailTrace_2807110 : CollatzResearch.WordTrace tailWord_2807110 prefixEnd_2807110 480465560014205800971781 := by
  unfold tailWord_2807110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3199491026885230033276087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68255808573551574043223189 3199491026885230033276087)
  ·
    refine ⟨4799236540327845049914131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3199491026885230033276087 4799236540327845049914131)
    ·
      refine ⟨7198854810491767574871197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4799236540327845049914131 7198854810491767574871197)
      ·
        refine ⟨2699570553934412840576699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7198854810491767574871197 2699570553934412840576699)
        ·
          refine ⟨4049355830901619260865049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2699570553934412840576699 4049355830901619260865049)
          ·
            refine ⟨3037016873176214445648787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4049355830901619260865049 3037016873176214445648787)
            ·
              refine ⟨4555525309764321668473181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3037016873176214445648787 4555525309764321668473181)
              ·
                refine ⟨1708321991161620625677443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4555525309764321668473181 1708321991161620625677443)
                ·
                  refine ⟨2562482986742430938516165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1708321991161620625677443 2562482986742430938516165)
                  ·
                    refine ⟨480465560014205800971781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2562482986742430938516165 480465560014205800971781)
                    ·
                      rfl

theorem cell23_2807110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_2807110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807110 prefixEnd_2807110 := by exact prefixLift 2807110
  have htrace : WordTrace (prefixWord ++ tailWord_2807110) baseStart_2807110 baseEnd_2807110 := by
    simpa [prefixWord, tailWord_2807110, baseEnd_2807110] using wordTrace_append hprefix tailTrace_2807110
  have hstable : (prefixWord ++ tailWord_2807110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807110).length < 2 ^ (prefixWord ++ tailWord_2807110).sum := by decide
  have hdescent : baseEnd_2807110 < baseStart_2807110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807116 : List Nat := [2, 2, 1, 3, 2, 4, 1, 3, 1, 1, 3]
def baseStart_2807116 : Nat := 118140960795 + 2807116 * 2 ^ 59
def prefixEnd_2807116 : Nat := 4983230072969 + 3 ^ 40 * 2807116 * 2
def baseEnd_2807116 : Nat := 1441399760926544379440315

theorem tailTrace_2807116 : CollatzResearch.WordTrace tailWord_2807116 prefixEnd_2807116 1441399760926544379440315 := by
  unfold tailWord_2807116
  simp only [CollatzResearch.WordTrace]
  refine ⟨51191965849152812044776601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68255954465537082726368801 51191965849152812044776601)
  ·
    refine ⟨38393974386864609033582451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51191965849152812044776601 38393974386864609033582451)
    ·
      refine ⟨57590961580296913550373677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38393974386864609033582451 57590961580296913550373677)
      ·
        refine ⟨21596610592611342581390129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57590961580296913550373677 21596610592611342581390129)
        ·
          refine ⟨16197457944458506936042597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21596610592611342581390129 16197457944458506936042597)
          ·
            refine ⟨3037023364585970050507987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16197457944458506936042597 3037023364585970050507987)
            ·
              refine ⟨4555535046878955075761981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3037023364585970050507987 4555535046878955075761981)
              ·
                refine ⟨1708325642579608153410743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4555535046878955075761981 1708325642579608153410743)
                ·
                  refine ⟨2562488463869412230116115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1708325642579608153410743 2562488463869412230116115)
                  ·
                    refine ⟨3843732695804118345174173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2562488463869412230116115 3843732695804118345174173)
                    ·
                      refine ⟨1441399760926544379440315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3843732695804118345174173 1441399760926544379440315)
                      ·
                        rfl

theorem cell23_2807116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_2807116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807116 prefixEnd_2807116 := by exact prefixLift 2807116
  have htrace : WordTrace (prefixWord ++ tailWord_2807116) baseStart_2807116 baseEnd_2807116 := by
    simpa [prefixWord, tailWord_2807116, baseEnd_2807116] using wordTrace_append hprefix tailTrace_2807116
  have hstable : (prefixWord ++ tailWord_2807116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807116).length < 2 ^ (prefixWord ++ tailWord_2807116).sum := by decide
  have hdescent : baseEnd_2807116 < baseStart_2807116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807125 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_2807125 : Nat := 118140960795 + 2807125 * 2 ^ 59
def prefixEnd_2807125 : Nat := 4983230072969 + 3 ^ 40 * 2807125 * 2
def baseEnd_2807125 : Nat := 1441404382252434844227773

theorem tailTrace_2807125 : CollatzResearch.WordTrace tailWord_2807125 prefixEnd_2807125 1441404382252434844227773 := by
  unfold tailWord_2807125
  simp only [CollatzResearch.WordTrace]
  refine ⟨102384259955273018626630829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68256173303515345751087219 102384259955273018626630829)
  ·
    refine ⟨38394097483227381984986561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102384259955273018626630829 38394097483227381984986561)
    ·
      refine ⟨28795573112420536488739921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38394097483227381984986561 28795573112420536488739921)
      ·
        refine ⟨21596679834315402366554941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28795573112420536488739921 21596679834315402366554941)
        ·
          refine ⟨8098754937868275887458103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21596679834315402366554941 8098754937868275887458103)
          ·
            refine ⟨12148132406802413831187155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8098754937868275887458103 12148132406802413831187155)
            ·
              refine ⟨18222198610203620746780733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12148132406802413831187155 18222198610203620746780733)
              ·
                refine ⟨6833324478826357780042775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18222198610203620746780733 6833324478826357780042775)
                ·
                  refine ⟨10249986718239536670064163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6833324478826357780042775 10249986718239536670064163)
                  ·
                    refine ⟨15374980077359305005096245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10249986718239536670064163 15374980077359305005096245)
                    ·
                      refine ⟨1441404382252434844227773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15374980077359305005096245 1441404382252434844227773)
                      ·
                        rfl

theorem cell23_2807125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_2807125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807125 prefixEnd_2807125 := by exact prefixLift 2807125
  have htrace : WordTrace (prefixWord ++ tailWord_2807125) baseStart_2807125 baseEnd_2807125 := by
    simpa [prefixWord, tailWord_2807125, baseEnd_2807125] using wordTrace_append hprefix tailTrace_2807125
  have hstable : (prefixWord ++ tailWord_2807125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807125).length < 2 ^ (prefixWord ++ tailWord_2807125).sum := by decide
  have hdescent : baseEnd_2807125 < baseStart_2807125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807139 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 3, 2, 2]
def baseStart_2807139 : Nat := 118140960795 + 2807139 * 2 ^ 59
def prefixEnd_2807139 : Nat := 4983230072969 + 3 ^ 40 * 2807139 * 2
def baseEnd_2807139 : Nat := 1441411570981597789452709

theorem tailTrace_2807139 : CollatzResearch.WordTrace tailWord_2807139 prefixEnd_2807139 1441411570981597789452709 := by
  unfold tailWord_2807139
  simp only [CollatzResearch.WordTrace]
  refine ⟨102384770577222299017640471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68256513718148199345093647 102384770577222299017640471)
  ·
    refine ⟨153577155865833448526460707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102384770577222299017640471 153577155865833448526460707)
    ·
      refine ⟨230365733798750172789691061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153577155865833448526460707 230365733798750172789691061)
      ·
        refine ⟨21596787543632828699033537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 230365733798750172789691061 21596787543632828699033537)
        ·
          refine ⟨16197590657724621524275153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21596787543632828699033537 16197590657724621524275153)
          ·
            refine ⟨12148192993293466143206365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16197590657724621524275153 12148192993293466143206365)
            ·
              refine ⟨4555572372485049803702387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12148192993293466143206365 4555572372485049803702387)
              ·
                refine ⟨6833358558727574705553581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555572372485049803702387 6833358558727574705553581)
                ·
                  refine ⟨2562509459522840514582593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6833358558727574705553581 2562509459522840514582593)
                  ·
                    refine ⟨1921882094642130385936945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2562509459522840514582593 1921882094642130385936945)
                    ·
                      refine ⟨1441411570981597789452709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1921882094642130385936945 1441411570981597789452709)
                      ·
                        rfl

theorem cell23_2807139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_2807139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807139 prefixEnd_2807139 := by exact prefixLift 2807139
  have htrace : WordTrace (prefixWord ++ tailWord_2807139) baseStart_2807139 baseEnd_2807139 := by
    simpa [prefixWord, tailWord_2807139, baseEnd_2807139] using wordTrace_append hprefix tailTrace_2807139
  have hstable : (prefixWord ++ tailWord_2807139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807139).length < 2 ^ (prefixWord ++ tailWord_2807139).sum := by decide
  have hdescent : baseEnd_2807139 < baseStart_2807139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807149 : List Nat := [1, 5, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_2807149 : Nat := 118140960795 + 2807149 * 2 ^ 59
def prefixEnd_2807149 : Nat := 4983230072969 + 3 ^ 40 * 2807149 * 2
def baseEnd_2807149 : Nat := 480472235262714250109221

theorem tailTrace_2807149 : CollatzResearch.WordTrace tailWord_2807149 prefixEnd_2807149 480472235262714250109221 := by
  unfold tailWord_2807149
  simp only [CollatzResearch.WordTrace]
  refine ⟨102385135307186070725504501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68256756871457380483669667 102385135307186070725504501)
  ·
    refine ⟨9598606435048694130516047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102385135307186070725504501 9598606435048694130516047)
    ·
      refine ⟨14397909652573041195774071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9598606435048694130516047 14397909652573041195774071)
      ·
        refine ⟨21596864478859561793661107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14397909652573041195774071 21596864478859561793661107)
        ·
          refine ⟨32395296718289342690491661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21596864478859561793661107 32395296718289342690491661)
          ·
            refine ⟨12148236269358503508934373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32395296718289342690491661 12148236269358503508934373)
            ·
              refine ⟨2277794300504719407925195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12148236269358503508934373 2277794300504719407925195)
              ·
                refine ⟨3416691450757079111887793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2277794300504719407925195 3416691450757079111887793)
                ·
                  refine ⟨2562518588067809333915845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3416691450757079111887793 2562518588067809333915845)
                  ·
                    refine ⟨480472235262714250109221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2562518588067809333915845 480472235262714250109221)
                    ·
                      rfl

theorem cell23_2807149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_2807149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807149 prefixEnd_2807149 := by exact prefixLift 2807149
  have htrace : WordTrace (prefixWord ++ tailWord_2807149) baseStart_2807149 baseEnd_2807149 := by
    simpa [prefixWord, tailWord_2807149, baseEnd_2807149] using wordTrace_append hprefix tailTrace_2807149
  have hstable : (prefixWord ++ tailWord_2807149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807149).length < 2 ^ (prefixWord ++ tailWord_2807149).sum := by decide
  have hdescent : baseEnd_2807149 < baseStart_2807149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807168 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 5]
def baseStart_2807168 : Nat := 118140960795 + 2807168 * 2 ^ 59
def prefixEnd_2807168 : Nat := 4983230072969 + 3 ^ 40 * 2807168 * 2
def baseEnd_2807168 : Nat := 1441426461920578175990075

theorem tailTrace_2807168 : CollatzResearch.WordTrace tailWord_2807168 prefixEnd_2807168 1441426461920578175990075 := by
  unfold tailWord_2807168
  simp only [CollatzResearch.WordTrace]
  refine ⟨51192914147058618485223079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68257218862744824646964105 51192914147058618485223079)
  ·
    refine ⟨76789371220587927727834619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51192914147058618485223079 76789371220587927727834619)
    ·
      refine ⟨115184056830881891591751929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76789371220587927727834619 115184056830881891591751929)
      ·
        refine ⟨86388042623161418693813947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115184056830881891591751929 86388042623161418693813947)
        ·
          refine ⟨129582063934742128040720921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86388042623161418693813947 129582063934742128040720921)
          ·
            refine ⟨97186547951056596030540691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129582063934742128040720921 97186547951056596030540691)
            ·
              refine ⟨145779821926584894045811037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97186547951056596030540691 145779821926584894045811037)
              ·
                refine ⟨54667433222469335267179139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145779821926584894045811037 54667433222469335267179139)
                ·
                  refine ⟨82001149833704002900768709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54667433222469335267179139 82001149833704002900768709)
                  ·
                    refine ⟨15375215593819500543894133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82001149833704002900768709 15375215593819500543894133)
                    ·
                      refine ⟨1441426461920578175990075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15375215593819500543894133 1441426461920578175990075)
                      ·
                        rfl

theorem cell23_2807168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_2807168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807168 prefixEnd_2807168 := by exact prefixLift 2807168
  have htrace : WordTrace (prefixWord ++ tailWord_2807168) baseStart_2807168 baseEnd_2807168 := by
    simpa [prefixWord, tailWord_2807168, baseEnd_2807168] using wordTrace_append hprefix tailTrace_2807168
  have hstable : (prefixWord ++ tailWord_2807168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807168).length < 2 ^ (prefixWord ++ tailWord_2807168).sum := by decide
  have hdescent : baseEnd_2807168 < baseStart_2807168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807172 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_2807172 : Nat := 118140960795 + 2807172 * 2 ^ 59
def prefixEnd_2807172 : Nat := 4983230072969 + 3 ^ 40 * 2807172 * 2
def baseEnd_2807172 : Nat := 1441428515843196160340057

theorem tailTrace_2807172 : CollatzResearch.WordTrace tailWord_2807172 prefixEnd_2807172 1441428515843196160340057 := by
  unfold tailWord_2807172
  simp only [CollatzResearch.WordTrace]
  refine ⟨51192987093051372826795885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68257316124068497102394513 51192987093051372826795885)
  ·
    refine ⟨19197370159894264810048457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51192987093051372826795885 19197370159894264810048457)
    ·
      refine ⟨14398027619920698607536343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19197370159894264810048457 14398027619920698607536343)
      ·
        refine ⟨21597041429881047911304515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14398027619920698607536343 21597041429881047911304515)
        ·
          refine ⟨32395562144821571866956773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21597041429881047911304515 32395562144821571866956773)
          ·
            refine ⟨6074167902154044725054395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32395562144821571866956773 6074167902154044725054395)
            ·
              refine ⟨9111251853231067087581593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6074167902154044725054395 9111251853231067087581593)
              ·
                refine ⟨6833438889923300315686195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9111251853231067087581593 6833438889923300315686195)
                ·
                  refine ⟨10250158334884950473529293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6833438889923300315686195 10250158334884950473529293)
                  ·
                    refine ⟨3843809375581856427573485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10250158334884950473529293 3843809375581856427573485)
                    ·
                      refine ⟨1441428515843196160340057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3843809375581856427573485 1441428515843196160340057)
                      ·
                        rfl

theorem cell23_2807172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_2807172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807172 prefixEnd_2807172 := by exact prefixLift 2807172
  have htrace : WordTrace (prefixWord ++ tailWord_2807172) baseStart_2807172 baseEnd_2807172 := by
    simpa [prefixWord, tailWord_2807172, baseEnd_2807172] using wordTrace_append hprefix tailTrace_2807172
  have hstable : (prefixWord ++ tailWord_2807172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807172).length < 2 ^ (prefixWord ++ tailWord_2807172).sum := by decide
  have hdescent : baseEnd_2807172 < baseStart_2807172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807212 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 1, 4, 2]
def baseStart_2807212 : Nat := 118140960795 + 2807212 * 2 ^ 59
def prefixEnd_2807212 : Nat := 4983230072969 + 3 ^ 40 * 2807212 * 2
def baseEnd_2807212 : Nat := 1441449055069376003839873

theorem tailTrace_2807212 : CollatzResearch.WordTrace tailWord_2807212 prefixEnd_2807212 1441449055069376003839873 := by
  unfold tailWord_2807212
  simp only [CollatzResearch.WordTrace]
  refine ⟨51193716552978916242523945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68258288737305221656698593 51193716552978916242523945)
  ·
    refine ⟨38395287414734187181892959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51193716552978916242523945 38395287414734187181892959)
    ·
      refine ⟨57592931122101280772839439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38395287414734187181892959 57592931122101280772839439)
      ·
        refine ⟨86389396683151921159259159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57592931122101280772839439 86389396683151921159259159)
        ·
          refine ⟨129584095024727881738888739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86389396683151921159259159 129584095024727881738888739)
          ·
            refine ⟨194376142537091822608333109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129584095024727881738888739 194376142537091822608333109)
            ·
              refine ⟨18222763362852358369531229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 194376142537091822608333109 18222763362852358369531229)
              ·
                refine ⟨6833536261069634388574211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18222763362852358369531229 6833536261069634388574211)
                ·
                  refine ⟨10250304391604451582861317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6833536261069634388574211 10250304391604451582861317)
                  ·
                    refine ⟨1921932073425834671786497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10250304391604451582861317 1921932073425834671786497)
                    ·
                      refine ⟨1441449055069376003839873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1921932073425834671786497 1441449055069376003839873)
                      ·
                        rfl

theorem cell23_2807212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 4, 2].length) (baseStart_2807212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807212 prefixEnd_2807212 := by exact prefixLift 2807212
  have htrace : WordTrace (prefixWord ++ tailWord_2807212) baseStart_2807212 baseEnd_2807212 := by
    simpa [prefixWord, tailWord_2807212, baseEnd_2807212] using wordTrace_append hprefix tailTrace_2807212
  have hstable : (prefixWord ++ tailWord_2807212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807212).length < 2 ^ (prefixWord ++ tailWord_2807212).sum := by decide
  have hdescent : baseEnd_2807212 < baseStart_2807212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807229 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 4, 2, 2]
def baseStart_2807229 : Nat := 118140960795 + 2807229 * 2 ^ 59
def prefixEnd_2807229 : Nat := 4983230072969 + 3 ^ 40 * 2807229 * 2
def baseEnd_2807229 : Nat := 1441457784240502437327295

theorem tailTrace_2807229 : CollatzResearch.WordTrace tailWord_2807229 prefixEnd_2807229 1441457784240502437327295 := by
  unfold tailWord_2807229
  simp only [CollatzResearch.WordTrace]
  refine ⟨102388053146896244388416741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68258702097930829592277827 102388053146896244388416741)
  ·
    refine ⟨19197759965043045822828139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102388053146896244388416741 19197759965043045822828139)
    ·
      refine ⟨28796639947564568734242209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19197759965043045822828139 28796639947564568734242209)
      ·
        refine ⟨21597479960673426550681657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28796639947564568734242209 21597479960673426550681657)
        ·
          refine ⟨16198109970505069913011243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21597479960673426550681657 16198109970505069913011243)
          ·
            refine ⟨24297164955757604869516865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16198109970505069913011243 24297164955757604869516865)
            ·
              refine ⟨18222873716818203652137649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24297164955757604869516865 18222873716818203652137649)
              ·
                refine ⟨13667155287613652739103237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18222873716818203652137649 13667155287613652739103237)
                ·
                  refine ⟨2562591616427559888581857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13667155287613652739103237 2562591616427559888581857)
                  ·
                    refine ⟨1921943712320669916436393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2562591616427559888581857 1921943712320669916436393)
                    ·
                      refine ⟨1441457784240502437327295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1921943712320669916436393 1441457784240502437327295)
                      ·
                        rfl

theorem cell23_2807229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_2807229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807229 prefixEnd_2807229 := by exact prefixLift 2807229
  have htrace : WordTrace (prefixWord ++ tailWord_2807229) baseStart_2807229 baseEnd_2807229 := by
    simpa [prefixWord, tailWord_2807229, baseEnd_2807229] using wordTrace_append hprefix tailTrace_2807229
  have hstable : (prefixWord ++ tailWord_2807229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807229).length < 2 ^ (prefixWord ++ tailWord_2807229).sum := by decide
  have hdescent : baseEnd_2807229 < baseStart_2807229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807246 : List Nat := [4, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2]
def baseStart_2807246 : Nat := 118140960795 + 2807246 * 2 ^ 59
def prefixEnd_2807246 : Nat := 4983230072969 + 3 ^ 40 * 2807246 * 2
def baseEnd_2807246 : Nat := 1441466513411628870814717

theorem tailTrace_2807246 : CollatzResearch.WordTrace tailWord_2807246 prefixEnd_2807246 1441466513411628870814717 := by
  unfold tailWord_2807246
  simp only [CollatzResearch.WordTrace]
  refine ⟨12798584148479332036473199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68259115458556437527857061 12798584148479332036473199)
  ·
    refine ⟨19197876222718998054709799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12798584148479332036473199 19197876222718998054709799)
    ·
      refine ⟨28796814334078497082064699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19197876222718998054709799 28796814334078497082064699)
      ·
        refine ⟨43195221501117745623097049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28796814334078497082064699 43195221501117745623097049)
        ·
          refine ⟨32396416125838309217322787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43195221501117745623097049 32396416125838309217322787)
          ·
            refine ⟨48594624188757463825984181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32396416125838309217322787 48594624188757463825984181)
            ·
              refine ⟨4555746017696012233686017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48594624188757463825984181 4555746017696012233686017)
              ·
                refine ⟨3416809513272009175264513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4555746017696012233686017 3416809513272009175264513)
                ·
                  refine ⟨2562607134954006881448385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3416809513272009175264513 2562607134954006881448385)
                  ·
                    refine ⟨1921955351215505161086289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2562607134954006881448385 1921955351215505161086289)
                    ·
                      refine ⟨1441466513411628870814717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1921955351215505161086289 1441466513411628870814717)
                      ·
                        rfl

theorem cell23_2807246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_2807246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807246 prefixEnd_2807246 := by exact prefixLift 2807246
  have htrace : WordTrace (prefixWord ++ tailWord_2807246) baseStart_2807246 baseEnd_2807246 := by
    simpa [prefixWord, tailWord_2807246, baseEnd_2807246] using wordTrace_append hprefix tailTrace_2807246
  have hstable : (prefixWord ++ tailWord_2807246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807246).length < 2 ^ (prefixWord ++ tailWord_2807246).sum := by decide
  have hdescent : baseEnd_2807246 < baseStart_2807246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807265 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 1, 7]
def baseStart_2807265 : Nat := 118140960795 + 2807265 * 2 ^ 59
def prefixEnd_2807265 : Nat := 4983230072969 + 3 ^ 40 * 2807265 * 2
def baseEnd_2807265 : Nat := 480492089848021432159043

theorem tailTrace_2807265 : CollatzResearch.WordTrace tailWord_2807265 prefixEnd_2807265 480492089848021432159043 := by
  unfold tailWord_2807265
  simp only [CollatzResearch.WordTrace]
  refine ⟨102389366174765822536727249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68259577449843881691151499 102389366174765822536727249)
  ·
    refine ⟨76792024631074366902545437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102389366174765822536727249 76792024631074366902545437)
    ·
      refine ⟨28797009236652887588454539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76792024631074366902545437 28797009236652887588454539)
      ·
        refine ⟨43195513854979331382681809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28797009236652887588454539 43195513854979331382681809)
        ·
          refine ⟨32396635391234498537011357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43195513854979331382681809 32396635391234498537011357)
          ·
            refine ⟨12148738271712936951379259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32396635391234498537011357 12148738271712936951379259)
            ·
              refine ⟨18223107407569405427068889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12148738271712936951379259 18223107407569405427068889)
              ·
                refine ⟨13667330555677054070301667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18223107407569405427068889 13667330555677054070301667)
                ·
                  refine ⟨20500995833515581105452501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13667330555677054070301667 20500995833515581105452501)
                  ·
                    refine ⟨480492089848021432159043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20500995833515581105452501 480492089848021432159043)
                    ·
                      rfl

theorem cell23_2807265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_2807265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807265 prefixEnd_2807265 := by exact prefixLift 2807265
  have htrace : WordTrace (prefixWord ++ tailWord_2807265) baseStart_2807265 baseEnd_2807265 := by
    simpa [prefixWord, tailWord_2807265, baseEnd_2807265] using wordTrace_append hprefix tailTrace_2807265
  have hstable : (prefixWord ++ tailWord_2807265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807265).length < 2 ^ (prefixWord ++ tailWord_2807265).sum := by decide
  have hdescent : baseEnd_2807265 < baseStart_2807265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807282 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 1, 7]
def baseStart_2807282 : Nat := 118140960795 + 2807282 * 2 ^ 59
def prefixEnd_2807282 : Nat := 4983230072969 + 3 ^ 40 * 2807282 * 2
def baseEnd_2807282 : Nat := 480494999571730243321517

theorem tailTrace_2807282 : CollatzResearch.WordTrace tailWord_2807282 prefixEnd_2807282 480494999571730243321517 := by
  unfold tailWord_2807282
  simp only [CollatzResearch.WordTrace]
  refine ⟨25597496553926058610024025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68259990810469489626730733 25597496553926058610024025)
  ·
    refine ⟨19198122415444543957518019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25597496553926058610024025 19198122415444543957518019)
    ·
      refine ⟨28797183623166815936277029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19198122415444543957518019 28797183623166815936277029)
      ·
        refine ⟨5399471929343777988051943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28797183623166815936277029 5399471929343777988051943)
        ·
          refine ⟨8099207894015666982077915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5399471929343777988051943 8099207894015666982077915)
          ·
            refine ⟨12148811841023500473116873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8099207894015666982077915 12148811841023500473116873)
            ·
              refine ⟨9111608880767625354837655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12148811841023500473116873 9111608880767625354837655)
              ·
                refine ⟨13667413321151438032256483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9111608880767625354837655 13667413321151438032256483)
                ·
                  refine ⟨20501119981727157048384725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13667413321151438032256483 20501119981727157048384725)
                  ·
                    refine ⟨480494999571730243321517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20501119981727157048384725 480494999571730243321517)
                    ·
                      rfl

theorem cell23_2807282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_2807282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807282 prefixEnd_2807282 := by exact prefixLift 2807282
  have htrace : WordTrace (prefixWord ++ tailWord_2807282) baseStart_2807282 baseEnd_2807282 := by
    simpa [prefixWord, tailWord_2807282, baseEnd_2807282] using wordTrace_append hprefix tailTrace_2807282
  have hstable : (prefixWord ++ tailWord_2807282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807282).length < 2 ^ (prefixWord ++ tailWord_2807282).sum := by decide
  have hdescent : baseEnd_2807282 < baseStart_2807282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807286 : List Nat := [5, 1, 1, 1, 2, 4, 1, 3, 5]
def baseStart_2807286 : Nat := 118140960795 + 2807286 * 2 ^ 59
def prefixEnd_2807286 : Nat := 4983230072969 + 3 ^ 40 * 2807286 * 2
def baseEnd_2807286 : Nat := 160165228070867634923837

theorem tailTrace_2807286 : CollatzResearch.WordTrace tailWord_2807286 prefixEnd_2807286 160165228070867634923837 := by
  unfold tailWord_2807286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6399383256730608945202607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68260088071793162082161141 6399383256730608945202607)
  ·
    refine ⟨9599074885095913417803911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6399383256730608945202607 9599074885095913417803911)
    ·
      refine ⟨14398612327643870126705867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9599074885095913417803911 14398612327643870126705867)
      ·
        refine ⟨21597918491465805190058801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14398612327643870126705867 21597918491465805190058801)
        ·
          refine ⟨16198438868599353892544101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21597918491465805190058801 16198438868599353892544101)
          ·
            refine ⟨3037207287862378854852019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16198438868599353892544101 3037207287862378854852019)
            ·
              refine ⟨4555810931793568282278029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3037207287862378854852019 4555810931793568282278029)
              ·
                refine ⟨1708429099422588105854261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4555810931793568282278029 1708429099422588105854261)
                ·
                  refine ⟨160165228070867634923837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1708429099422588105854261 160165228070867634923837)
                  ·
                    rfl

theorem cell23_2807286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_2807286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807286 prefixEnd_2807286 := by exact prefixLift 2807286
  have htrace : WordTrace (prefixWord ++ tailWord_2807286) baseStart_2807286 baseEnd_2807286 := by
    simpa [prefixWord, tailWord_2807286, baseEnd_2807286] using wordTrace_append hprefix tailTrace_2807286
  have hstable : (prefixWord ++ tailWord_2807286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807286).length < 2 ^ (prefixWord ++ tailWord_2807286).sum := by decide
  have hdescent : baseEnd_2807286 < baseStart_2807286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807322 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3]
def baseStart_2807322 : Nat := 118140960795 + 2807322 * 2 ^ 59
def prefixEnd_2807322 : Nat := 4983230072969 + 3 ^ 40 * 2807322 * 2
def baseEnd_2807322 : Nat := 1441505537941370573464367

theorem tailTrace_2807322 : CollatzResearch.WordTrace tailWord_2807322 prefixEnd_2807322 1441505537941370573464367 := by
  unfold tailWord_2807322
  simp only [CollatzResearch.WordTrace]
  refine ⟨25597861283889830317888055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68260963423706214181034813 25597861283889830317888055)
  ·
    refine ⟨38396791925834745476832083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25597861283889830317888055 38396791925834745476832083)
    ·
      refine ⟨57595187888752118215248125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38396791925834745476832083 57595187888752118215248125)
      ·
        refine ⟨21598195458282044330718047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57595187888752118215248125 21598195458282044330718047)
        ·
          refine ⟨32397293187423066496077071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21598195458282044330718047 32397293187423066496077071)
          ·
            refine ⟨48595939781134599744115607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32397293187423066496077071 48595939781134599744115607)
            ·
              refine ⟨72893909671701899616173411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48595939781134599744115607 72893909671701899616173411)
              ·
                refine ⟨109340864507552849424260117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72893909671701899616173411 109340864507552849424260117)
                ·
                  refine ⟨5125353023791539816762193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109340864507552849424260117 5125353023791539816762193)
                  ·
                    refine ⟨3844014767843654862571645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5125353023791539816762193 3844014767843654862571645)
                    ·
                      refine ⟨1441505537941370573464367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3844014767843654862571645 1441505537941370573464367)
                      ·
                        rfl

theorem cell23_2807322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_2807322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807322 prefixEnd_2807322 := by exact prefixLift 2807322
  have htrace : WordTrace (prefixWord ++ tailWord_2807322) baseStart_2807322 baseEnd_2807322 := by
    simpa [prefixWord, tailWord_2807322, baseEnd_2807322] using wordTrace_append hprefix tailTrace_2807322
  have hstable : (prefixWord ++ tailWord_2807322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807322).length < 2 ^ (prefixWord ++ tailWord_2807322).sum := by decide
  have hdescent : baseEnd_2807322 < baseStart_2807322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807336 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2807336 : Nat := 118140960795 + 2807336 * 2 ^ 59
def prefixEnd_2807336 : Nat := 4983230072969 + 3 ^ 40 * 2807336 * 2
def baseEnd_2807336 : Nat := 1441512726670533518689303

theorem tailTrace_2807336 : CollatzResearch.WordTrace tailWord_2807336 prefixEnd_2807336 1441512726670533518689303 := by
  unfold tailWord_2807336
  simp only [CollatzResearch.WordTrace]
  refine ⟨51195977878754300831280931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68261303838339067775041241 51195977878754300831280931)
  ·
    refine ⟨76793966818131451246921397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51195977878754300831280931 76793966818131451246921397)
    ·
      refine ⟨7199434389199823554398881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76793966818131451246921397 7199434389199823554398881)
      ·
        refine ⟨5399575791899867665799161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7199434389199823554398881 5399575791899867665799161)
        ·
          refine ⟨4049681843924900749349371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5399575791899867665799161 4049681843924900749349371)
          ·
            refine ⟨6074522765887351124024057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4049681843924900749349371 6074522765887351124024057)
            ·
              refine ⟨4555892074415513343018043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6074522765887351124024057 4555892074415513343018043)
              ·
                refine ⟨6833838111623270014527065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555892074415513343018043 6833838111623270014527065)
                ·
                  refine ⟨5125378583717452510895299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6833838111623270014527065 5125378583717452510895299)
                  ·
                    refine ⟨7688067875576178766342949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5125378583717452510895299 7688067875576178766342949)
                    ·
                      refine ⟨1441512726670533518689303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7688067875576178766342949 1441512726670533518689303)
                      ·
                        rfl

theorem cell23_2807336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2807336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807336 prefixEnd_2807336 := by exact prefixLift 2807336
  have htrace : WordTrace (prefixWord ++ tailWord_2807336) baseStart_2807336 baseEnd_2807336 := by
    simpa [prefixWord, tailWord_2807336, baseEnd_2807336] using wordTrace_append hprefix tailTrace_2807336
  have hstable : (prefixWord ++ tailWord_2807336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807336).length < 2 ^ (prefixWord ++ tailWord_2807336).sum := by decide
  have hdescent : baseEnd_2807336 < baseStart_2807336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807345 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 8]
def baseStart_2807345 : Nat := 118140960795 + 2807345 * 2 ^ 59
def prefixEnd_2807345 : Nat := 4983230072969 + 3 ^ 40 * 2807345 * 2
def baseEnd_2807345 : Nat := 1441517347996423983476761

theorem tailTrace_2807345 : CollatzResearch.WordTrace tailWord_2807345 prefixEnd_2807345 1441517347996423983476761 := by
  unfold tailWord_2807345
  simp only [CollatzResearch.WordTrace]
  refine ⟨102392284014475996199639489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68261522676317330799759659 102392284014475996199639489)
  ·
    refine ⟨76794213010856997149729617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102392284014475996199639489 76794213010856997149729617)
    ·
      refine ⟨57595659758142747862297213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76794213010856997149729617 57595659758142747862297213)
      ·
        refine ⟨21598372409303530448361455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57595659758142747862297213 21598372409303530448361455)
        ·
          refine ⟨32397558613955295672542183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21598372409303530448361455 32397558613955295672542183)
          ·
            refine ⟨48596337920932943508813275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32397558613955295672542183 48596337920932943508813275)
            ·
              refine ⟨72894506881399415263219913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48596337920932943508813275 72894506881399415263219913)
              ·
                refine ⟨54670880161049561447414935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72894506881399415263219913 54670880161049561447414935)
                ·
                  refine ⟨82006320241574342171122403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54670880161049561447414935 82006320241574342171122403)
                  ·
                    refine ⟨123009480362361513256683605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82006320241574342171122403 123009480362361513256683605)
                    ·
                      refine ⟨1441517347996423983476761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 123009480362361513256683605 1441517347996423983476761)
                      ·
                        rfl

theorem cell23_2807345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_2807345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807345 prefixEnd_2807345 := by exact prefixLift 2807345
  have htrace : WordTrace (prefixWord ++ tailWord_2807345) baseStart_2807345 baseEnd_2807345 := by
    simpa [prefixWord, tailWord_2807345, baseEnd_2807345] using wordTrace_append hprefix tailTrace_2807345
  have hstable : (prefixWord ++ tailWord_2807345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807345).length < 2 ^ (prefixWord ++ tailWord_2807345).sum := by decide
  have hdescent : baseEnd_2807345 < baseStart_2807345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807372 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 3, 5]
def baseStart_2807372 : Nat := 118140960795 + 2807372 * 2 ^ 59
def prefixEnd_2807372 : Nat := 4983230072969 + 3 ^ 40 * 2807372 * 2
def baseEnd_2807372 : Nat := 480510403991365125946379

theorem tailTrace_2807372 : CollatzResearch.WordTrace tailWord_2807372 prefixEnd_2807372 480510403991365125946379 := by
  unfold tailWord_2807372
  simp only [CollatzResearch.WordTrace]
  refine ⟨51196634392689089905436185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68262179190252119873914913 51196634392689089905436185)
  ·
    refine ⟨38397475794516817429077139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51196634392689089905436185 38397475794516817429077139)
    ·
      refine ⟨57596213691775226143615709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38397475794516817429077139 57596213691775226143615709)
      ·
        refine ⟨21598580134415709803855891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57596213691775226143615709 21598580134415709803855891)
        ·
          refine ⟨32397870201623564705783837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21598580134415709803855891 32397870201623564705783837)
          ·
            refine ⟨12149201325608836764668939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32397870201623564705783837 12149201325608836764668939)
            ·
              refine ⟨18223801988413255147003409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12149201325608836764668939 18223801988413255147003409)
              ·
                refine ⟨13667851491309941360252557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18223801988413255147003409 13667851491309941360252557)
                ·
                  refine ⟨5125444309241228010094709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13667851491309941360252557 5125444309241228010094709)
                  ·
                    refine ⟨480510403991365125946379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5125444309241228010094709 480510403991365125946379)
                    ·
                      rfl

theorem cell23_2807372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_2807372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807372 prefixEnd_2807372 := by exact prefixLift 2807372
  have htrace : WordTrace (prefixWord ++ tailWord_2807372) baseStart_2807372 baseEnd_2807372 := by
    simpa [prefixWord, tailWord_2807372, baseEnd_2807372] using wordTrace_append hprefix tailTrace_2807372
  have hstable : (prefixWord ++ tailWord_2807372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807372).length < 2 ^ (prefixWord ++ tailWord_2807372).sum := by decide
  have hdescent : baseEnd_2807372 < baseStart_2807372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807396 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 2, 3, 2]
def baseStart_2807396 : Nat := 118140960795 + 2807396 * 2 ^ 59
def prefixEnd_2807396 : Nat := 4983230072969 + 3 ^ 40 * 2807396 * 2
def baseEnd_2807396 : Nat := 1441543535509803283939027

theorem tailTrace_2807396 : CollatzResearch.WordTrace tailWord_2807396 prefixEnd_2807396 1441543535509803283939027 := by
  unfold tailWord_2807396
  simp only [CollatzResearch.WordTrace]
  refine ⟨51197072068645615954873021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68262762758194154606497361 51197072068645615954873021)
  ·
    refine ⟨19198902025742105983077383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51197072068645615954873021 19198902025742105983077383)
    ·
      refine ⟨28798353038613158974616075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19198902025742105983077383 28798353038613158974616075)
      ·
        refine ⟨43197529557919738461924113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28798353038613158974616075 43197529557919738461924113)
        ·
          refine ⟨32398147168439803846443085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43197529557919738461924113 32398147168439803846443085)
          ·
            refine ⟨12149305188164926442416157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32398147168439803846443085 12149305188164926442416157)
            ·
              refine ⟨4555989445561847415906059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12149305188164926442416157 4555989445561847415906059)
              ·
                refine ⟨6833984168342771123859089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555989445561847415906059 6833984168342771123859089)
                ·
                  refine ⟨5125488126257078342894317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6833984168342771123859089 5125488126257078342894317)
                  ·
                    refine ⟨1922058047346404378585369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5125488126257078342894317 1922058047346404378585369)
                    ·
                      refine ⟨1441543535509803283939027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1922058047346404378585369 1441543535509803283939027)
                      ·
                        rfl

theorem cell23_2807396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_2807396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807396 prefixEnd_2807396 := by exact prefixLift 2807396
  have htrace : WordTrace (prefixWord ++ tailWord_2807396) baseStart_2807396 baseEnd_2807396 := by
    simpa [prefixWord, tailWord_2807396, baseEnd_2807396] using wordTrace_append hprefix tailTrace_2807396
  have hstable : (prefixWord ++ tailWord_2807396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807396).length < 2 ^ (prefixWord ++ tailWord_2807396).sum := by decide
  have hdescent : baseEnd_2807396 < baseStart_2807396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807406 : List Nat := [4, 1, 2, 2, 3, 1, 1, 3, 1, 5]
def baseStart_2807406 : Nat := 118140960795 + 2807406 * 2 ^ 59
def prefixEnd_2807406 : Nat := 4983230072969 + 3 ^ 40 * 2807406 * 2
def baseEnd_2807406 : Nat := 480516223438782748271327

theorem tailTrace_2807406 : CollatzResearch.WordTrace tailWord_2807406 prefixEnd_2807406 480516223438782748271327 := by
  unfold tailWord_2807406
  simp only [CollatzResearch.WordTrace]
  refine ⟨12799313608406875452201259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68263005911503335745073381 12799313608406875452201259)
  ·
    refine ⟨19198970412610313178301889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12799313608406875452201259 19198970412610313178301889)
    ·
      refine ⟨14399227809457734883726417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19198970412610313178301889 14399227809457734883726417)
      ·
        refine ⟨10799420857093301162794813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14399227809457734883726417 10799420857093301162794813)
        ·
          refine ⟨4049782821409987936048055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10799420857093301162794813 4049782821409987936048055)
          ·
            refine ⟨6074674232114981904072083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4049782821409987936048055 6074674232114981904072083)
            ·
              refine ⟨9112011348172472856108125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6074674232114981904072083 9112011348172472856108125)
              ·
                refine ⟨3417004255564677321040547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9112011348172472856108125 3417004255564677321040547)
                ·
                  refine ⟨5125506383347015981560821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3417004255564677321040547 5125506383347015981560821)
                  ·
                    refine ⟨480516223438782748271327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5125506383347015981560821 480516223438782748271327)
                    ·
                      rfl

theorem cell23_2807406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_2807406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807406 prefixEnd_2807406 := by exact prefixLift 2807406
  have htrace : WordTrace (prefixWord ++ tailWord_2807406) baseStart_2807406 baseEnd_2807406 := by
    simpa [prefixWord, tailWord_2807406, baseEnd_2807406] using wordTrace_append hprefix tailTrace_2807406
  have hstable : (prefixWord ++ tailWord_2807406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807406).length < 2 ^ (prefixWord ++ tailWord_2807406).sum := by decide
  have hdescent : baseEnd_2807406 < baseStart_2807406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807436 : List Nat := [2, 2, 1, 2, 1, 1, 7, 1, 2, 4]
def baseStart_2807436 : Nat := 118140960795 + 2807436 * 2 ^ 59
def prefixEnd_2807436 : Nat := 4983230072969 + 3 ^ 40 * 2807436 * 2
def baseEnd_2807436 : Nat := 480521358245327709146281

theorem tailTrace_2807436 : CollatzResearch.WordTrace tailWord_2807436 prefixEnd_2807436 480521358245327709146281 := by
  unfold tailWord_2807436
  simp only [CollatzResearch.WordTrace]
  refine ⟨51197801528573159370601081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68263735371430879160801441 51197801528573159370601081)
  ·
    refine ⟨38398351146429869527950811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51197801528573159370601081 38398351146429869527950811)
    ·
      refine ⟨57597526719644804291926217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38398351146429869527950811 57597526719644804291926217)
      ·
        refine ⟨43198145039733603218944663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57597526719644804291926217 43198145039733603218944663)
        ·
          refine ⟨64797217559600404828416995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43198145039733603218944663 64797217559600404828416995)
          ·
            refine ⟨97195826339400607242625493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64797217559600404828416995 97195826339400607242625493)
            ·
              refine ⟨2278027179829701732249035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 97195826339400607242625493 2278027179829701732249035)
              ·
                refine ⟨3417040769744552598373553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278027179829701732249035 3417040769744552598373553)
                ·
                  refine ⟨2562780577308414448780165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3417040769744552598373553 2562780577308414448780165)
                  ·
                    refine ⟨480521358245327709146281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2562780577308414448780165 480521358245327709146281)
                    ·
                      rfl

theorem cell23_2807436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_2807436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807436 prefixEnd_2807436 := by exact prefixLift 2807436
  have htrace : WordTrace (prefixWord ++ tailWord_2807436) baseStart_2807436 baseEnd_2807436 := by
    simpa [prefixWord, tailWord_2807436, baseEnd_2807436] using wordTrace_append hprefix tailTrace_2807436
  have hstable : (prefixWord ++ tailWord_2807436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807436).length < 2 ^ (prefixWord ++ tailWord_2807436).sum := by decide
  have hdescent : baseEnd_2807436 < baseStart_2807436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807459 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 6, 1, 3]
def baseStart_2807459 : Nat := 118140960795 + 2807459 * 2 ^ 59
def prefixEnd_2807459 : Nat := 4983230072969 + 3 ^ 40 * 2807459 * 2
def baseEnd_2807459 : Nat := 1441575884791036537451237

theorem tailTrace_2807459 : CollatzResearch.WordTrace tailWord_2807459 prefixEnd_2807459 1441575884791036537451237 := by
  unfold tailWord_2807459
  simp only [CollatzResearch.WordTrace]
  refine ⟨102396441936062993669289431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68264294624041995779526287 102396441936062993669289431)
  ·
    refine ⟨153594662904094490503934147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102396441936062993669289431 153594662904094490503934147)
    ·
      refine ⟨230391994356141735755901221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153594662904094490503934147 230391994356141735755901221)
      ·
        refine ⟨43198498941776575454231479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230391994356141735755901221 43198498941776575454231479)
        ·
          refine ⟨64797748412664863181347219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43198498941776575454231479 64797748412664863181347219)
          ·
            refine ⟨97196622618997294772020829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64797748412664863181347219 97196622618997294772020829)
            ·
              refine ⟨36448733482123985539507811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97196622618997294772020829 36448733482123985539507811)
              ·
                refine ⟨54673100223185978309261717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36448733482123985539507811 54673100223185978309261717)
                ·
                  refine ⟨2562801572961842733246643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54673100223185978309261717 2562801572961842733246643)
                  ·
                    refine ⟨3844202359442764099869965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2562801572961842733246643 3844202359442764099869965)
                    ·
                      refine ⟨1441575884791036537451237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3844202359442764099869965 1441575884791036537451237)
                      ·
                        rfl

theorem cell23_2807459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_2807459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807459 prefixEnd_2807459 := by exact prefixLift 2807459
  have htrace : WordTrace (prefixWord ++ tailWord_2807459) baseStart_2807459 baseEnd_2807459 := by
    simpa [prefixWord, tailWord_2807459, baseEnd_2807459] using wordTrace_append hprefix tailTrace_2807459
  have hstable : (prefixWord ++ tailWord_2807459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807459).length < 2 ^ (prefixWord ++ tailWord_2807459).sum := by decide
  have hdescent : baseEnd_2807459 < baseStart_2807459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807460 : List Nat := [2, 3, 1, 2, 2, 2, 3, 3, 1, 2, 2]
def baseStart_2807460 : Nat := 118140960795 + 2807460 * 2 ^ 59
def prefixEnd_2807460 : Nat := 4983230072969 + 3 ^ 40 * 2807460 * 2
def baseEnd_2807460 : Nat := 1441576398271691033538733

theorem tailTrace_2807460 : CollatzResearch.WordTrace tailWord_2807460 prefixEnd_2807460 1441576398271691033538733 := by
  unfold tailWord_2807460
  simp only [CollatzResearch.WordTrace]
  refine ⟨51198239204529685420037917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68264318939372913893383889 51198239204529685420037917)
  ·
    refine ⟨19199339701698632032514219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51198239204529685420037917 19199339701698632032514219)
    ·
      refine ⟨28799009552547948048771329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19199339701698632032514219 28799009552547948048771329)
      ·
        refine ⟨21599257164410961036578497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28799009552547948048771329 21599257164410961036578497)
        ·
          refine ⟨16199442873308220777433873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21599257164410961036578497 16199442873308220777433873)
          ·
            refine ⟨12149582154981165583075405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16199442873308220777433873 12149582154981165583075405)
            ·
              refine ⟨4556093308117937093653277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12149582154981165583075405 4556093308117937093653277)
              ·
                refine ⟨1708534990544226410119979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4556093308117937093653277 1708534990544226410119979)
                ·
                  refine ⟨2562802485816339615179969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1708534990544226410119979 2562802485816339615179969)
                  ·
                    refine ⟨1922101864362254711384977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2562802485816339615179969 1922101864362254711384977)
                    ·
                      refine ⟨1441576398271691033538733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1922101864362254711384977 1441576398271691033538733)
                      ·
                        rfl

theorem cell23_2807460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_2807460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807460 prefixEnd_2807460 := by exact prefixLift 2807460
  have htrace : WordTrace (prefixWord ++ tailWord_2807460) baseStart_2807460 baseEnd_2807460 := by
    simpa [prefixWord, tailWord_2807460, baseEnd_2807460] using wordTrace_append hprefix tailTrace_2807460
  have hstable : (prefixWord ++ tailWord_2807460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807460).length < 2 ^ (prefixWord ++ tailWord_2807460).sum := by decide
  have hdescent : baseEnd_2807460 < baseStart_2807460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807477 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 3, 2, 2]
def baseStart_2807477 : Nat := 118140960795 + 2807477 * 2 ^ 59
def prefixEnd_2807477 : Nat := 4983230072969 + 3 ^ 40 * 2807477 * 2
def baseEnd_2807477 : Nat := 1441585127442817467026155

theorem tailTrace_2807477 : CollatzResearch.WordTrace tailWord_2807477 prefixEnd_2807477 1441585127442817467026155 := by
  unfold tailWord_2807477
  simp only [CollatzResearch.WordTrace]
  refine ⟨102397098449997782743444685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68264732299998521828963123 102397098449997782743444685)
  ·
    refine ⟨38398911918749168528791757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102397098449997782743444685 38398911918749168528791757)
    ·
      refine ⟨14399591969530938198296909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38398911918749168528791757 14399591969530938198296909)
      ·
        refine ⟨5399846988574101824361341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14399591969530938198296909 5399846988574101824361341)
        ·
          refine ⟨2024942620715288184135503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5399846988574101824361341 2024942620715288184135503)
          ·
            refine ⟨3037413931072932276203255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024942620715288184135503 3037413931072932276203255)
            ·
              refine ⟨4556120896609398414304883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3037413931072932276203255 4556120896609398414304883)
              ·
                refine ⟨6834181344914097621457325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4556120896609398414304883 6834181344914097621457325)
                ·
                  refine ⟨2562818004342786608046497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6834181344914097621457325 2562818004342786608046497)
                  ·
                    refine ⟨1922113503257089956034873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2562818004342786608046497 1922113503257089956034873)
                    ·
                      refine ⟨1441585127442817467026155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1922113503257089956034873 1441585127442817467026155)
                      ·
                        rfl

theorem cell23_2807477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_2807477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807477 prefixEnd_2807477 := by exact prefixLift 2807477
  have htrace : WordTrace (prefixWord ++ tailWord_2807477) baseStart_2807477 baseEnd_2807477 := by
    simpa [prefixWord, tailWord_2807477, baseEnd_2807477] using wordTrace_append hprefix tailTrace_2807477
  have hstable : (prefixWord ++ tailWord_2807477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807477).length < 2 ^ (prefixWord ++ tailWord_2807477).sum := by decide
  have hdescent : baseEnd_2807477 < baseStart_2807477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807499 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 5, 4, 2]
def baseStart_2807499 : Nat := 118140960795 + 2807499 * 2 ^ 59
def prefixEnd_2807499 : Nat := 4983230072969 + 3 ^ 40 * 2807499 * 2
def baseEnd_2807499 : Nat := 1441596424017216380951053

theorem tailTrace_2807499 : CollatzResearch.WordTrace tailWord_2807499 prefixEnd_2807499 1441596424017216380951053 := by
  unfold tailWord_2807499
  simp only [CollatzResearch.WordTrace]
  refine ⟨102397900855918080500745551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68265267237278720333830367 102397900855918080500745551)
  ·
    refine ⟨153596851283877120751118327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102397900855918080500745551 153596851283877120751118327)
    ·
      refine ⟨230395276925815681126677491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153596851283877120751118327 230395276925815681126677491)
      ·
        refine ⟨345592915388723521690016237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230395276925815681126677491 345592915388723521690016237)
        ·
          refine ⟨129597343270771320633756089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345592915388723521690016237 129597343270771320633756089)
          ·
            refine ⟨97198007453078490475317067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129597343270771320633756089 97198007453078490475317067)
            ·
              refine ⟨145797011179617735712975601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97198007453078490475317067 145797011179617735712975601)
              ·
                refine ⟨109347758384713301784731701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145797011179617735712975601 109347758384713301784731701)
                ·
                  refine ⟨10251352348566872042318597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109347758384713301784731701 10251352348566872042318597)
                  ·
                    refine ⟨1922128565356288507934737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10251352348566872042318597 1922128565356288507934737)
                    ·
                      refine ⟨1441596424017216380951053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1922128565356288507934737 1441596424017216380951053)
                      ·
                        rfl

theorem cell23_2807499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 4, 2].length) (baseStart_2807499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807499 prefixEnd_2807499 := by exact prefixLift 2807499
  have htrace : WordTrace (prefixWord ++ tailWord_2807499) baseStart_2807499 baseEnd_2807499 := by
    simpa [prefixWord, tailWord_2807499, baseEnd_2807499] using wordTrace_append hprefix tailTrace_2807499
  have hstable : (prefixWord ++ tailWord_2807499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807499).length < 2 ^ (prefixWord ++ tailWord_2807499).sum := by decide
  have hdescent : baseEnd_2807499 < baseStart_2807499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807510 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2807510 : Nat := 118140960795 + 2807510 * 2 ^ 59
def prefixEnd_2807510 : Nat := 4983230072969 + 3 ^ 40 * 2807510 * 2
def baseEnd_2807510 : Nat := 1441602072304415837913503

theorem tailTrace_2807510 : CollatzResearch.WordTrace tailWord_2807510 prefixEnd_2807510 1441602072304415837913503 := by
  unfold tailWord_2807510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6399893878679889336212249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68265534705918819586263989 6399893878679889336212249)
  ·
    refine ⟨4799920409009917002159187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6399893878679889336212249 4799920409009917002159187)
    ·
      refine ⟨7199880613514875503238781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4799920409009917002159187 7199880613514875503238781)
      ·
        refine ⟨2699955230068078313714543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7199880613514875503238781 2699955230068078313714543)
        ·
          refine ⟨4049932845102117470571815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2699955230068078313714543 4049932845102117470571815)
          ·
            refine ⟨6074899267653176205857723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4049932845102117470571815 6074899267653176205857723)
            ·
              refine ⟨9112348901479764308786585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6074899267653176205857723 9112348901479764308786585)
              ·
                refine ⟨6834261676109823231589939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9112348901479764308786585 6834261676109823231589939)
                ·
                  refine ⟨10251392514164734847384909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6834261676109823231589939 10251392514164734847384909)
                  ·
                    refine ⟨3844272192811775567769341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10251392514164734847384909 3844272192811775567769341)
                    ·
                      refine ⟨1441602072304415837913503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3844272192811775567769341 1441602072304415837913503)
                      ·
                        rfl

theorem cell23_2807510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2807510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807510 prefixEnd_2807510 := by exact prefixLift 2807510
  have htrace : WordTrace (prefixWord ++ tailWord_2807510) baseStart_2807510 baseEnd_2807510 := by
    simpa [prefixWord, tailWord_2807510, baseEnd_2807510] using wordTrace_append hprefix tailTrace_2807510
  have hstable : (prefixWord ++ tailWord_2807510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807510).length < 2 ^ (prefixWord ++ tailWord_2807510).sum := by decide
  have hdescent : baseEnd_2807510 < baseStart_2807510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807532 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 7]
def baseStart_2807532 : Nat := 118140960795 + 2807532 * 2 ^ 59
def prefixEnd_2807532 : Nat := 4983230072969 + 3 ^ 40 * 2807532 * 2
def baseEnd_2807532 : Nat := 1441613368878814751838401

theorem tailTrace_2807532 : CollatzResearch.WordTrace tailWord_2807532 prefixEnd_2807532 1441613368878814751838401 := by
  unfold tailWord_2807532
  simp only [CollatzResearch.WordTrace]
  refine ⟨51199552232399263568348425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68266069643199018091131233 51199552232399263568348425)
  ·
    refine ⟨38399664174299447676261319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51199552232399263568348425 38399664174299447676261319)
    ·
      refine ⟨57599496261449171514391979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38399664174299447676261319 57599496261449171514391979)
      ·
        refine ⟨86399244392173757271587969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57599496261449171514391979 86399244392173757271587969)
        ·
          refine ⟨64799433294130317953690977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86399244392173757271587969 64799433294130317953690977)
          ·
            refine ⟨48599574970597738465268233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64799433294130317953690977 48599574970597738465268233)
            ·
              refine ⟨36449681227948303848951175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48599574970597738465268233 36449681227948303848951175)
              ·
                refine ⟨54674521841922455773426763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36449681227948303848951175 54674521841922455773426763)
                ·
                  refine ⟨82011782762883683660140145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54674521841922455773426763 82011782762883683660140145)
                  ·
                    refine ⟨61508837072162762745105109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82011782762883683660140145 61508837072162762745105109)
                    ·
                      refine ⟨1441613368878814751838401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61508837072162762745105109 1441613368878814751838401)
                      ·
                        rfl

theorem cell23_2807532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_2807532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807532 prefixEnd_2807532 := by exact prefixLift 2807532
  have htrace : WordTrace (prefixWord ++ tailWord_2807532) baseStart_2807532 baseEnd_2807532 := by
    simpa [prefixWord, tailWord_2807532, baseEnd_2807532] using wordTrace_append hprefix tailTrace_2807532
  have hstable : (prefixWord ++ tailWord_2807532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807532).length < 2 ^ (prefixWord ++ tailWord_2807532).sum := by decide
  have hdescent : baseEnd_2807532 < baseStart_2807532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807550 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_2807550 : Nat := 118140960795 + 2807550 * 2 ^ 59
def prefixEnd_2807550 : Nat := 4983230072969 + 3 ^ 40 * 2807550 * 2
def baseEnd_2807550 : Nat := 1441622611530595681413319

theorem tailTrace_2807550 : CollatzResearch.WordTrace tailWord_2807550 prefixEnd_2807550 1441622611530595681413319 := by
  unfold tailWord_2807550
  simp only [CollatzResearch.WordTrace]
  refine ⟨12799970122341664526356513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68266507319155544140568069 12799970122341664526356513)
  ·
    refine ⟨9599977591756248394767385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12799970122341664526356513 9599977591756248394767385)
    ·
      refine ⟨7199983193817186296075539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9599977591756248394767385 7199983193817186296075539)
      ·
        refine ⟨10799974790725779444113309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7199983193817186296075539 10799974790725779444113309)
        ·
          refine ⟨4049990546522167291542491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10799974790725779444113309 4049990546522167291542491)
          ·
            refine ⟨6074985819783250937313737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4049990546522167291542491 6074985819783250937313737)
            ·
              refine ⟨4556239364837438202985303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6074985819783250937313737 4556239364837438202985303)
              ·
                refine ⟨6834359047256157304477955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4556239364837438202985303 6834359047256157304477955)
                ·
                  refine ⟨10251538570884235956716933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6834359047256157304477955 10251538570884235956716933)
                  ·
                    refine ⟨1922163482040794241884425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10251538570884235956716933 1922163482040794241884425)
                    ·
                      refine ⟨1441622611530595681413319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1922163482040794241884425 1441622611530595681413319)
                      ·
                        rfl

theorem cell23_2807550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_2807550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807550 prefixEnd_2807550 := by exact prefixLift 2807550
  have htrace : WordTrace (prefixWord ++ tailWord_2807550) baseStart_2807550 baseEnd_2807550 := by
    simpa [prefixWord, tailWord_2807550, baseEnd_2807550] using wordTrace_append hprefix tailTrace_2807550
  have hstable : (prefixWord ++ tailWord_2807550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807550).length < 2 ^ (prefixWord ++ tailWord_2807550).sum := by decide
  have hdescent : baseEnd_2807550 < baseStart_2807550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807552 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 3, 7]
def baseStart_2807552 : Nat := 118140960795 + 2807552 * 2 ^ 59
def prefixEnd_2807552 : Nat := 4983230072969 + 3 ^ 40 * 2807552 * 2
def baseEnd_2807552 : Nat := 480541212830634891196103

theorem tailTrace_2807552 : CollatzResearch.WordTrace tailWord_2807552 prefixEnd_2807552 480541212830634891196103 := by
  unfold tailWord_2807552
  simp only [CollatzResearch.WordTrace]
  refine ⟨51199916962363035276212455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68266555949817380368283273 51199916962363035276212455)
  ·
    refine ⟨76799875443544552914318683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51199916962363035276212455 76799875443544552914318683)
    ·
      refine ⟨115199813165316829371478025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76799875443544552914318683 115199813165316829371478025)
      ·
        refine ⟨86399859873987622028608519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115199813165316829371478025 86399859873987622028608519)
        ·
          refine ⟨129599789810981433042912779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86399859873987622028608519 129599789810981433042912779)
          ·
            refine ⟨194399684716472149564369169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129599789810981433042912779 194399684716472149564369169)
            ·
              refine ⟨145799763537354112173276877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194399684716472149564369169 145799763537354112173276877)
              ·
                refine ⟨54674911326507792064978829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145799763537354112173276877 54674911326507792064978829)
                ·
                  refine ⟨20503091747440422024367061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54674911326507792064978829 20503091747440422024367061)
                  ·
                    refine ⟨480541212830634891196103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20503091747440422024367061 480541212830634891196103)
                    ·
                      rfl

theorem cell23_2807552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 7].length) (baseStart_2807552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807552 prefixEnd_2807552 := by exact prefixLift 2807552
  have htrace : WordTrace (prefixWord ++ tailWord_2807552) baseStart_2807552 baseEnd_2807552 := by
    simpa [prefixWord, tailWord_2807552, baseEnd_2807552] using wordTrace_append hprefix tailTrace_2807552
  have hstable : (prefixWord ++ tailWord_2807552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807552).length < 2 ^ (prefixWord ++ tailWord_2807552).sum := by decide
  have hdescent : baseEnd_2807552 < baseStart_2807552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807599 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 7, 4]
def baseStart_2807599 : Nat := 118140960795 + 2807599 * 2 ^ 59
def prefixEnd_2807599 : Nat := 4983230072969 + 3 ^ 40 * 2807599 * 2
def baseEnd_2807599 : Nat := 480549257360888663233531

theorem tailTrace_2807599 : CollatzResearch.WordTrace tailWord_2807599 prefixEnd_2807599 480549257360888663233531 := by
  unfold tailWord_2807599
  simp only [CollatzResearch.WordTrace]
  refine ⟨102401548155555797579385851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68267698770370531719590567 102401548155555797579385851)
  ·
    refine ⟨153602322233333696369078777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102401548155555797579385851 153602322233333696369078777)
    ·
      refine ⟨115201741675000272276809083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153602322233333696369078777 115201741675000272276809083)
      ·
        refine ⟨172802612512500408415213625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115201741675000272276809083 172802612512500408415213625)
        ·
          refine ⟨129601959384375306311410219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172802612512500408415213625 129601959384375306311410219)
          ·
            refine ⟨194402939076562959467115329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129601959384375306311410219 194402939076562959467115329)
            ·
              refine ⟨145802204307422219600336497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194402939076562959467115329 145802204307422219600336497)
              ·
                refine ⟨109351653230566664700252373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145802204307422219600336497 109351653230566664700252373)
                ·
                  refine ⟨2562929372591406203912165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 109351653230566664700252373 2562929372591406203912165)
                  ·
                    refine ⟨480549257360888663233531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2562929372591406203912165 480549257360888663233531)
                    ·
                      rfl

theorem cell23_2807599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 4].length) (baseStart_2807599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807599 prefixEnd_2807599 := by exact prefixLift 2807599
  have htrace : WordTrace (prefixWord ++ tailWord_2807599) baseStart_2807599 baseEnd_2807599 := by
    simpa [prefixWord, tailWord_2807599, baseEnd_2807599] using wordTrace_append hprefix tailTrace_2807599
  have hstable : (prefixWord ++ tailWord_2807599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807599).length < 2 ^ (prefixWord ++ tailWord_2807599).sum := by decide
  have hdescent : baseEnd_2807599 < baseStart_2807599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807626 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 2, 2, 3]
def baseStart_2807626 : Nat := 118140960795 + 2807626 * 2 ^ 59
def prefixEnd_2807626 : Nat := 4983230072969 + 3 ^ 40 * 2807626 * 2
def baseEnd_2807626 : Nat := 1441661636060337384062969

theorem tailTrace_2807626 : CollatzResearch.WordTrace tailWord_2807626 prefixEnd_2807626 1441661636060337384062969 := by
  unfold tailWord_2807626
  simp only [CollatzResearch.WordTrace]
  refine ⟨25600633231614495297654683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68268355284305320793745821 25600633231614495297654683)
  ·
    refine ⟨38400949847421742946482025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25600633231614495297654683 38400949847421742946482025)
    ·
      refine ⟨28800712385566307209861519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38400949847421742946482025 28800712385566307209861519)
      ·
        refine ⟨43201068578349460814792279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28800712385566307209861519 43201068578349460814792279)
        ·
          refine ⟨64801602867524191222188419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43201068578349460814792279 64801602867524191222188419)
          ·
            refine ⟨97202404301286286833282629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64801602867524191222188419 97202404301286286833282629)
            ·
              refine ⟨18225450806491178781240493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97202404301286286833282629 18225450806491178781240493)
              ·
                refine ⟨6834544052434192042965185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18225450806491178781240493 6834544052434192042965185)
                ·
                  refine ⟨5125908039325644032223889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6834544052434192042965185 5125908039325644032223889)
                  ·
                    refine ⟨3844431029494233024167917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5125908039325644032223889 3844431029494233024167917)
                    ·
                      refine ⟨1441661636060337384062969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3844431029494233024167917 1441661636060337384062969)
                      ·
                        rfl

theorem cell23_2807626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_2807626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807626 prefixEnd_2807626 := by exact prefixLift 2807626
  have htrace : WordTrace (prefixWord ++ tailWord_2807626) baseStart_2807626 baseEnd_2807626 := by
    simpa [prefixWord, tailWord_2807626, baseEnd_2807626] using wordTrace_append hprefix tailTrace_2807626
  have hstable : (prefixWord ++ tailWord_2807626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807626).length < 2 ^ (prefixWord ++ tailWord_2807626).sum := by decide
  have hdescent : baseEnd_2807626 < baseStart_2807626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807650 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_2807650 : Nat := 118140960795 + 2807650 * 2 ^ 59
def prefixEnd_2807650 : Nat := 4983230072969 + 3 ^ 40 * 2807650 * 2
def baseEnd_2807650 : Nat := 480557986532015096720953

theorem tailTrace_2807650 : CollatzResearch.WordTrace tailWord_2807650 prefixEnd_2807650 480557986532015096720953 := by
  unfold tailWord_2807650
  simp only [CollatzResearch.WordTrace]
  refine ⟨25600852069592758322373101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68268938852247355526328269 25600852069592758322373101)
  ·
    refine ⟨9600319526097284370889913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25600852069592758322373101 9600319526097284370889913)
    ·
      refine ⟨7200239644572963278167435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9600319526097284370889913 7200239644572963278167435)
      ·
        refine ⟨10800359466859444917251153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7200239644572963278167435 10800359466859444917251153)
        ·
          refine ⟨8100269600144583687938365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10800359466859444917251153 8100269600144583687938365)
          ·
            refine ⟨3037601100054218882976887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8100269600144583687938365 3037601100054218882976887)
            ·
              refine ⟨4556401650081328324465331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3037601100054218882976887 4556401650081328324465331)
              ·
                refine ⟨6834602475121992486697997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4556401650081328324465331 6834602475121992486697997)
                ·
                  refine ⟨2562975928170747182511749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6834602475121992486697997 2562975928170747182511749)
                  ·
                    refine ⟨480557986532015096720953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2562975928170747182511749 480557986532015096720953)
                    ·
                      rfl

theorem cell23_2807650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_2807650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807650 prefixEnd_2807650 := by exact prefixLift 2807650
  have htrace : WordTrace (prefixWord ++ tailWord_2807650) baseStart_2807650 baseEnd_2807650 := by
    simpa [prefixWord, tailWord_2807650, baseEnd_2807650] using wordTrace_append hprefix tailTrace_2807650
  have hstable : (prefixWord ++ tailWord_2807650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807650).length < 2 ^ (prefixWord ++ tailWord_2807650).sum := by decide
  have hdescent : baseEnd_2807650 < baseStart_2807650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807659 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 3, 5]
def baseStart_2807659 : Nat := 118140960795 + 2807659 * 2 ^ 59
def prefixEnd_2807659 : Nat := 4983230072969 + 3 ^ 40 * 2807659 * 2
def baseEnd_2807659 : Nat := 480559526973978584983439

theorem tailTrace_2807659 : CollatzResearch.WordTrace tailWord_2807659 prefixEnd_2807659 480559526973978584983439 := by
  unfold tailWord_2807659
  simp only [CollatzResearch.WordTrace]
  refine ⟨102403736535338427826570031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68269157690225618551046687 102403736535338427826570031)
  ·
    refine ⟨153605604803007641739855047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102403736535338427826570031 153605604803007641739855047)
    ·
      refine ⟨230408407204511462609782571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153605604803007641739855047 230408407204511462609782571)
      ·
        refine ⟨345612610806767193914673857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230408407204511462609782571 345612610806767193914673857)
        ·
          refine ⟨259209458105075395436005393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345612610806767193914673857 259209458105075395436005393)
          ·
            refine ⟨194407093578806546577004045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259209458105075395436005393 194407093578806546577004045)
            ·
              refine ⟨72902660092052454966376517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194407093578806546577004045 72902660092052454966376517)
              ·
                refine ⟨13669248767259835306195597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72902660092052454966376517 13669248767259835306195597)
                ·
                  refine ⟨5125968287722438239823349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13669248767259835306195597 5125968287722438239823349)
                  ·
                    refine ⟨480559526973978584983439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5125968287722438239823349 480559526973978584983439)
                    ·
                      rfl

theorem cell23_2807659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 5].length) (baseStart_2807659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807659 prefixEnd_2807659 := by exact prefixLift 2807659
  have htrace : WordTrace (prefixWord ++ tailWord_2807659) baseStart_2807659 baseEnd_2807659 := by
    simpa [prefixWord, tailWord_2807659, baseEnd_2807659] using wordTrace_append hprefix tailTrace_2807659
  have hstable : (prefixWord ++ tailWord_2807659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807659).length < 2 ^ (prefixWord ++ tailWord_2807659).sum := by decide
  have hdescent : baseEnd_2807659 < baseStart_2807659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807683 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 2, 3, 2]
def baseStart_2807683 : Nat := 118140960795 + 2807683 * 2 ^ 59
def prefixEnd_2807683 : Nat := 4983230072969 + 3 ^ 40 * 2807683 * 2
def baseEnd_2807683 : Nat := 1441690904457643661050207

theorem tailTrace_2807683 : CollatzResearch.WordTrace tailWord_2807683 prefixEnd_2807683 1441690904457643661050207 := by
  unfold tailWord_2807683
  simp only [CollatzResearch.WordTrace]
  refine ⟨102404611887251479925443703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68269741258167653283629135 102404611887251479925443703)
  ·
    refine ⟨153606917830877219888165555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102404611887251479925443703 153606917830877219888165555)
    ·
      refine ⟨230410376746315829832248333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153606917830877219888165555 230410376746315829832248333)
      ·
        refine ⟨86403891279868436187093125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230410376746315829832248333 86403891279868436187093125)
        ·
          refine ⟨16200729614975331785079961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86403891279868436187093125 16200729614975331785079961)
          ·
            refine ⟨12150547211231498838809971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16200729614975331785079961 12150547211231498838809971)
            ·
              refine ⟨18225820816847248258214957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12150547211231498838809971 18225820816847248258214957)
              ·
                refine ⟨6834682806317718096830609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18225820816847248258214957 6834682806317718096830609)
                ·
                  refine ⟨5126012104738288572622957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6834682806317718096830609 5126012104738288572622957)
                  ·
                    refine ⟨1922254539276858214733609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5126012104738288572622957 1922254539276858214733609)
                    ·
                      refine ⟨1441690904457643661050207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1922254539276858214733609 1441690904457643661050207)
                      ·
                        rfl

theorem cell23_2807683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 3, 2].length) (baseStart_2807683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807683 prefixEnd_2807683 := by exact prefixLift 2807683
  have htrace : WordTrace (prefixWord ++ tailWord_2807683) baseStart_2807683 baseEnd_2807683 := by
    simpa [prefixWord, tailWord_2807683, baseEnd_2807683] using wordTrace_append hprefix tailTrace_2807683
  have hstable : (prefixWord ++ tailWord_2807683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807683).length < 2 ^ (prefixWord ++ tailWord_2807683).sum := by decide
  have hdescent : baseEnd_2807683 < baseStart_2807683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807700 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_2807700 : Nat := 118140960795 + 2807700 * 2 ^ 59
def prefixEnd_2807700 : Nat := 4983230072969 + 3 ^ 40 * 2807700 * 2
def baseEnd_2807700 : Nat := 1441699633628770094537629

theorem tailTrace_2807700 : CollatzResearch.WordTrace tailWord_2807700 prefixEnd_2807700 1441699633628770094537629 := by
  unfold tailWord_2807700
  simp only [CollatzResearch.WordTrace]
  refine ⟨51202615964094945914406277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68270154618793261219208369 51202615964094945914406277)
  ·
    refine ⟨9600490493267802358951177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51202615964094945914406277 9600490493267802358951177)
    ·
      refine ⟨7200367869950851769213383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9600490493267802358951177 7200367869950851769213383)
      ·
        refine ⟨10800551804926277653820075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7200367869950851769213383 10800551804926277653820075)
        ·
          refine ⟨16200827707389416480730113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10800551804926277653820075 16200827707389416480730113)
          ·
            refine ⟨12150620780542062360547585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16200827707389416480730113 12150620780542062360547585)
            ·
              refine ⟨9112965585406546770410689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12150620780542062360547585 9112965585406546770410689)
              ·
                refine ⟨6834724189054910077808017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9112965585406546770410689 6834724189054910077808017)
                ·
                  refine ⟨5126043141791182558356013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6834724189054910077808017 5126043141791182558356013)
                  ·
                    refine ⟨1922266178171693459383505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5126043141791182558356013 1922266178171693459383505)
                    ·
                      refine ⟨1441699633628770094537629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1922266178171693459383505 1441699633628770094537629)
                      ·
                        rfl

theorem cell23_2807700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_2807700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807700 prefixEnd_2807700 := by exact prefixLift 2807700
  have htrace : WordTrace (prefixWord ++ tailWord_2807700) baseStart_2807700 baseEnd_2807700 := by
    simpa [prefixWord, tailWord_2807700, baseEnd_2807700] using wordTrace_append hprefix tailTrace_2807700
  have hstable : (prefixWord ++ tailWord_2807700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807700).length < 2 ^ (prefixWord ++ tailWord_2807700).sum := by decide
  have hdescent : baseEnd_2807700 < baseStart_2807700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807733 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_2807733 : Nat := 118140960795 + 2807733 * 2 ^ 59
def prefixEnd_2807733 : Nat := 4983230072969 + 3 ^ 40 * 2807733 * 2
def baseEnd_2807733 : Nat := 1441716578490368465424977

theorem tailTrace_2807733 : CollatzResearch.WordTrace tailWord_2807733 prefixEnd_2807733 1441716578490368465424977 := by
  unfold tailWord_2807733
  simp only [CollatzResearch.WordTrace]
  refine ⟨102406435537070338464763853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68270957024713558976509235 102406435537070338464763853)
  ·
    refine ⟨38402413326401376924286445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102406435537070338464763853 38402413326401376924286445)
    ·
      refine ⟨14400904997400516346607417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38402413326401376924286445 14400904997400516346607417)
      ·
        refine ⟨10800678748050387259955563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14400904997400516346607417 10800678748050387259955563)
        ·
          refine ⟨16201018122075580889933345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10800678748050387259955563 16201018122075580889933345)
          ·
            refine ⟨12150763591556685667450009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16201018122075580889933345 12150763591556685667450009)
            ·
              refine ⟨9113072693667514250587507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12150763591556685667450009 9113072693667514250587507)
              ·
                refine ⟨13669609040501271375881261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9113072693667514250587507 13669609040501271375881261)
                ·
                  refine ⟨5126103390187976765955473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13669609040501271375881261 5126103390187976765955473)
                  ·
                    refine ⟨3844577542640982574466605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5126103390187976765955473 3844577542640982574466605)
                    ·
                      refine ⟨1441716578490368465424977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3844577542640982574466605 1441716578490368465424977)
                      ·
                        rfl

theorem cell23_2807733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_2807733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807733 prefixEnd_2807733 := by exact prefixLift 2807733
  have htrace : WordTrace (prefixWord ++ tailWord_2807733) baseStart_2807733 baseEnd_2807733 := by
    simpa [prefixWord, tailWord_2807733, baseEnd_2807733] using wordTrace_append hprefix tailTrace_2807733
  have hstable : (prefixWord ++ tailWord_2807733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807733).length < 2 ^ (prefixWord ++ tailWord_2807733).sum := by decide
  have hdescent : baseEnd_2807733 < baseStart_2807733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807736 : List Nat := [2, 1, 2, 1, 2, 3, 5, 7]
def baseStart_2807736 : Nat := 118140960795 + 2807736 * 2 ^ 59
def prefixEnd_2807736 : Nat := 4983230072969 + 3 ^ 40 * 2807736 * 2
def baseEnd_2807736 : Nat := 53396967367864146432869

theorem tailTrace_2807736 : CollatzResearch.WordTrace tailWord_2807736 prefixEnd_2807736 53396967367864146432869 := by
  unfold tailWord_2807736
  simp only [CollatzResearch.WordTrace]
  refine ⟨51203272478029734988561531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68271029970706313318082041 51203272478029734988561531)
  ·
    refine ⟨76804908717044602482842297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51203272478029734988561531 76804908717044602482842297)
    ·
      refine ⟨57603681537783451862131723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76804908717044602482842297 57603681537783451862131723)
      ·
        refine ⟨86405522306675177793197585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57603681537783451862131723 86405522306675177793197585)
        ·
          refine ⟨64804141730006383344898189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86405522306675177793197585 64804141730006383344898189)
          ·
            refine ⟨24301553148752393754336821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64804141730006383344898189 24301553148752393754336821)
            ·
              refine ⟨2278270607695536914469077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24301553148752393754336821 2278270607695536914469077)
              ·
                refine ⟨53396967367864146432869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2278270607695536914469077 53396967367864146432869)
                ·
                  rfl

theorem cell23_2807736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 7].length) (baseStart_2807736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807736 prefixEnd_2807736 := by exact prefixLift 2807736
  have htrace : WordTrace (prefixWord ++ tailWord_2807736) baseStart_2807736 baseEnd_2807736 := by
    simpa [prefixWord, tailWord_2807736, baseEnd_2807736] using wordTrace_append hprefix tailTrace_2807736
  have hstable : (prefixWord ++ tailWord_2807736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807736).length < 2 ^ (prefixWord ++ tailWord_2807736).sum := by decide
  have hdescent : baseEnd_2807736 < baseStart_2807736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807749 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 1, 9]
def baseStart_2807749 : Nat := 118140960795 + 2807749 * 2 ^ 59
def prefixEnd_2807749 : Nat := 4983230072969 + 3 ^ 40 * 2807749 * 2
def baseEnd_2807749 : Nat := 480574931393613467608301

theorem tailTrace_2807749 : CollatzResearch.WordTrace tailWord_2807749 prefixEnd_2807749 480574931393613467608301 := by
  unfold tailWord_2807749
  simp only [CollatzResearch.WordTrace]
  refine ⟨102407019105012373197346301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68271346070008248798230867 102407019105012373197346301)
  ·
    refine ⟨38402632164379639949004863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102407019105012373197346301 38402632164379639949004863)
    ·
      refine ⟨57603948246569459923507295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38402632164379639949004863 57603948246569459923507295)
      ·
        refine ⟨86405922369854189885260943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57603948246569459923507295 86405922369854189885260943)
        ·
          refine ⟨129608883554781284827891415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86405922369854189885260943 129608883554781284827891415)
          ·
            refine ⟨194413325332171927241837123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129608883554781284827891415 194413325332171927241837123)
            ·
              refine ⟨291619987998257890862755685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194413325332171927241837123 291619987998257890862755685)
              ·
                refine ⟨54678747749673354536766691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 291619987998257890862755685 54678747749673354536766691)
                ·
                  refine ⟨82018121624510031805150037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54678747749673354536766691 82018121624510031805150037)
                  ·
                    refine ⟨480574931393613467608301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 82018121624510031805150037 480574931393613467608301)
                    ·
                      rfl

theorem cell23_2807749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_2807749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807749 prefixEnd_2807749 := by exact prefixLift 2807749
  have htrace : WordTrace (prefixWord ++ tailWord_2807749) baseStart_2807749 baseEnd_2807749 := by
    simpa [prefixWord, tailWord_2807749, baseEnd_2807749] using wordTrace_append hprefix tailTrace_2807749
  have hstable : (prefixWord ++ tailWord_2807749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807749).length < 2 ^ (prefixWord ++ tailWord_2807749).sum := by decide
  have hdescent : baseEnd_2807749 < baseStart_2807749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807798 : List Nat := [5, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2]
def baseStart_2807798 : Nat := 118140960795 + 2807798 * 2 ^ 59
def prefixEnd_2807798 : Nat := 4983230072969 + 3 ^ 40 * 2807798 * 2
def baseEnd_2807798 : Nat := 1441749954732910711112179

theorem tailTrace_2807798 : CollatzResearch.WordTrace tailWord_2807798 prefixEnd_2807798 1441749954732910711112179 := by
  unfold tailWord_2807798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6400550392614678410367503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68272537521223236377253365 6400550392614678410367503)
  ·
    refine ⟨9600825588922017615551255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6400550392614678410367503 9600825588922017615551255)
    ·
      refine ⟨14401238383383026423326883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9600825588922017615551255 14401238383383026423326883)
      ·
        refine ⟨21601857575074539634990325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14401238383383026423326883 21601857575074539634990325)
        ·
          refine ⟨2025174147663238090780343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21601857575074539634990325 2025174147663238090780343)
          ·
            refine ⟨3037761221494857136170515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2025174147663238090780343 3037761221494857136170515)
            ·
              refine ⟨4556641832242285704255773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3037761221494857136170515 4556641832242285704255773)
              ·
                refine ⟨1708740687090857139095915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4556641832242285704255773 1708740687090857139095915)
                ·
                  refine ⟨2563111030636285708643873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1708740687090857139095915 2563111030636285708643873)
                  ·
                    refine ⟨1922333272977214281482905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2563111030636285708643873 1922333272977214281482905)
                    ·
                      refine ⟨1441749954732910711112179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1922333272977214281482905 1441749954732910711112179)
                      ·
                        rfl

theorem cell23_2807798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_2807798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807798 prefixEnd_2807798 := by exact prefixLift 2807798
  have htrace : WordTrace (prefixWord ++ tailWord_2807798) baseStart_2807798 baseEnd_2807798 := by
    simpa [prefixWord, tailWord_2807798, baseEnd_2807798] using wordTrace_append hprefix tailTrace_2807798
  have hstable : (prefixWord ++ tailWord_2807798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807798).length < 2 ^ (prefixWord ++ tailWord_2807798).sum := by decide
  have hdescent : baseEnd_2807798 < baseStart_2807798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807803 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2]
def baseStart_2807803 : Nat := 118140960795 + 2807803 * 2 ^ 59
def prefixEnd_2807803 : Nat := 4983230072969 + 3 ^ 40 * 2807803 * 2
def baseEnd_2807803 : Nat := 1441752522136183191549655

theorem tailTrace_2807803 : CollatzResearch.WordTrace tailWord_2807803 prefixEnd_2807803 1441752522136183191549655 := by
  unfold tailWord_2807803
  simp only [CollatzResearch.WordTrace]
  refine ⟨102408988646816740419812063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68272659097877826946541375 102408988646816740419812063)
  ·
    refine ⟨153613482970225110629718095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102408988646816740419812063 153613482970225110629718095)
    ·
      refine ⟨230420224455337665944577143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153613482970225110629718095 230420224455337665944577143)
      ·
        refine ⟨345630336683006498916865715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230420224455337665944577143 345630336683006498916865715)
        ·
          refine ⟨518445505024509748375298573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345630336683006498916865715 518445505024509748375298573)
          ·
            refine ⟨194417064384191155640736965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 518445505024509748375298573 194417064384191155640736965)
            ·
              refine ⟨36453199572035841682638181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194417064384191155640736965 36453199572035841682638181)
              ·
                refine ⟨6834974919756720315494659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36453199572035841682638181 6834974919756720315494659)
                ·
                  refine ⟨10252462379635080473241989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6834974919756720315494659 10252462379635080473241989)
                  ·
                    refine ⟨1922336696181577588732873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10252462379635080473241989 1922336696181577588732873)
                    ·
                      refine ⟨1441752522136183191549655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1922336696181577588732873 1441752522136183191549655)
                      ·
                        rfl

theorem cell23_2807803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 4, 2].length) (baseStart_2807803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807803 prefixEnd_2807803 := by exact prefixLift 2807803
  have htrace : WordTrace (prefixWord ++ tailWord_2807803) baseStart_2807803 baseEnd_2807803 := by
    simpa [prefixWord, tailWord_2807803, baseEnd_2807803] using wordTrace_append hprefix tailTrace_2807803
  have hstable : (prefixWord ++ tailWord_2807803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807803).length < 2 ^ (prefixWord ++ tailWord_2807803).sum := by decide
  have hdescent : baseEnd_2807803 < baseStart_2807803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807820 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 4, 2, 2]
def baseStart_2807820 : Nat := 118140960795 + 2807820 * 2 ^ 59
def prefixEnd_2807820 : Nat := 4983230072969 + 3 ^ 40 * 2807820 * 2
def baseEnd_2807820 : Nat := 1441761251307309625037077

theorem tailTrace_2807820 : CollatzResearch.WordTrace tailWord_2807820 prefixEnd_2807820 1441761251307309625037077 := by
  unfold tailWord_2807820
  simp only [CollatzResearch.WordTrace]
  refine ⟨51204804343877576161590457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68273072458503434882120609 51204804343877576161590457)
  ·
    refine ⟨38403603257908182121192843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51204804343877576161590457 38403603257908182121192843)
    ·
      refine ⟨57605404886862273181789265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38403603257908182121192843 57605404886862273181789265)
      ·
        refine ⟨43204053665146704886341949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57605404886862273181789265 43204053665146704886341949)
        ·
          refine ⟨16201520124430014332378231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43204053665146704886341949 16201520124430014332378231)
          ·
            refine ⟨24302280186645021498567347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16201520124430014332378231 24302280186645021498567347)
            ·
              refine ⟨36453420279967532247851021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24302280186645021498567347 36453420279967532247851021)
              ·
                refine ⟨13670032604987824592944133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36453420279967532247851021 13670032604987824592944133)
                ·
                  refine ⟨2563131113435217111177025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13670032604987824592944133 2563131113435217111177025)
                  ·
                    refine ⟨1922348335076412833382769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2563131113435217111177025 1922348335076412833382769)
                    ·
                      refine ⟨1441761251307309625037077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1922348335076412833382769 1441761251307309625037077)
                      ·
                        rfl

theorem cell23_2807820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_2807820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807820 prefixEnd_2807820 := by exact prefixLift 2807820
  have htrace : WordTrace (prefixWord ++ tailWord_2807820) baseStart_2807820 baseEnd_2807820 := by
    simpa [prefixWord, tailWord_2807820, baseEnd_2807820] using wordTrace_append hprefix tailTrace_2807820
  have hstable : (prefixWord ++ tailWord_2807820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807820).length < 2 ^ (prefixWord ++ tailWord_2807820).sum := by decide
  have hdescent : baseEnd_2807820 < baseStart_2807820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807831 : List Nat := [1, 1, 3, 5, 3, 1, 2, 1, 2, 1, 3]
def baseStart_2807831 : Nat := 118140960795 + 2807831 * 2 ^ 59
def prefixEnd_2807831 : Nat := 4983230072969 + 3 ^ 40 * 2807831 * 2
def baseEnd_2807831 : Nat := 1441766899594509081999527

theorem tailTrace_2807831 : CollatzResearch.WordTrace tailWord_2807831 prefixEnd_2807831 1441766899594509081999527 := by
  unfold tailWord_2807831
  simp only [CollatzResearch.WordTrace]
  refine ⟨102410009890715301201831347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68273339927143534134554231 102410009890715301201831347)
  ·
    refine ⟨153615014836072951802747021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102410009890715301201831347 153615014836072951802747021)
    ·
      refine ⟨57605630563527356926030133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153615014836072951802747021 57605630563527356926030133)
      ·
        refine ⟨5400527865330689711815325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57605630563527356926030133 5400527865330689711815325)
        ·
          refine ⟨2025197949499008641930747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5400527865330689711815325 2025197949499008641930747)
          ·
            refine ⟨3037796924248512962896121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2025197949499008641930747 3037796924248512962896121)
            ·
              refine ⟨2278347693186384722172091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3037796924248512962896121 2278347693186384722172091)
              ·
                refine ⟨3417521539779577083258137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278347693186384722172091 3417521539779577083258137)
                ·
                  refine ⟨2563141154834682812443603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3417521539779577083258137 2563141154834682812443603)
                  ·
                    refine ⟨3844711732252024218665405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2563141154834682812443603 3844711732252024218665405)
                    ·
                      refine ⟨1441766899594509081999527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3844711732252024218665405 1441766899594509081999527)
                      ·
                        rfl

theorem cell23_2807831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_2807831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807831 prefixEnd_2807831 := by exact prefixLift 2807831
  have htrace : WordTrace (prefixWord ++ tailWord_2807831) baseStart_2807831 baseEnd_2807831 := by
    simpa [prefixWord, tailWord_2807831, baseEnd_2807831] using wordTrace_append hprefix tailTrace_2807831
  have hstable : (prefixWord ++ tailWord_2807831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807831).length < 2 ^ (prefixWord ++ tailWord_2807831).sum := by decide
  have hdescent : baseEnd_2807831 < baseStart_2807831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807913 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 1, 4, 3]
def baseStart_2807913 : Nat := 118140960795 + 2807913 * 2 ^ 59
def prefixEnd_2807913 : Nat := 4983230072969 + 3 ^ 40 * 2807913 * 2
def baseEnd_2807913 : Nat := 1441809005008177761174149

theorem tailTrace_2807913 : CollatzResearch.WordTrace tailWord_2807913 prefixEnd_2807913 1441809005008177761174149 := by
  unfold tailWord_2807913
  simp only [CollatzResearch.WordTrace]
  refine ⟨102413000676418229206316393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68275333784278819470877595 102413000676418229206316393)
  ·
    refine ⟨76809750507313671904737295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102413000676418229206316393 76809750507313671904737295)
    ·
      refine ⟨115214625760970507857105943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76809750507313671904737295 115214625760970507857105943)
      ·
        refine ⟨172821938641455761785658915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115214625760970507857105943 172821938641455761785658915)
        ·
          refine ⟨259232907962183642678488373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172821938641455761785658915 259232907962183642678488373)
          ·
            refine ⟨24303085121454716501108285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 259232907962183642678488373 24303085121454716501108285)
            ·
              refine ⟨9113656920545518687915607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24303085121454716501108285 9113656920545518687915607)
              ·
                refine ⟨13670485380818278031873411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9113656920545518687915607 13670485380818278031873411)
                ·
                  refine ⟨20505728071227417047810117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13670485380818278031873411 20505728071227417047810117)
                  ·
                    refine ⟨3844824013355140696464397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20505728071227417047810117 3844824013355140696464397)
                    ·
                      refine ⟨1441809005008177761174149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3844824013355140696464397 1441809005008177761174149)
                      ·
                        rfl

theorem cell23_2807913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 4, 3].length) (baseStart_2807913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807913 prefixEnd_2807913 := by exact prefixLift 2807913
  have htrace : WordTrace (prefixWord ++ tailWord_2807913) baseStart_2807913 baseEnd_2807913 := by
    simpa [prefixWord, tailWord_2807913, baseEnd_2807913] using wordTrace_append hprefix tailTrace_2807913
  have hstable : (prefixWord ++ tailWord_2807913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807913).length < 2 ^ (prefixWord ++ tailWord_2807913).sum := by decide
  have hdescent : baseEnd_2807913 < baseStart_2807913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807933 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 8]
def baseStart_2807933 : Nat := 118140960795 + 2807933 * 2 ^ 59
def prefixEnd_2807933 : Nat := 4983230072969 + 3 ^ 40 * 2807933 * 2
def baseEnd_2807933 : Nat := 160202141624585298102673

theorem tailTrace_2807933 : CollatzResearch.WordTrace tailWord_2807933 prefixEnd_2807933 160202141624585298102673 := by
  unfold tailWord_2807933
  simp only [CollatzResearch.WordTrace]
  refine ⟨102413730136345772622044453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68275820090897181748029635 102413730136345772622044453)
  ·
    refine ⟨19202574400564832366633335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102413730136345772622044453 19202574400564832366633335)
    ·
      refine ⟨28803861600847248549950003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19202574400564832366633335 28803861600847248549950003)
      ·
        refine ⟨43205792401270872824925005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28803861600847248549950003 43205792401270872824925005)
        ·
          refine ⟨16202172150476577309346877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43205792401270872824925005 16202172150476577309346877)
          ·
            refine ⟨6075814556428716491005079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16202172150476577309346877 6075814556428716491005079)
            ·
              refine ⟨9113721834643074736507619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6075814556428716491005079 9113721834643074736507619)
              ·
                refine ⟨13670582751964612104761429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9113721834643074736507619 13670582751964612104761429)
                ·
                  refine ⟨160202141624585298102673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13670582751964612104761429 160202141624585298102673)
                  ·
                    rfl

theorem cell23_2807933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_2807933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807933 prefixEnd_2807933 := by exact prefixLift 2807933
  have htrace : WordTrace (prefixWord ++ tailWord_2807933) baseStart_2807933 baseEnd_2807933 := by
    simpa [prefixWord, tailWord_2807933, baseEnd_2807933] using wordTrace_append hprefix tailTrace_2807933
  have hstable : (prefixWord ++ tailWord_2807933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807933).length < 2 ^ (prefixWord ++ tailWord_2807933).sum := by decide
  have hdescent : baseEnd_2807933 < baseStart_2807933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807937 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 3, 4]
def baseStart_2807937 : Nat := 118140960795 + 2807937 * 2 ^ 59
def prefixEnd_2807937 : Nat := 4983230072969 + 3 ^ 40 * 2807937 * 2
def baseEnd_2807937 : Nat := 480607109514628555758013

theorem tailTrace_2807937 : CollatzResearch.WordTrace tailWord_2807937 prefixEnd_2807937 480607109514628555758013 := by
  unfold tailWord_2807937
  simp only [CollatzResearch.WordTrace]
  refine ⟨102413876028331281305190065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68275917352220854203460043 102413876028331281305190065)
  ·
    refine ⟨76810407021248460978892549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102413876028331281305190065 76810407021248460978892549)
    ·
      refine ⟨14401951316484086433542353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76810407021248460978892549 14401951316484086433542353)
      ·
        refine ⟨10801463487363064825156765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14401951316484086433542353 10801463487363064825156765)
        ·
          refine ⟨4050548807761149309433787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10801463487363064825156765 4050548807761149309433787)
          ·
            refine ⟨6075823211641723964150681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4050548807761149309433787 6075823211641723964150681)
            ·
              refine ⟨4556867408731292973113011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6075823211641723964150681 4556867408731292973113011)
              ·
                refine ⟨6835301113096939459669517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4556867408731292973113011 6835301113096939459669517)
                ·
                  refine ⟨2563237917411352297376069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6835301113096939459669517 2563237917411352297376069)
                  ·
                    refine ⟨480607109514628555758013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2563237917411352297376069 480607109514628555758013)
                    ·
                      rfl

theorem cell23_2807937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_2807937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807937 prefixEnd_2807937 := by exact prefixLift 2807937
  have htrace : WordTrace (prefixWord ++ tailWord_2807937) baseStart_2807937 baseEnd_2807937 := by
    simpa [prefixWord, tailWord_2807937, baseEnd_2807937] using wordTrace_append hprefix tailTrace_2807937
  have hstable : (prefixWord ++ tailWord_2807937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807937).length < 2 ^ (prefixWord ++ tailWord_2807937).sum := by decide
  have hdescent : baseEnd_2807937 < baseStart_2807937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807983 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 4]
def baseStart_2807983 : Nat := 118140960795 + 2807983 * 2 ^ 59
def prefixEnd_2807983 : Nat := 4983230072969 + 3 ^ 40 * 2807983 * 2
def baseEnd_2807983 : Nat := 1441844948653992487298827

theorem tailTrace_2807983 : CollatzResearch.WordTrace tailWord_2807983 prefixEnd_2807983 1441844948653992487298827 := by
  unfold tailWord_2807983
  simp only [CollatzResearch.WordTrace]
  refine ⟨102415553786164631161364603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68277035857443087440909735 102415553786164631161364603)
  ·
    refine ⟨153623330679246946742046905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102415553786164631161364603 153623330679246946742046905)
    ·
      refine ⟨115217498009435210056535179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153623330679246946742046905 115217498009435210056535179)
      ·
        refine ⟨172826247014152815084802769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115217498009435210056535179 172826247014152815084802769)
        ·
          refine ⟨129619685260614611313602077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172826247014152815084802769 129619685260614611313602077)
          ·
            refine ⟨48607381972730479242600779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129619685260614611313602077 48607381972730479242600779)
            ·
              refine ⟨72911072959095718863901169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48607381972730479242600779 72911072959095718863901169)
              ·
                refine ⟨54683304719321789147925877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72911072959095718863901169 54683304719321789147925877)
                ·
                  refine ⟨5126559817436417732618051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54683304719321789147925877 5126559817436417732618051)
                  ·
                    refine ⟨7689839726154626598927077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5126559817436417732618051 7689839726154626598927077)
                    ·
                      refine ⟨1441844948653992487298827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7689839726154626598927077 1441844948653992487298827)
                      ·
                        rfl

theorem cell23_2807983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 4].length) (baseStart_2807983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807983 prefixEnd_2807983 := by exact prefixLift 2807983
  have htrace : WordTrace (prefixWord ++ tailWord_2807983) baseStart_2807983 baseEnd_2807983 := by
    simpa [prefixWord, tailWord_2807983, baseEnd_2807983] using wordTrace_append hprefix tailTrace_2807983
  have hstable : (prefixWord ++ tailWord_2807983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807983).length < 2 ^ (prefixWord ++ tailWord_2807983).sum := by decide
  have hdescent : baseEnd_2807983 < baseStart_2807983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2807988 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2807988 : Nat := 118140960795 + 2807988 * 2 ^ 59
def prefixEnd_2807988 : Nat := 4983230072969 + 3 ^ 40 * 2807988 * 2
def baseEnd_2807988 : Nat := 480615838685754989245435

theorem tailTrace_2807988 : CollatzResearch.WordTrace tailWord_2807988 prefixEnd_2807988 480615838685754989245435 := by
  unfold tailWord_2807988
  simp only [CollatzResearch.WordTrace]
  refine ⟨51207868075573258507648309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68277157434097678010197745 51207868075573258507648309)
  ·
    refine ⟨4800737632084992985092029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51207868075573258507648309 4800737632084992985092029)
    ·
      refine ⟨1800276612031872369409511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4800737632084992985092029 1800276612031872369409511)
      ·
        refine ⟨2700414918047808554114267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1800276612031872369409511 2700414918047808554114267)
        ·
          refine ⟨4050622377071712831171401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2700414918047808554114267 4050622377071712831171401)
          ·
            refine ⟨3037966782803784623378551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4050622377071712831171401 3037966782803784623378551)
            ·
              refine ⟨4556950174205676935067827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3037966782803784623378551 4556950174205676935067827)
              ·
                refine ⟨6835425261308515402601741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4556950174205676935067827 6835425261308515402601741)
                ·
                  refine ⟨2563284472990693275975653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6835425261308515402601741 2563284472990693275975653)
                  ·
                    refine ⟨480615838685754989245435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2563284472990693275975653 480615838685754989245435)
                    ·
                      rfl

theorem cell23_2807988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2807988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2807988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2807988 prefixEnd_2807988 := by exact prefixLift 2807988
  have htrace : WordTrace (prefixWord ++ tailWord_2807988) baseStart_2807988 baseEnd_2807988 := by
    simpa [prefixWord, tailWord_2807988, baseEnd_2807988] using wordTrace_append hprefix tailTrace_2807988
  have hstable : (prefixWord ++ tailWord_2807988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2807988).length < 2 ^ (prefixWord ++ tailWord_2807988).sum := by decide
  have hdescent : baseEnd_2807988 < baseStart_2807988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2807988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808001 : List Nat := [1, 2, 6, 1, 3, 1, 2, 1, 6]
def baseStart_2808001 : Nat := 118140960795 + 2808001 * 2 ^ 59
def prefixEnd_2808001 : Nat := 4983230072969 + 3 ^ 40 * 2808001 * 2
def baseEnd_2808001 : Nat := 160206021256197046319305

theorem tailTrace_2808001 : CollatzResearch.WordTrace tailWord_2808001 prefixEnd_2808001 160206021256197046319305 := by
  unfold tailWord_2808001
  simp only [CollatzResearch.WordTrace]
  refine ⟨102416210300099420235519857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68277473533399613490346571 102416210300099420235519857)
  ·
    refine ⟨76812157725074565176639893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102416210300099420235519857 76812157725074565176639893)
    ·
      refine ⟨3600569893362870242654995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76812157725074565176639893 3600569893362870242654995)
      ·
        refine ⟨5400854840044305363982493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3600569893362870242654995 5400854840044305363982493)
        ·
          refine ⟨2025320565016614511493435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5400854840044305363982493 2025320565016614511493435)
          ·
            refine ⟨3037980847524921767240153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2025320565016614511493435 3037980847524921767240153)
            ·
              refine ⟨2278485635643691325430115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3037980847524921767240153 2278485635643691325430115)
              ·
                refine ⟨3417728453465536988145173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278485635643691325430115 3417728453465536988145173)
                ·
                  refine ⟨160206021256197046319305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3417728453465536988145173 160206021256197046319305)
                  ·
                    rfl

theorem cell23_2808001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 6].length) (baseStart_2808001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808001 prefixEnd_2808001 := by exact prefixLift 2808001
  have htrace : WordTrace (prefixWord ++ tailWord_2808001) baseStart_2808001 baseEnd_2808001 := by
    simpa [prefixWord, tailWord_2808001, baseEnd_2808001] using wordTrace_append hprefix tailTrace_2808001
  have hstable : (prefixWord ++ tailWord_2808001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808001).length < 2 ^ (prefixWord ++ tailWord_2808001).sum := by decide
  have hdescent : baseEnd_2808001 < baseStart_2808001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808017 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 3, 2, 2]
def baseStart_2808017 : Nat := 118140960795 + 2808017 * 2 ^ 59
def prefixEnd_2808017 : Nat := 4983230072969 + 3 ^ 40 * 2808017 * 2
def baseEnd_2808017 : Nat := 1441862406996245354273671

theorem tailTrace_2808017 : CollatzResearch.WordTrace tailWord_2808017 prefixEnd_2808017 1441862406996245354273671 := by
  unfold tailWord_2808017
  simp only [CollatzResearch.WordTrace]
  refine ⟨102416793868041454968102305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68277862578694303312068203 102416793868041454968102305)
  ·
    refine ⟨76812595401031091226076729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102416793868041454968102305 76812595401031091226076729)
    ·
      refine ⟨57609446550773318419557547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76812595401031091226076729 57609446550773318419557547)
      ·
        refine ⟨86414169826159977629336321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57609446550773318419557547 86414169826159977629336321)
        ·
          refine ⟨64810627369619983222002241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86414169826159977629336321 64810627369619983222002241)
          ·
            refine ⟨48607970527214987416501681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64810627369619983222002241 48607970527214987416501681)
            ·
              refine ⟨36455977895411240562376261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48607970527214987416501681 36455977895411240562376261)
              ·
                refine ⟨6835495855389607605445549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36455977895411240562376261 6835495855389607605445549)
                ·
                  refine ⟨2563310945771102852042081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6835495855389607605445549 2563310945771102852042081)
                  ·
                    refine ⟨1922483209328327139031561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2563310945771102852042081 1922483209328327139031561)
                    ·
                      refine ⟨1441862406996245354273671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1922483209328327139031561 1441862406996245354273671)
                      ·
                        rfl

theorem cell23_2808017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 2, 2].length) (baseStart_2808017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808017 prefixEnd_2808017 := by exact prefixLift 2808017
  have htrace : WordTrace (prefixWord ++ tailWord_2808017) baseStart_2808017 baseEnd_2808017 := by
    simpa [prefixWord, tailWord_2808017, baseEnd_2808017] using wordTrace_append hprefix tailTrace_2808017
  have hstable : (prefixWord ++ tailWord_2808017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808017).length < 2 ^ (prefixWord ++ tailWord_2808017).sum := by decide
  have hdescent : baseEnd_2808017 < baseStart_2808017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808037 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 1, 1, 5]
def baseStart_2808037 : Nat := 118140960795 + 2808037 * 2 ^ 59
def prefixEnd_2808037 : Nat := 4983230072969 + 3 ^ 40 * 2808037 * 2
def baseEnd_2808037 : Nat := 1441872676609335276023579

theorem tailTrace_2808037 : CollatzResearch.WordTrace tailWord_2808037 prefixEnd_2808037 1441872676609335276023579 := by
  unfold tailWord_2808037
  simp only [CollatzResearch.WordTrace]
  refine ⟨102417523327968998383830365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68278348885312665589220243 102417523327968998383830365)
  ·
    refine ⟨38406571247988374393936387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102417523327968998383830365 38406571247988374393936387)
    ·
      refine ⟨57609856871982561590904581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38406571247988374393936387 57609856871982561590904581)
      ·
        refine ⟨10801848163496730298294609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57609856871982561590904581 10801848163496730298294609)
        ·
          refine ⟨8101386122622547723720957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10801848163496730298294609 8101386122622547723720957)
          ·
            refine ⟨3038019795983455396395359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8101386122622547723720957 3038019795983455396395359)
            ·
              refine ⟨4557029693975183094593039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3038019795983455396395359 4557029693975183094593039)
              ·
                refine ⟨6835544540962774641889559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4557029693975183094593039 6835544540962774641889559)
                ·
                  refine ⟨10253316811444161962834339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6835544540962774641889559 10253316811444161962834339)
                  ·
                    refine ⟨15379975217166242944251509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10253316811444161962834339 15379975217166242944251509)
                    ·
                      refine ⟨1441872676609335276023579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15379975217166242944251509 1441872676609335276023579)
                      ·
                        rfl

theorem cell23_2808037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_2808037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808037 prefixEnd_2808037 := by exact prefixLift 2808037
  have htrace : WordTrace (prefixWord ++ tailWord_2808037) baseStart_2808037 baseEnd_2808037 := by
    simpa [prefixWord, tailWord_2808037, baseEnd_2808037] using wordTrace_append hprefix tailTrace_2808037
  have hstable : (prefixWord ++ tailWord_2808037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808037).length < 2 ^ (prefixWord ++ tailWord_2808037).sum := by decide
  have hdescent : baseEnd_2808037 < baseStart_2808037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808045 : List Nat := [1, 5, 1, 2, 4, 1, 2, 2, 1, 1, 3]
def baseStart_2808045 : Nat := 118140960795 + 2808045 * 2 ^ 59
def prefixEnd_2808045 : Nat := 4983230072969 + 3 ^ 40 * 2808045 * 2
def baseEnd_2808045 : Nat := 1441876784454571244723543

theorem tailTrace_2808045 : CollatzResearch.WordTrace tailWord_2808045 prefixEnd_2808045 1441876784454571244723543 := by
  unfold tailWord_2808045
  simp only [CollatzResearch.WordTrace]
  refine ⟨102417815111940015750121589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68278543407960010500081059 102417815111940015750121589)
  ·
    refine ⟨9601670166744376476573899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102417815111940015750121589 9601670166744376476573899)
    ·
      refine ⟨14402505250116564714860849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9601670166744376476573899 14402505250116564714860849)
      ·
        refine ⟨10801878937587423536145637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14402505250116564714860849 10801878937587423536145637)
        ·
          refine ⟨2025352300797641913027307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10801878937587423536145637 2025352300797641913027307)
          ·
            refine ⟨3038028451196462869540961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2025352300797641913027307 3038028451196462869540961)
            ·
              refine ⟨2278521338397347152155721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3038028451196462869540961 2278521338397347152155721)
              ·
                refine ⟨1708891003798010364116791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2278521338397347152155721 1708891003798010364116791)
                ·
                  refine ⟨2563336505697015546175187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1708891003798010364116791 2563336505697015546175187)
                  ·
                    refine ⟨3845004758545523319262781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2563336505697015546175187 3845004758545523319262781)
                    ·
                      refine ⟨1441876784454571244723543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3845004758545523319262781 1441876784454571244723543)
                      ·
                        rfl

theorem cell23_2808045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_2808045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808045 prefixEnd_2808045 := by exact prefixLift 2808045
  have htrace : WordTrace (prefixWord ++ tailWord_2808045) baseStart_2808045 baseEnd_2808045 := by
    simpa [prefixWord, tailWord_2808045, baseEnd_2808045] using wordTrace_append hprefix tailTrace_2808045
  have hstable : (prefixWord ++ tailWord_2808045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808045).length < 2 ^ (prefixWord ++ tailWord_2808045).sum := by decide
  have hdescent : baseEnd_2808045 < baseStart_2808045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808067 : List Nat := [1, 1, 1, 3, 2, 3, 1, 5, 2, 1, 3]
def baseStart_2808067 : Nat := 118140960795 + 2808067 * 2 ^ 59
def prefixEnd_2808067 : Nat := 4983230072969 + 3 ^ 40 * 2808067 * 2
def baseEnd_2808067 : Nat := 1441888081028970158648441

theorem tailTrace_2808067 : CollatzResearch.WordTrace tailWord_2808067 prefixEnd_2808067 1441888081028970158648441 := by
  unfold tailWord_2808067
  simp only [CollatzResearch.WordTrace]
  refine ⟨102418617517860313507422455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68279078345240209004948303 102418617517860313507422455)
  ·
    refine ⟨153627926276790470261133683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102418617517860313507422455 153627926276790470261133683)
    ·
      refine ⟨230441889415185705391700525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153627926276790470261133683 230441889415185705391700525)
      ·
        refine ⟨86415708530694639521887697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230441889415185705391700525 86415708530694639521887697)
        ·
          refine ⟨64811781398020979641415773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86415708530694639521887697 64811781398020979641415773)
          ·
            refine ⟨24304418024257867365530915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64811781398020979641415773 24304418024257867365530915)
            ·
              refine ⟨36456627036386801048296373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24304418024257867365530915 36456627036386801048296373)
              ·
                refine ⟨3417808784661262598277785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36456627036386801048296373 3417808784661262598277785)
                ·
                  refine ⟨2563356588495946948708339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3417808784661262598277785 2563356588495946948708339)
                  ·
                    refine ⟨3845034882743920423062509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2563356588495946948708339 3845034882743920423062509)
                    ·
                      refine ⟨1441888081028970158648441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3845034882743920423062509 1441888081028970158648441)
                      ·
                        rfl

theorem cell23_2808067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_2808067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808067 prefixEnd_2808067 := by exact prefixLift 2808067
  have htrace : WordTrace (prefixWord ++ tailWord_2808067) baseStart_2808067 baseEnd_2808067 := by
    simpa [prefixWord, tailWord_2808067, baseEnd_2808067] using wordTrace_append hprefix tailTrace_2808067
  have hstable : (prefixWord ++ tailWord_2808067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808067).length < 2 ^ (prefixWord ++ tailWord_2808067).sum := by decide
  have hdescent : baseEnd_2808067 < baseStart_2808067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808100 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 2, 6]
def baseStart_2808100 : Nat := 118140960795 + 2808100 * 2 ^ 59
def prefixEnd_2808100 : Nat := 4983230072969 + 3 ^ 40 * 2808100 * 2
def baseEnd_2808100 : Nat := 480635008630189509845263

theorem tailTrace_2808100 : CollatzResearch.WordTrace tailWord_2808100 prefixEnd_2808100 480635008630189509845263 := by
  unfold tailWord_2808100
  simp only [CollatzResearch.WordTrace]
  refine ⟨51209910563370380071686877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68279880751160506762249169 51209910563370380071686877)
  ·
    refine ⟨19203716461263892526882579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51209910563370380071686877 19203716461263892526882579)
    ·
      refine ⟨28805574691895838790323869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19203716461263892526882579 28805574691895838790323869)
      ·
        refine ⟨10802090509460939546371451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28805574691895838790323869 10802090509460939546371451)
        ·
          refine ⟨16203135764191409319557177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10802090509460939546371451 16203135764191409319557177)
          ·
            refine ⟨12152351823143556989667883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16203135764191409319557177 12152351823143556989667883)
            ·
              refine ⟨18228527734715335484501825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12152351823143556989667883 18228527734715335484501825)
              ·
                refine ⟨13671395801036501613376369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18228527734715335484501825 13671395801036501613376369)
                ·
                  refine ⟨10253546850777376210032277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13671395801036501613376369 10253546850777376210032277)
                  ·
                    refine ⟨480635008630189509845263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10253546850777376210032277 480635008630189509845263)
                    ·
                      rfl

theorem cell23_2808100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_2808100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808100 prefixEnd_2808100 := by exact prefixLift 2808100
  have htrace : WordTrace (prefixWord ++ tailWord_2808100) baseStart_2808100 baseEnd_2808100 := by
    simpa [prefixWord, tailWord_2808100, baseEnd_2808100] using wordTrace_append hprefix tailTrace_2808100
  have hstable : (prefixWord ++ tailWord_2808100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808100).length < 2 ^ (prefixWord ++ tailWord_2808100).sum := by decide
  have hdescent : baseEnd_2808100 < baseStart_2808100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808101 : List Nat := [1, 3, 1, 2, 5, 2, 1, 2, 2, 1, 3]
def baseStart_2808101 : Nat := 118140960795 + 2808101 * 2 ^ 59
def prefixEnd_2808101 : Nat := 4983230072969 + 3 ^ 40 * 2808101 * 2
def baseEnd_2808101 : Nat := 1441905539371223025623285

theorem tailTrace_2808101 : CollatzResearch.WordTrace tailWord_2808101 prefixEnd_2808101 1441905539371223025623285 := by
  unfold tailWord_2808101
  simp only [CollatzResearch.WordTrace]
  refine ⟨102419857599737137314160157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68279905066491424876106771 102419857599737137314160157)
  ·
    refine ⟨38407446599901426492810059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102419857599737137314160157 38407446599901426492810059)
    ·
      refine ⟨57611169899852139739215089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38407446599901426492810059 57611169899852139739215089)
      ·
        refine ⟨43208377424889104804411317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57611169899852139739215089 43208377424889104804411317)
        ·
          refine ⟨4050785383583353575413561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43208377424889104804411317 4050785383583353575413561)
          ·
            refine ⟨3038089037687515181560171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4050785383583353575413561 3038089037687515181560171)
            ·
              refine ⟨4557133556531272772340257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3038089037687515181560171 4557133556531272772340257)
              ·
                refine ⟨3417850167398454579255193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4557133556531272772340257 3417850167398454579255193)
                ·
                  refine ⟨2563387625548840934441395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3417850167398454579255193 2563387625548840934441395)
                  ·
                    refine ⟨3845081438323261401662093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2563387625548840934441395 3845081438323261401662093)
                    ·
                      refine ⟨1441905539371223025623285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3845081438323261401662093 1441905539371223025623285)
                      ·
                        rfl

theorem cell23_2808101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_2808101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808101 prefixEnd_2808101 := by exact prefixLift 2808101
  have htrace : WordTrace (prefixWord ++ tailWord_2808101) baseStart_2808101 baseEnd_2808101 := by
    simpa [prefixWord, tailWord_2808101, baseEnd_2808101] using wordTrace_append hprefix tailTrace_2808101
  have hstable : (prefixWord ++ tailWord_2808101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808101).length < 2 ^ (prefixWord ++ tailWord_2808101).sum := by decide
  have hdescent : baseEnd_2808101 < baseStart_2808101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808120 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 2, 2, 4]
def baseStart_2808120 : Nat := 118140960795 + 2808120 * 2 ^ 59
def prefixEnd_2808120 : Nat := 4983230072969 + 3 ^ 40 * 2808120 * 2
def baseEnd_2808120 : Nat := 1441915295503658451285697

theorem tailTrace_2808120 : CollatzResearch.WordTrace tailWord_2808120 prefixEnd_2808120 1441915295503658451285697 := by
  unfold tailWord_2808120
  simp only [CollatzResearch.WordTrace]
  refine ⟨51210275293334151779550907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68280367057778869039401209 51210275293334151779550907)
  ·
    refine ⟨76815412940001227669326361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51210275293334151779550907 76815412940001227669326361)
    ·
      refine ⟨57611559705000920751994771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76815412940001227669326361 57611559705000920751994771)
      ·
        refine ⟨86417339557501381127992157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57611559705000920751994771 86417339557501381127992157)
        ·
          refine ⟨32406502334063017922997059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86417339557501381127992157 32406502334063017922997059)
          ·
            refine ⟨48609753501094526884495589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32406502334063017922997059 48609753501094526884495589)
            ·
              refine ⟨9114328781455223790842923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48609753501094526884495589 9114328781455223790842923)
              ·
                refine ⟨13671493172182835686264385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9114328781455223790842923 13671493172182835686264385)
                ·
                  refine ⟨10253619879137126764698289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13671493172182835686264385 10253619879137126764698289)
                  ·
                    refine ⟨7690214909352845073523717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10253619879137126764698289 7690214909352845073523717)
                    ·
                      refine ⟨1441915295503658451285697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7690214909352845073523717 1441915295503658451285697)
                      ·
                        rfl

theorem cell23_2808120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_2808120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808120 prefixEnd_2808120 := by exact prefixLift 2808120
  have htrace : WordTrace (prefixWord ++ tailWord_2808120) baseStart_2808120 baseEnd_2808120 := by
    simpa [prefixWord, tailWord_2808120, baseEnd_2808120] using wordTrace_append hprefix tailTrace_2808120
  have hstable : (prefixWord ++ tailWord_2808120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808120).length < 2 ^ (prefixWord ++ tailWord_2808120).sum := by decide
  have hdescent : baseEnd_2808120 < baseStart_2808120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808164 : List Nat := [2, 3, 1, 1, 3, 1, 5, 2, 5]
def baseStart_2808164 : Nat := 118140960795 + 2808164 * 2 ^ 59
def prefixEnd_2808164 : Nat := 4983230072969 + 3 ^ 40 * 2808164 * 2
def baseEnd_2808164 : Nat := 160215320961384031015055

theorem tailTrace_2808164 : CollatzResearch.WordTrace tailWord_2808164 prefixEnd_2808164 160215320961384031015055 := by
  unfold tailWord_2808164
  simp only [CollatzResearch.WordTrace]
  refine ⟨51211077699254449536851773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68281436932339266049135697 51211077699254449536851773)
  ·
    refine ⟨19204154137220418576319415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51211077699254449536851773 19204154137220418576319415)
    ·
      refine ⟨28806231205830627864479123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19204154137220418576319415 28806231205830627864479123)
      ·
        refine ⟨43209346808745941796718685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28806231205830627864479123 43209346808745941796718685)
        ·
          refine ⟨16203505053279728173769507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43209346808745941796718685 16203505053279728173769507)
          ·
            refine ⟨24305257579919592260654261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16203505053279728173769507 24305257579919592260654261)
            ·
              refine ⟨2278617898117461774436337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24305257579919592260654261 2278617898117461774436337)
              ·
                refine ⟨1708963423588096330827253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2278617898117461774436337 1708963423588096330827253)
                ·
                  refine ⟨160215320961384031015055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1708963423588096330827253 160215320961384031015055)
                  ·
                    rfl

theorem cell23_2808164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_2808164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808164 prefixEnd_2808164 := by exact prefixLift 2808164
  have htrace : WordTrace (prefixWord ++ tailWord_2808164) baseStart_2808164 baseEnd_2808164 := by
    simpa [prefixWord, tailWord_2808164, baseEnd_2808164] using wordTrace_append hprefix tailTrace_2808164
  have hstable : (prefixWord ++ tailWord_2808164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808164).length < 2 ^ (prefixWord ++ tailWord_2808164).sum := by decide
  have hdescent : baseEnd_2808164 < baseStart_2808164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808197 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 4, 4, 2]
def baseStart_2808197 : Nat := 118140960795 + 2808197 * 2 ^ 59
def prefixEnd_2808197 : Nat := 4983230072969 + 3 ^ 40 * 2808197 * 2
def baseEnd_2808197 : Nat := 1441954833514054650022843

theorem tailTrace_2808197 : CollatzResearch.WordTrace tailWord_2808197 prefixEnd_2808197 1441954833514054650022843 := by
  unfold tailWord_2808197
  simp only [CollatzResearch.WordTrace]
  refine ⟨102423359007389345709654845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68282239338259563806436563 102423359007389345709654845)
  ·
    refine ⟨38408759627771004641120567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102423359007389345709654845 38408759627771004641120567)
    ·
      refine ⟨57613139441656506961680851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38408759627771004641120567 57613139441656506961680851)
      ·
        refine ⟨86419709162484760442521277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57613139441656506961680851 86419709162484760442521277)
        ·
          refine ⟨32407390935931785165945479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86419709162484760442521277 32407390935931785165945479)
          ·
            refine ⟨48611086403897677748918219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32407390935931785165945479 48611086403897677748918219)
            ·
              refine ⟨72916629605846516623377329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48611086403897677748918219 72916629605846516623377329)
              ·
                refine ⟨54687472204384887467532997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72916629605846516623377329 54687472204384887467532997)
                ·
                  refine ⟨10253901038322166400162437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54687472204384887467532997 10253901038322166400162437)
                  ·
                    refine ⟨1922606444685406200030457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10253901038322166400162437 1922606444685406200030457)
                    ·
                      refine ⟨1441954833514054650022843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1922606444685406200030457 1441954833514054650022843)
                      ·
                        rfl

theorem cell23_2808197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 4, 2].length) (baseStart_2808197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808197 prefixEnd_2808197 := by exact prefixLift 2808197
  have htrace : WordTrace (prefixWord ++ tailWord_2808197) baseStart_2808197 baseEnd_2808197 := by
    simpa [prefixWord, tailWord_2808197, baseEnd_2808197] using wordTrace_append hprefix tailTrace_2808197
  have hstable : (prefixWord ++ tailWord_2808197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808197).length < 2 ^ (prefixWord ++ tailWord_2808197).sum := by decide
  have hdescent : baseEnd_2808197 < baseStart_2808197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808217 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 2, 2, 3]
def baseStart_2808217 : Nat := 118140960795 + 2808217 * 2 ^ 59
def prefixEnd_2808217 : Nat := 4983230072969 + 3 ^ 40 * 2808217 * 2
def baseEnd_2808217 : Nat := 1441965103127144571772751

theorem tailTrace_2808217 : CollatzResearch.WordTrace tailWord_2808217 prefixEnd_2808217 1441965103127144571772751 := by
  unfold tailWord_2808217
  simp only [CollatzResearch.WordTrace]
  refine ⟨102424088467316889125382905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68282725644877926083588603 102424088467316889125382905)
  ·
    refine ⟨76818066350487666844037179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102424088467316889125382905 76818066350487666844037179)
    ·
      refine ⟨115227099525731500266055769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76818066350487666844037179 115227099525731500266055769)
      ·
        refine ⟨86420324644298625199541827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115227099525731500266055769 86420324644298625199541827)
        ·
          refine ⟨129630486966447937799312741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86420324644298625199541827 129630486966447937799312741)
          ·
            refine ⟨24305716306208988337371139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129630486966447937799312741 24305716306208988337371139)
            ·
              refine ⟨36458574459313482506056709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24305716306208988337371139 36458574459313482506056709)
              ·
                refine ⟨6835982711121277969885633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36458574459313482506056709 6835982711121277969885633)
                ·
                  refine ⟨5126987033340958477414225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6835982711121277969885633 5126987033340958477414225)
                  ·
                    refine ⟨3845240275005718858060669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5126987033340958477414225 3845240275005718858060669)
                    ·
                      refine ⟨1441965103127144571772751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3845240275005718858060669 1441965103127144571772751)
                      ·
                        rfl

theorem cell23_2808217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_2808217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808217 prefixEnd_2808217 := by exact prefixLift 2808217
  have htrace : WordTrace (prefixWord ++ tailWord_2808217) baseStart_2808217 baseEnd_2808217 := by
    simpa [prefixWord, tailWord_2808217, baseEnd_2808217] using wordTrace_append hprefix tailTrace_2808217
  have hstable : (prefixWord ++ tailWord_2808217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808217).length < 2 ^ (prefixWord ++ tailWord_2808217).sum := by decide
  have hdescent : baseEnd_2808217 < baseStart_2808217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808281 : List Nat := [1, 2, 1, 2, 4, 1, 1, 6, 1, 1, 3]
def baseStart_2808281 : Nat := 118140960795 + 2808281 * 2 ^ 59
def prefixEnd_2808281 : Nat := 4983230072969 + 3 ^ 40 * 2808281 * 2
def baseEnd_2808281 : Nat := 1441997965889032321372457

theorem tailTrace_2808281 : CollatzResearch.WordTrace tailWord_2808281 prefixEnd_2808281 1441997965889032321372457 := by
  unfold tailWord_2808281
  simp only [CollatzResearch.WordTrace]
  refine ⟨102426422739085028055712697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68284281826056685370475131 102426422739085028055712697)
  ·
    refine ⟨76819817054313771041784523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102426422739085028055712697 76819817054313771041784523)
    ·
      refine ⟨115229725581470656562676785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76819817054313771041784523 115229725581470656562676785)
      ·
        refine ⟨86422294186102992422007589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115229725581470656562676785 86422294186102992422007589)
        ·
          refine ⟨16204180159894311079126423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86422294186102992422007589 16204180159894311079126423)
          ·
            refine ⟨24306270239841466618689635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16204180159894311079126423 24306270239841466618689635)
            ·
              refine ⟨36459405359762199928034453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24306270239841466618689635 36459405359762199928034453)
              ·
                refine ⟨1709034626238853121626615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36459405359762199928034453 1709034626238853121626615)
                ·
                  refine ⟨2563551939358279682439923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1709034626238853121626615 2563551939358279682439923)
                  ·
                    refine ⟨3845327909037419523659885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2563551939358279682439923 3845327909037419523659885)
                    ·
                      refine ⟨1441997965889032321372457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3845327909037419523659885 1441997965889032321372457)
                      ·
                        rfl

theorem cell23_2808281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 1, 1, 3].length) (baseStart_2808281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808281 prefixEnd_2808281 := by exact prefixLift 2808281
  have htrace : WordTrace (prefixWord ++ tailWord_2808281) baseStart_2808281 baseEnd_2808281 := by
    simpa [prefixWord, tailWord_2808281, baseEnd_2808281] using wordTrace_append hprefix tailTrace_2808281
  have hstable : (prefixWord ++ tailWord_2808281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808281).length < 2 ^ (prefixWord ++ tailWord_2808281).sum := by decide
  have hdescent : baseEnd_2808281 < baseStart_2808281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808301 : List Nat := [1, 5, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_2808301 : Nat := 118140960795 + 2808301 * 2 ^ 59
def prefixEnd_2808301 : Nat := 4983230072969 + 3 ^ 40 * 2808301 * 2
def baseEnd_2808301 : Nat := 480669411834040747707455

theorem tailTrace_2808301 : CollatzResearch.WordTrace tailWord_2808301 prefixEnd_2808301 480669411834040747707455 := by
  unfold tailWord_2808301
  simp only [CollatzResearch.WordTrace]
  refine ⟨102427152199012571471440757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68284768132675047647627171 102427152199012571471440757)
  ·
    refine ⟨9602545518657428575447571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102427152199012571471440757 9602545518657428575447571)
    ·
      refine ⟨14403818277986142863171357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9602545518657428575447571 14403818277986142863171357)
      ·
        refine ⟨5401431854244803573689259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14403818277986142863171357 5401431854244803573689259)
        ·
          refine ⟨8102147781367205360533889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5401431854244803573689259 8102147781367205360533889)
          ·
            refine ⟨6076610836025404020400417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8102147781367205360533889 6076610836025404020400417)
            ·
              refine ⟨4557458127019053015300313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6076610836025404020400417 4557458127019053015300313)
              ·
                refine ⟨3418093595264289761475235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4557458127019053015300313 3418093595264289761475235)
                ·
                  refine ⟨5127140392896434642212853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3418093595264289761475235 5127140392896434642212853)
                  ·
                    refine ⟨480669411834040747707455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5127140392896434642212853 480669411834040747707455)
                    ·
                      rfl

theorem cell23_2808301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_2808301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808301 prefixEnd_2808301 := by exact prefixLift 2808301
  have htrace : WordTrace (prefixWord ++ tailWord_2808301) baseStart_2808301 baseEnd_2808301 := by
    simpa [prefixWord, tailWord_2808301, baseEnd_2808301] using wordTrace_append hprefix tailTrace_2808301
  have hstable : (prefixWord ++ tailWord_2808301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808301).length < 2 ^ (prefixWord ++ tailWord_2808301).sum := by decide
  have hdescent : baseEnd_2808301 < baseStart_2808301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808304 : List Nat := [2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 4]
def baseStart_2808304 : Nat := 118140960795 + 2808304 * 2 ^ 59
def prefixEnd_2808304 : Nat := 4983230072969 + 3 ^ 40 * 2808304 * 2
def baseEnd_2808304 : Nat := 1442009775944085731384851

theorem tailTrace_2808304 : CollatzResearch.WordTrace tailWord_2808304 prefixEnd_2808304 1442009775944085731384851 := by
  unfold tailWord_2808304
  simp only [CollatzResearch.WordTrace]
  refine ⟨51213630809000851491899983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68284841078667801989199977 51213630809000851491899983)
  ·
    refine ⟨76820446213501277237849975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51213630809000851491899983 76820446213501277237849975)
    ·
      refine ⟨115230669320251915856774963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76820446213501277237849975 115230669320251915856774963)
      ·
        refine ⟨172846003980377873785162445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115230669320251915856774963 172846003980377873785162445)
        ·
          refine ⟨64817251492641702669435917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172846003980377873785162445 64817251492641702669435917)
          ·
            refine ⟨24306469309740638501038469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64817251492641702669435917 24306469309740638501038469)
            ·
              refine ⟨4557462995576369718944713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24306469309740638501038469 4557462995576369718944713)
              ·
                refine ⟨3418097246682277289208535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4557462995576369718944713 3418097246682277289208535)
                ·
                  refine ⟨5127145870023415933812803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3418097246682277289208535 5127145870023415933812803)
                  ·
                    refine ⟨7690718805035123900719205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5127145870023415933812803 7690718805035123900719205)
                    ·
                      refine ⟨1442009775944085731384851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7690718805035123900719205 1442009775944085731384851)
                      ·
                        rfl

theorem cell23_2808304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 4].length) (baseStart_2808304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808304 prefixEnd_2808304 := by exact prefixLift 2808304
  have htrace : WordTrace (prefixWord ++ tailWord_2808304) baseStart_2808304 baseEnd_2808304 := by
    simpa [prefixWord, tailWord_2808304, baseEnd_2808304] using wordTrace_append hprefix tailTrace_2808304
  have hstable : (prefixWord ++ tailWord_2808304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808304).length < 2 ^ (prefixWord ++ tailWord_2808304).sum := by decide
  have hdescent : baseEnd_2808304 < baseStart_2808304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808317 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_2808317 : Nat := 118140960795 + 2808317 * 2 ^ 59
def prefixEnd_2808317 : Nat := 4983230072969 + 3 ^ 40 * 2808317 * 2
def baseEnd_2808317 : Nat := 1442016451192594180522291

theorem tailTrace_2808317 : CollatzResearch.WordTrace tailWord_2808317 prefixEnd_2808317 1442016451192594180522291 := by
  unfold tailWord_2808317
  simp only [CollatzResearch.WordTrace]
  refine ⟨102427735766954606204023205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68285157177969737469348803 102427735766954606204023205)
  ·
    refine ⟨19205200456303988663254351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102427735766954606204023205 19205200456303988663254351)
    ·
      refine ⟨28807800684455982994881527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19205200456303988663254351 28807800684455982994881527)
      ·
        refine ⟨43211701026683974492322291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28807800684455982994881527 43211701026683974492322291)
        ·
          refine ⟨64817551540025961738483437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43211701026683974492322291 64817551540025961738483437)
          ·
            refine ⟨24306581827509735651931289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64817551540025961738483437 24306581827509735651931289)
            ·
              refine ⟨18229936370632301738948467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24306581827509735651931289 18229936370632301738948467)
              ·
                refine ⟨27344904555948452608422701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18229936370632301738948467 27344904555948452608422701)
                ·
                  refine ⟨10254339208480669728158513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27344904555948452608422701 10254339208480669728158513)
                  ·
                    refine ⟨7690754406360502296118885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10254339208480669728158513 7690754406360502296118885)
                    ·
                      refine ⟨1442016451192594180522291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7690754406360502296118885 1442016451192594180522291)
                      ·
                        rfl

theorem cell23_2808317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_2808317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808317 prefixEnd_2808317 := by exact prefixLift 2808317
  have htrace : WordTrace (prefixWord ++ tailWord_2808317) baseStart_2808317 baseEnd_2808317 := by
    simpa [prefixWord, tailWord_2808317, baseEnd_2808317] using wordTrace_append hprefix tailTrace_2808317
  have hstable : (prefixWord ++ tailWord_2808317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808317).length < 2 ^ (prefixWord ++ tailWord_2808317).sum := by decide
  have hdescent : baseEnd_2808317 < baseStart_2808317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808324 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2808324 : Nat := 118140960795 + 2808324 * 2 ^ 59
def prefixEnd_2808324 : Nat := 4983230072969 + 3 ^ 40 * 2808324 * 2
def baseEnd_2808324 : Nat := 1442020045557175653134759

theorem tailTrace_2808324 : CollatzResearch.WordTrace tailWord_2808324 prefixEnd_2808324 1442020045557175653134759 := by
  unfold tailWord_2808324
  simp only [CollatzResearch.WordTrace]
  refine ⟨51213995538964623199764013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68285327385286164266352017 51213995538964623199764013)
  ·
    refine ⟨19205248327111733699911505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51213995538964623199764013 19205248327111733699911505)
    ·
      refine ⟨14403936245333800274933629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19205248327111733699911505 14403936245333800274933629)
      ·
        refine ⟨5401476092000175103100111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14403936245333800274933629 5401476092000175103100111)
        ·
          refine ⟨8102214138000262654650167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5401476092000175103100111 8102214138000262654650167)
          ·
            refine ⟨12153321207000393981975251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8102214138000262654650167 12153321207000393981975251)
            ·
              refine ⟨18229981810500590972962877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12153321207000393981975251 18229981810500590972962877)
              ·
                refine ⟨6836243178937721614861079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18229981810500590972962877 6836243178937721614861079)
                ·
                  refine ⟨10254364768406582422291619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6836243178937721614861079 10254364768406582422291619)
                  ·
                    refine ⟨15381547152609873633437429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10254364768406582422291619 15381547152609873633437429)
                    ·
                      refine ⟨1442020045557175653134759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15381547152609873633437429 1442020045557175653134759)
                      ·
                        rfl

theorem cell23_2808324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2808324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808324 prefixEnd_2808324 := by exact prefixLift 2808324
  have htrace : WordTrace (prefixWord ++ tailWord_2808324) baseStart_2808324 baseEnd_2808324 := by
    simpa [prefixWord, tailWord_2808324, baseEnd_2808324] using wordTrace_append hprefix tailTrace_2808324
  have hstable : (prefixWord ++ tailWord_2808324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808324).length < 2 ^ (prefixWord ++ tailWord_2808324).sum := by decide
  have hdescent : baseEnd_2808324 < baseStart_2808324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808337 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 3]
def baseStart_2808337 : Nat := 118140960795 + 2808337 * 2 ^ 59
def prefixEnd_2808337 : Nat := 4983230072969 + 3 ^ 40 * 2808337 * 2
def baseEnd_2808337 : Nat := 1442026720805684102272199

theorem tailTrace_2808337 : CollatzResearch.WordTrace tailWord_2808337 prefixEnd_2808337 1442026720805684102272199 := by
  unfold tailWord_2808337
  simp only [CollatzResearch.WordTrace]
  refine ⟨102428465226882149619751265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68285643484588099746500843 102428465226882149619751265)
  ·
    refine ⟨76821348920161612214813449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102428465226882149619751265 76821348920161612214813449)
    ·
      refine ⟨57616011690121209161110087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76821348920161612214813449 57616011690121209161110087)
      ·
        refine ⟨86424017535181813741665131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57616011690121209161110087 86424017535181813741665131)
        ·
          refine ⟨129636026302772720612497697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86424017535181813741665131 129636026302772720612497697)
          ·
            refine ⟨97227019727079540459373273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129636026302772720612497697 97227019727079540459373273)
            ·
              refine ⟨72920264795309655344529955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97227019727079540459373273 72920264795309655344529955)
              ·
                refine ⟨109380397192964483016794933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72920264795309655344529955 109380397192964483016794933)
                ·
                  refine ⟨10254412236840420282824525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109380397192964483016794933 10254412236840420282824525)
                  ·
                    refine ⟨3845404588815157606059197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10254412236840420282824525 3845404588815157606059197)
                    ·
                      refine ⟨1442026720805684102272199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3845404588815157606059197 1442026720805684102272199)
                      ·
                        rfl

theorem cell23_2808337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_2808337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808337 prefixEnd_2808337 := by exact prefixLift 2808337
  have htrace : WordTrace (prefixWord ++ tailWord_2808337) baseStart_2808337 baseEnd_2808337 := by
    simpa [prefixWord, tailWord_2808337, baseEnd_2808337] using wordTrace_append hprefix tailTrace_2808337
  have hstable : (prefixWord ++ tailWord_2808337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808337).length < 2 ^ (prefixWord ++ tailWord_2808337).sum := by decide
  have hdescent : baseEnd_2808337 < baseStart_2808337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808348 : List Nat := [2, 2, 3, 1, 2, 4, 2, 1, 2, 4]
def baseStart_2808348 : Nat := 118140960795 + 2808348 * 2 ^ 59
def prefixEnd_2808348 : Nat := 4983230072969 + 3 ^ 40 * 2808348 * 2
def baseEnd_2808348 : Nat := 480677456364294519744883

theorem tailTrace_2808348 : CollatzResearch.WordTrace tailWord_2808348 prefixEnd_2808348 480677456364294519744883 := by
  unfold tailWord_2808348
  simp only [CollatzResearch.WordTrace]
  refine ⟨51214433214921149249200849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68285910953228198998934465 51214433214921149249200849)
  ·
    refine ⟨38410824911190861936900637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51214433214921149249200849 38410824911190861936900637)
    ·
      refine ⟨14404059341696573226337739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38410824911190861936900637 14404059341696573226337739)
      ·
        refine ⟨21606089012544859839506609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14404059341696573226337739 21606089012544859839506609)
        ·
          refine ⟨16204566759408644879629957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21606089012544859839506609 16204566759408644879629957)
          ·
            refine ⟨3038356267389120914930617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16204566759408644879629957 3038356267389120914930617)
            ·
              refine ⟨2278767200541840686197963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3038356267389120914930617 2278767200541840686197963)
              ·
                refine ⟨3418150800812761029296945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278767200541840686197963 3418150800812761029296945)
                ·
                  refine ⟨2563613100609570771972709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3418150800812761029296945 2563613100609570771972709)
                  ·
                    refine ⟨480677456364294519744883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2563613100609570771972709 480677456364294519744883)
                    ·
                      rfl

theorem cell23_2808348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_2808348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808348 prefixEnd_2808348 := by exact prefixLift 2808348
  have htrace : WordTrace (prefixWord ++ tailWord_2808348) baseStart_2808348 baseEnd_2808348 := by
    simpa [prefixWord, tailWord_2808348, baseEnd_2808348] using wordTrace_append hprefix tailTrace_2808348
  have hstable : (prefixWord ++ tailWord_2808348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808348).length < 2 ^ (prefixWord ++ tailWord_2808348).sum := by decide
  have hdescent : baseEnd_2808348 < baseStart_2808348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808354 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_2808354 : Nat := 118140960795 + 2808354 * 2 ^ 59
def prefixEnd_2808354 : Nat := 4983230072969 + 3 ^ 40 * 2808354 * 2
def baseEnd_2808354 : Nat := 1442035449976810535759621

theorem tailTrace_2808354 : CollatzResearch.WordTrace tailWord_2808354 prefixEnd_2808354 1442035449976810535759621 := by
  unfold tailWord_2808354
  simp only [CollatzResearch.WordTrace]
  refine ⟨25607271316955140380780029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68286056845213707682080077 25607271316955140380780029)
  ·
    refine ⟨9602726743858177642792511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25607271316955140380780029 9602726743858177642792511)
    ·
      refine ⟨14404090115787266464188767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9602726743858177642792511 14404090115787266464188767)
      ·
        refine ⟨21606135173680899696283151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14404090115787266464188767 21606135173680899696283151)
        ·
          refine ⟨32409202760521349544424727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21606135173680899696283151 32409202760521349544424727)
          ·
            refine ⟨48613804140782024316637091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32409202760521349544424727 48613804140782024316637091)
            ·
              refine ⟨72920706211173036474955637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48613804140782024316637091 72920706211173036474955637)
              ·
                refine ⟨6836316207297472169527091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72920706211173036474955637 6836316207297472169527091)
                ·
                  refine ⟨10254474310946208254290637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6836316207297472169527091 10254474310946208254290637)
                  ·
                    refine ⟨3845427866604828095358989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10254474310946208254290637 3845427866604828095358989)
                    ·
                      refine ⟨1442035449976810535759621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3845427866604828095358989 1442035449976810535759621)
                      ·
                        rfl

theorem cell23_2808354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_2808354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808354 prefixEnd_2808354 := by exact prefixLift 2808354
  have htrace : WordTrace (prefixWord ++ tailWord_2808354) baseStart_2808354 baseEnd_2808354 := by
    simpa [prefixWord, tailWord_2808354, baseEnd_2808354] using wordTrace_append hprefix tailTrace_2808354
  have hstable : (prefixWord ++ tailWord_2808354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808354).length < 2 ^ (prefixWord ++ tailWord_2808354).sum := by decide
  have hdescent : baseEnd_2808354 < baseStart_2808354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808404 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_2808404 : Nat := 118140960795 + 2808404 * 2 ^ 59
def prefixEnd_2808404 : Nat := 4983230072969 + 3 ^ 40 * 2808404 * 2
def baseEnd_2808404 : Nat := 480687041336511780044797

theorem tailTrace_2808404 : CollatzResearch.WordTrace tailWord_2808404 prefixEnd_2808404 480687041336511780044797 := by
  unfold tailWord_2808404
  simp only [CollatzResearch.WordTrace]
  refine ⟨51215454458819710031220133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68287272611759613374960177 51215454458819710031220133)
  ·
    refine ⟨9602897711028695630853775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51215454458819710031220133 9602897711028695630853775)
    ·
      refine ⟨14404346566543043446280663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9602897711028695630853775 14404346566543043446280663)
      ·
        refine ⟨21606519849814565169420995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14404346566543043446280663 21606519849814565169420995)
        ·
          refine ⟨32409779774721847754131493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21606519849814565169420995 32409779774721847754131493)
          ·
            refine ⟨6076833707760346453899655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32409779774721847754131493 6076833707760346453899655)
            ·
              refine ⟨9115250561640519680849483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6076833707760346453899655 9115250561640519680849483)
              ·
                refine ⟨13672875842460779521274225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9115250561640519680849483 13672875842460779521274225)
                ·
                  refine ⟨10254656881845584640955669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13672875842460779521274225 10254656881845584640955669)
                  ·
                    refine ⟨480687041336511780044797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10254656881845584640955669 480687041336511780044797)
                    ·
                      rfl

theorem cell23_2808404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_2808404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808404 prefixEnd_2808404 := by exact prefixLift 2808404
  have htrace : WordTrace (prefixWord ++ tailWord_2808404) baseStart_2808404 baseEnd_2808404 := by
    simpa [prefixWord, tailWord_2808404, baseEnd_2808404] using wordTrace_append hprefix tailTrace_2808404
  have hstable : (prefixWord ++ tailWord_2808404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808404).length < 2 ^ (prefixWord ++ tailWord_2808404).sum := by decide
  have hdescent : baseEnd_2808404 < baseStart_2808404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808417 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 9]
def baseStart_2808417 : Nat := 118140960795 + 2808417 * 2 ^ 59
def prefixEnd_2808417 : Nat := 4983230072969 + 3 ^ 40 * 2808417 * 2
def baseEnd_2808417 : Nat := 160229755473115976585759

theorem tailTrace_2808417 : CollatzResearch.WordTrace tailWord_2808417 prefixEnd_2808417 160229755473115976585759 := by
  unfold tailWord_2808417
  simp only [CollatzResearch.WordTrace]
  refine ⟨102431383066592323282663505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68287588711061548855109003 102431383066592323282663505)
  ·
    refine ⟨76823537299944242461997629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102431383066592323282663505 76823537299944242461997629)
    ·
      refine ⟨28808826487479090923249111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76823537299944242461997629 28808826487479090923249111)
      ·
        refine ⟨43213239731218636384873667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28808826487479090923249111 43213239731218636384873667)
        ·
          refine ⟨64819859596827954577310501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43213239731218636384873667 64819859596827954577310501)
          ·
            refine ⟨12153723674405241483245719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64819859596827954577310501 12153723674405241483245719)
            ·
              refine ⟨18230585511607862224868579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12153723674405241483245719 18230585511607862224868579)
              ·
                refine ⟨27345878267411793337302869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18230585511607862224868579 27345878267411793337302869)
                ·
                  refine ⟨160229755473115976585759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27345878267411793337302869 160229755473115976585759)
                  ·
                    rfl

theorem cell23_2808417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 9].length) (baseStart_2808417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808417 prefixEnd_2808417 := by exact prefixLift 2808417
  have htrace : WordTrace (prefixWord ++ tailWord_2808417) baseStart_2808417 baseEnd_2808417 := by
    simpa [prefixWord, tailWord_2808417, baseEnd_2808417] using wordTrace_append hprefix tailTrace_2808417
  have hstable : (prefixWord ++ tailWord_2808417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808417).length < 2 ^ (prefixWord ++ tailWord_2808417).sum := by decide
  have hdescent : baseEnd_2808417 < baseStart_2808417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808432 : List Nat := [2, 1, 1, 1, 8, 1, 2, 1, 1, 3, 2]
def baseStart_2808432 : Nat := 118140960795 + 2808432 * 2 ^ 59
def prefixEnd_2808432 : Nat := 4983230072969 + 3 ^ 40 * 2808432 * 2
def baseEnd_2808432 : Nat := 1442075501467861230584263

theorem tailTrace_2808432 : CollatzResearch.WordTrace tailWord_2808432 prefixEnd_2808432 1442075501467861230584263 := by
  unfold tailWord_2808432
  simp only [CollatzResearch.WordTrace]
  refine ⟨51215965080768990422229775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68287953441025320562973033 51215965080768990422229775)
  ·
    refine ⟨76823947621153485633344663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51215965080768990422229775 76823947621153485633344663)
    ·
      refine ⟨115235921431730228450016995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76823947621153485633344663 115235921431730228450016995)
      ·
        refine ⟨172853882147595342675025493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115235921431730228450016995 172853882147595342675025493)
        ·
          refine ⟨2025631431417132921972955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 172853882147595342675025493 2025631431417132921972955)
          ·
            refine ⟨3038447147125699382959433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2025631431417132921972955 3038447147125699382959433)
            ·
              refine ⟨2278835360344274537219575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3038447147125699382959433 2278835360344274537219575)
              ·
                refine ⟨3418253040516411805829363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278835360344274537219575 3418253040516411805829363)
                ·
                  refine ⟨5127379560774617708744045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3418253040516411805829363 5127379560774617708744045)
                  ·
                    refine ⟨1922767335290481640779017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5127379560774617708744045 1922767335290481640779017)
                    ·
                      refine ⟨1442075501467861230584263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1922767335290481640779017 1442075501467861230584263)
                      ·
                        rfl

theorem cell23_2808432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 1, 3, 2].length) (baseStart_2808432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808432 prefixEnd_2808432 := by exact prefixLift 2808432
  have htrace : WordTrace (prefixWord ++ tailWord_2808432) baseStart_2808432 baseEnd_2808432 := by
    simpa [prefixWord, tailWord_2808432, baseEnd_2808432] using wordTrace_append hprefix tailTrace_2808432
  have hstable : (prefixWord ++ tailWord_2808432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808432).length < 2 ^ (prefixWord ++ tailWord_2808432).sum := by decide
  have hdescent : baseEnd_2808432 < baseStart_2808432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808444 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 2, 3, 3]
def baseStart_2808444 : Nat := 118140960795 + 2808444 * 2 ^ 59
def prefixEnd_2808444 : Nat := 4983230072969 + 3 ^ 40 * 2808444 * 2
def baseEnd_2808444 : Nat := 1442081663235715183634207

theorem tailTrace_2808444 : CollatzResearch.WordTrace tailWord_2808444 prefixEnd_2808444 1442081663235715183634207 := by
  unfold tailWord_2808444
  simp only [CollatzResearch.WordTrace]
  refine ⟨51216183918747253446948193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68288245224996337929264257 51216183918747253446948193)
  ·
    refine ⟨38412137939060440085211145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51216183918747253446948193 38412137939060440085211145)
    ·
      refine ⟨28809103454295330063908359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38412137939060440085211145 28809103454295330063908359)
      ·
        refine ⟨43213655181442995095862539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28809103454295330063908359 43213655181442995095862539)
        ·
          refine ⟨64820482772164492643793809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43213655181442995095862539 64820482772164492643793809)
          ·
            refine ⟨48615362079123369482845357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64820482772164492643793809 48615362079123369482845357)
            ·
              refine ⟨18230760779671263556067009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48615362079123369482845357 18230760779671263556067009)
              ·
                refine ⟨13673070584753447667050257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18230760779671263556067009 13673070584753447667050257)
                ·
                  refine ⟨10254802938565085750287693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13673070584753447667050257 10254802938565085750287693)
                  ·
                    refine ⟨3845551101961907156357885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10254802938565085750287693 3845551101961907156357885)
                    ·
                      refine ⟨1442081663235715183634207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3845551101961907156357885 1442081663235715183634207)
                      ·
                        rfl

theorem cell23_2808444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_2808444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808444 prefixEnd_2808444 := by exact prefixLift 2808444
  have htrace : WordTrace (prefixWord ++ tailWord_2808444) baseStart_2808444 baseEnd_2808444 := by
    simpa [prefixWord, tailWord_2808444, baseEnd_2808444] using wordTrace_append hprefix tailTrace_2808444
  have hstable : (prefixWord ++ tailWord_2808444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808444).length < 2 ^ (prefixWord ++ tailWord_2808444).sum := by decide
  have hdescent : baseEnd_2808444 < baseStart_2808444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808457 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 7]
def baseStart_2808457 : Nat := 118140960795 + 2808457 * 2 ^ 59
def prefixEnd_2808457 : Nat := 4983230072969 + 3 ^ 40 * 2808457 * 2
def baseEnd_2808457 : Nat := 1442088338484223632771647

theorem tailTrace_2808457 : CollatzResearch.WordTrace tailWord_2808457 prefixEnd_2808457 1442088338484223632771647 := by
  unfold tailWord_2808457
  simp only [CollatzResearch.WordTrace]
  refine ⟨102432841986447410114119625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68288561324298273409413083 102432841986447410114119625)
  ·
    refine ⟨76824631489835557585589719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102432841986447410114119625 76824631489835557585589719)
    ·
      refine ⟨115236947234753336378384579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76824631489835557585589719 115236947234753336378384579)
      ·
        refine ⟨172855420852130004567576869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115236947234753336378384579 172855420852130004567576869)
        ·
          refine ⟨32410391409774375856420663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172855420852130004567576869 32410391409774375856420663)
          ·
            refine ⟨48615587114661563784630995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32410391409774375856420663 48615587114661563784630995)
            ·
              refine ⟨72923380671992345676946493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48615587114661563784630995 72923380671992345676946493)
              ·
                refine ⟨27346267751997129628854935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72923380671992345676946493 27346267751997129628854935)
                ·
                  refine ⟨41019401627995694443282403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27346267751997129628854935 41019401627995694443282403)
                  ·
                    refine ⟨61529102441993541664923605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41019401627995694443282403 61529102441993541664923605)
                    ·
                      refine ⟨1442088338484223632771647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61529102441993541664923605 1442088338484223632771647)
                      ·
                        rfl

theorem cell23_2808457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_2808457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808457 prefixEnd_2808457 := by exact prefixLift 2808457
  have htrace : WordTrace (prefixWord ++ tailWord_2808457) baseStart_2808457 baseEnd_2808457 := by
    simpa [prefixWord, tailWord_2808457, baseEnd_2808457] using wordTrace_append hprefix tailTrace_2808457
  have hstable : (prefixWord ++ tailWord_2808457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808457).length < 2 ^ (prefixWord ++ tailWord_2808457).sum := by decide
  have hdescent : baseEnd_2808457 < baseStart_2808457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808484 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_2808484 : Nat := 118140960795 + 2808484 * 2 ^ 59
def prefixEnd_2808484 : Nat := 4983230072969 + 3 ^ 40 * 2808484 * 2
def baseEnd_2808484 : Nat := 1442102202461895027134023

theorem tailTrace_2808484 : CollatzResearch.WordTrace tailWord_2808484 prefixEnd_2808484 1442102202461895027134023 := by
  unfold tailWord_2808484
  simp only [CollatzResearch.WordTrace]
  refine ⟨51216913378674796862676253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68289217838233062483568337 51216913378674796862676253)
  ·
    refine ⟨19206342517003048823503595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51216913378674796862676253 19206342517003048823503595)
    ·
      refine ⟨28809513775504573235255393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19206342517003048823503595 28809513775504573235255393)
      ·
        refine ⟨21607135331628429926441545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28809513775504573235255393 21607135331628429926441545)
        ·
          refine ⟨16205351498721322444831159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21607135331628429926441545 16205351498721322444831159)
          ·
            refine ⟨24308027248081983667246739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16205351498721322444831159 24308027248081983667246739)
            ·
              refine ⟨36462040872122975500870109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24308027248081983667246739 36462040872122975500870109)
              ·
                refine ⟨13673265327046115812826291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36462040872122975500870109 13673265327046115812826291)
                ·
                  refine ⟨20509897990569173719239437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13673265327046115812826291 20509897990569173719239437)
                  ·
                    refine ⟨7691211746463440144714789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20509897990569173719239437 7691211746463440144714789)
                    ·
                      refine ⟨1442102202461895027134023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7691211746463440144714789 1442102202461895027134023)
                      ·
                        rfl

theorem cell23_2808484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_2808484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808484 prefixEnd_2808484 := by exact prefixLift 2808484
  have htrace : WordTrace (prefixWord ++ tailWord_2808484) baseStart_2808484 baseEnd_2808484 := by
    simpa [prefixWord, tailWord_2808484, baseEnd_2808484] using wordTrace_append hprefix tailTrace_2808484
  have hstable : (prefixWord ++ tailWord_2808484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808484).length < 2 ^ (prefixWord ++ tailWord_2808484).sum := by decide
  have hdescent : baseEnd_2808484 < baseStart_2808484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808501 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2808501 : Nat := 118140960795 + 2808501 * 2 ^ 59
def prefixEnd_2808501 : Nat := 4983230072969 + 3 ^ 40 * 2808501 * 2
def baseEnd_2808501 : Nat := 1442110931633021460621445

theorem tailTrace_2808501 : CollatzResearch.WordTrace tailWord_2808501 prefixEnd_2808501 1442110931633021460621445 := by
  unfold tailWord_2808501
  simp only [CollatzResearch.WordTrace]
  refine ⟨102434446798288005628721357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68289631198858670419147571 102434446798288005628721357)
  ·
    refine ⟨38412917549358002110770509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102434446798288005628721357 38412917549358002110770509)
    ·
      refine ⟨14404844081009250791538941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38412917549358002110770509 14404844081009250791538941)
      ·
        refine ⟨5401816530378469046827103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14404844081009250791538941 5401816530378469046827103)
        ·
          refine ⟨8102724795567703570240655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5401816530378469046827103 8102724795567703570240655)
          ·
            refine ⟨12154087193351555355360983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8102724795567703570240655 12154087193351555355360983)
            ·
              refine ⟨18231130790027333033041475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12154087193351555355360983 18231130790027333033041475)
              ·
                refine ⟨27346696185040999549562213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18231130790027333033041475 27346696185040999549562213)
                ·
                  refine ⟨5127505534695187415542915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27346696185040999549562213 5127505534695187415542915)
                  ·
                    refine ⟨7691258302042781123314373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5127505534695187415542915 7691258302042781123314373)
                    ·
                      refine ⟨1442110931633021460621445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7691258302042781123314373 1442110931633021460621445)
                      ·
                        rfl

theorem cell23_2808501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2808501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808501 prefixEnd_2808501 := by exact prefixLift 2808501
  have htrace : WordTrace (prefixWord ++ tailWord_2808501) baseStart_2808501 baseEnd_2808501 := by
    simpa [prefixWord, tailWord_2808501, baseEnd_2808501] using wordTrace_append hprefix tailTrace_2808501
  have hstable : (prefixWord ++ tailWord_2808501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808501).length < 2 ^ (prefixWord ++ tailWord_2808501).sum := by decide
  have hdescent : baseEnd_2808501 < baseStart_2808501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808502 : List Nat := [5, 1, 3, 1, 2, 1, 3, 2, 5]
def baseStart_2808502 : Nat := 118140960795 + 2808502 * 2 ^ 59
def prefixEnd_2808502 : Nat := 4983230072969 + 3 ^ 40 * 2808502 * 2
def baseEnd_2808502 : Nat := 160234605012630661856549

theorem tailTrace_2808502 : CollatzResearch.WordTrace tailWord_2808502 prefixEnd_2808502 160234605012630661856549 := by
  unfold tailWord_2808502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6402155204455273924969235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68289655514189588533005173 6402155204455273924969235)
  ·
    refine ⟨9603232806682910887453853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6402155204455273924969235 9603232806682910887453853)
    ·
      refine ⟨3601212302506091582795195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9603232806682910887453853 3601212302506091582795195)
      ·
        refine ⟨5401818453759137374192793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3601212302506091582795195 5401818453759137374192793)
        ·
          refine ⟨4051363840319353030644595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5401818453759137374192793 4051363840319353030644595)
          ·
            refine ⟨6077045760479029545966893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051363840319353030644595 6077045760479029545966893)
            ·
              refine ⟨2278892160179636079737585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6077045760479029545966893 2278892160179636079737585)
              ·
                refine ⟨1709169120134727059803189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2278892160179636079737585 1709169120134727059803189)
                ·
                  refine ⟨160234605012630661856549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1709169120134727059803189 160234605012630661856549)
                  ·
                    rfl

theorem cell23_2808502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_2808502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808502 prefixEnd_2808502 := by exact prefixLift 2808502
  have htrace : WordTrace (prefixWord ++ tailWord_2808502) baseStart_2808502 baseEnd_2808502 := by
    simpa [prefixWord, tailWord_2808502, baseEnd_2808502] using wordTrace_append hprefix tailTrace_2808502
  have hstable : (prefixWord ++ tailWord_2808502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808502).length < 2 ^ (prefixWord ++ tailWord_2808502).sum := by decide
  have hdescent : baseEnd_2808502 < baseStart_2808502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808511 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 3, 4]
def baseStart_2808511 : Nat := 118140960795 + 2808511 * 2 ^ 59
def prefixEnd_2808511 : Nat := 4983230072969 + 3 ^ 40 * 2808511 * 2
def baseEnd_2808511 : Nat := 480705355479855473832133

theorem tailTrace_2808511 : CollatzResearch.WordTrace tailWord_2808511 prefixEnd_2808511 480705355479855473832133 := by
  unfold tailWord_2808511
  simp only [CollatzResearch.WordTrace]
  refine ⟨102434811528251777336585387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68289874352167851557723591 102434811528251777336585387)
  ·
    refine ⟨153652217292377666004878081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102434811528251777336585387 153652217292377666004878081)
    ·
      refine ⟨115239162969283249503658561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153652217292377666004878081 115239162969283249503658561)
      ·
        refine ⟨86429372226962437127743921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115239162969283249503658561 86429372226962437127743921)
        ·
          refine ⟨64822029170221827845807941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86429372226962437127743921 64822029170221827845807941)
          ·
            refine ⟨12154130469416592721088989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64822029170221827845807941 12154130469416592721088989)
            ·
              refine ⟨4557798926031222270408371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12154130469416592721088989 4557798926031222270408371)
              ·
                refine ⟨6836698389046833405612557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4557798926031222270408371 6836698389046833405612557)
                ·
                  refine ⟨2563761895892562527104709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6836698389046833405612557 2563761895892562527104709)
                  ·
                    refine ⟨480705355479855473832133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2563761895892562527104709 480705355479855473832133)
                    ·
                      rfl

theorem cell23_2808511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 4].length) (baseStart_2808511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808511 prefixEnd_2808511 := by exact prefixLift 2808511
  have htrace : WordTrace (prefixWord ++ tailWord_2808511) baseStart_2808511 baseEnd_2808511 := by
    simpa [prefixWord, tailWord_2808511, baseEnd_2808511] using wordTrace_append hprefix tailTrace_2808511
  have hstable : (prefixWord ++ tailWord_2808511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808511).length < 2 ^ (prefixWord ++ tailWord_2808511).sum := by decide
  have hdescent : baseEnd_2808511 < baseStart_2808511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808562 : List Nat := [3, 2, 1, 3, 1, 4, 2, 2, 1, 4]
def baseStart_2808562 : Nat := 118140960795 + 2808562 * 2 ^ 59
def prefixEnd_2808562 : Nat := 4983230072969 + 3 ^ 40 * 2808562 * 2
def baseEnd_2808562 : Nat := 480714084650981907319555

theorem tailTrace_2808562 : CollatzResearch.WordTrace tailWord_2808562 prefixEnd_2808562 480714084650981907319555 := by
  unfold tailWord_2808562
  simp only [CollatzResearch.WordTrace]
  refine ⟨25609167912766753261672985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68291114434044675364461293 25609167912766753261672985)
  ·
    refine ⟨19206875934575064946254739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25609167912766753261672985 19206875934575064946254739)
    ·
      refine ⟨28810313901862597419382109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19206875934575064946254739 28810313901862597419382109)
      ·
        refine ⟨10803867713198474032268291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28810313901862597419382109 10803867713198474032268291)
        ·
          refine ⟨16205801569797711048402437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10803867713198474032268291 16205801569797711048402437)
          ·
            refine ⟨3038587794337070821575457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16205801569797711048402437 3038587794337070821575457)
            ·
              refine ⟨2278940845752803116181593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3038587794337070821575457 2278940845752803116181593)
              ·
                refine ⟨1709205634314602337136195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2278940845752803116181593 1709205634314602337136195)
                ·
                  refine ⟨2563808451471903505704293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1709205634314602337136195 2563808451471903505704293)
                  ·
                    refine ⟨480714084650981907319555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2563808451471903505704293 480714084650981907319555)
                    ·
                      rfl

theorem cell23_2808562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_2808562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808562 prefixEnd_2808562 := by exact prefixLift 2808562
  have htrace : WordTrace (prefixWord ++ tailWord_2808562) baseStart_2808562 baseEnd_2808562 := by
    simpa [prefixWord, tailWord_2808562, baseEnd_2808562] using wordTrace_append hprefix tailTrace_2808562
  have hstable : (prefixWord ++ tailWord_2808562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808562).length < 2 ^ (prefixWord ++ tailWord_2808562).sum := by decide
  have hdescent : baseEnd_2808562 < baseStart_2808562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808591 : List Nat := [1, 1, 2, 1, 1, 1, 6, 4, 1, 1, 4]
def baseStart_2808591 : Nat := 118140960795 + 2808591 * 2 ^ 59
def prefixEnd_2808591 : Nat := 4983230072969 + 3 ^ 40 * 2808591 * 2
def baseEnd_2808591 : Nat := 1442157144891926108496031

theorem tailTrace_2808591 : CollatzResearch.WordTrace tailWord_2808591 prefixEnd_2808591 1442157144891926108496031 := by
  unfold tailWord_2808591
  simp only [CollatzResearch.WordTrace]
  refine ⟨102437729367961950999497627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68291819578641300666331751 102437729367961950999497627)
  ·
    refine ⟨153656594051942926499246441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102437729367961950999497627 153656594051942926499246441)
    ·
      refine ⟨115242445538957194874434831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153656594051942926499246441 115242445538957194874434831)
      ·
        refine ⟨172863668308435792311652247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115242445538957194874434831 172863668308435792311652247)
        ·
          refine ⟨259295502462653688467478371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172863668308435792311652247 259295502462653688467478371)
          ·
            refine ⟨388943253693980532701217557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259295502462653688467478371 388943253693980532701217557)
            ·
              refine ⟨18231715016905337470369573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 388943253693980532701217557 18231715016905337470369573)
              ·
                refine ⟨3418446565669750775694295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18231715016905337470369573 3418446565669750775694295)
                ·
                  refine ⟨5127669848504626163541443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3418446565669750775694295 5127669848504626163541443)
                  ·
                    refine ⟨7691504772756939245312165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5127669848504626163541443 7691504772756939245312165)
                    ·
                      refine ⟨1442157144891926108496031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7691504772756939245312165 1442157144891926108496031)
                      ·
                        rfl

theorem cell23_2808591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 1, 4].length) (baseStart_2808591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808591 prefixEnd_2808591 := by exact prefixLift 2808591
  have htrace : WordTrace (prefixWord ++ tailWord_2808591) baseStart_2808591 baseEnd_2808591 := by
    simpa [prefixWord, tailWord_2808591, baseEnd_2808591] using wordTrace_append hprefix tailTrace_2808591
  have hstable : (prefixWord ++ tailWord_2808591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808591).length < 2 ^ (prefixWord ++ tailWord_2808591).sum := by decide
  have hdescent : baseEnd_2808591 < baseStart_2808591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808605 : List Nat := [1, 4, 2, 4, 1, 1, 1, 3, 1, 5]
def baseStart_2808605 : Nat := 118140960795 + 2808605 * 2 ^ 59
def prefixEnd_2808605 : Nat := 4983230072969 + 3 ^ 40 * 2808605 * 2
def baseEnd_2808605 : Nat := 480721444540363017906989

theorem tailTrace_2808605 : CollatzResearch.WordTrace tailWord_2808605 prefixEnd_2808605 480721444540363017906989 := by
  unfold tailWord_2808605
  simp only [CollatzResearch.WordTrace]
  refine ⟨102438239989911231390507269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68292159993274154260338179 102438239989911231390507269)
  ·
    refine ⟨19207169998108355885720113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102438239989911231390507269 19207169998108355885720113)
    ·
      refine ⟨14405377498581266914290085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19207169998108355885720113 14405377498581266914290085)
      ·
        refine ⟨2701008280983987546429391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14405377498581266914290085 2701008280983987546429391)
        ·
          refine ⟨4051512421475981319644087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2701008280983987546429391 4051512421475981319644087)
          ·
            refine ⟨6077268632213971979466131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051512421475981319644087 6077268632213971979466131)
            ·
              refine ⟨9115902948320957969199197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6077268632213971979466131 9115902948320957969199197)
              ·
                refine ⟨3418463605620359238449699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9115902948320957969199197 3418463605620359238449699)
                ·
                  refine ⟨5127695408430538857674549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3418463605620359238449699 5127695408430538857674549)
                  ·
                    refine ⟨480721444540363017906989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5127695408430538857674549 480721444540363017906989)
                    ·
                      rfl

theorem cell23_2808605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_2808605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808605 prefixEnd_2808605 := by exact prefixLift 2808605
  have htrace : WordTrace (prefixWord ++ tailWord_2808605) baseStart_2808605 baseEnd_2808605 := by
    simpa [prefixWord, tailWord_2808605, baseEnd_2808605] using wordTrace_append hprefix tailTrace_2808605
  have hstable : (prefixWord ++ tailWord_2808605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808605).length < 2 ^ (prefixWord ++ tailWord_2808605).sum := by decide
  have hdescent : baseEnd_2808605 < baseStart_2808605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808608 : List Nat := [2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 4]
def baseStart_2808608 : Nat := 118140960795 + 2808608 * 2 ^ 59
def prefixEnd_2808608 : Nat := 4983230072969 + 3 ^ 40 * 2808608 * 2
def baseEnd_2808608 : Nat := 1442165874063052541983453

theorem tailTrace_2808608 : CollatzResearch.WordTrace tailWord_2808608 prefixEnd_2808608 1442165874063052541983453 := by
  unfold tailWord_2808608
  simp only [CollatzResearch.WordTrace]
  refine ⟨51219174704450181451433239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68292232939266908601910985 51219174704450181451433239)
  ·
    refine ⟨76828762056675272177149859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51219174704450181451433239 76828762056675272177149859)
    ·
      refine ⟨115243143085012908265724789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76828762056675272177149859 115243143085012908265724789)
      ·
        refine ⟨10804044664219960149911699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115243143085012908265724789 10804044664219960149911699)
        ·
          refine ⟨16206066996329940224867549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10804044664219960149911699 16206066996329940224867549)
          ·
            refine ⟨6077275123623727584325331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16206066996329940224867549 6077275123623727584325331)
            ·
              refine ⟨9115912685435591376487997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6077275123623727584325331 9115912685435591376487997)
              ·
                refine ⟨3418467257038346766182999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9115912685435591376487997 3418467257038346766182999)
                ·
                  refine ⟨5127700885557520149274499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3418467257038346766182999 5127700885557520149274499)
                  ·
                    refine ⟨7691551328336280223911749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5127700885557520149274499 7691551328336280223911749)
                    ·
                      refine ⟨1442165874063052541983453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7691551328336280223911749 1442165874063052541983453)
                      ·
                        rfl

theorem cell23_2808608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_2808608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808608 prefixEnd_2808608 := by exact prefixLift 2808608
  have htrace : WordTrace (prefixWord ++ tailWord_2808608) baseStart_2808608 baseEnd_2808608 := by
    simpa [prefixWord, tailWord_2808608, baseEnd_2808608] using wordTrace_append hprefix tailTrace_2808608
  have hstable : (prefixWord ++ tailWord_2808608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808608).length < 2 ^ (prefixWord ++ tailWord_2808608).sum := by decide
  have hdescent : baseEnd_2808608 < baseStart_2808608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808625 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 3, 2, 2]
def baseStart_2808625 : Nat := 118140960795 + 2808625 * 2 ^ 59
def prefixEnd_2808625 : Nat := 4983230072969 + 3 ^ 40 * 2808625 * 2
def baseEnd_2808625 : Nat := 1442174603234178975470875

theorem tailTrace_2808625 : CollatzResearch.WordTrace tailWord_2808625 prefixEnd_2808625 1442174603234178975470875 := by
  unfold tailWord_2808625
  simp only [CollatzResearch.WordTrace]
  refine ⟨102438969449838774806235329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68292646299892516537490219 102438969449838774806235329)
  ·
    refine ⟨76829227087379081104676497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102438969449838774806235329 76829227087379081104676497)
    ·
      refine ⟨57621920315534310828507373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76829227087379081104676497 57621920315534310828507373)
      ·
        refine ⟨21608220118325366560690265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57621920315534310828507373 21608220118325366560690265)
        ·
          refine ⟨16206165088744024920517699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21608220118325366560690265 16206165088744024920517699)
          ·
            refine ⟨24309247633116037380776549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16206165088744024920517699 24309247633116037380776549)
            ·
              refine ⟨4557983931209257008895603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24309247633116037380776549 4557983931209257008895603)
              ·
                refine ⟨6836975896813885513343405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4557983931209257008895603 6836975896813885513343405)
                ·
                  refine ⟨2563865961305207067503777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6836975896813885513343405 2563865961305207067503777)
                  ·
                    refine ⟨1922899470978905300627833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2563865961305207067503777 1922899470978905300627833)
                    ·
                      refine ⟨1442174603234178975470875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1922899470978905300627833 1442174603234178975470875)
                      ·
                        rfl

theorem cell23_2808625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_2808625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808625 prefixEnd_2808625 := by exact prefixLift 2808625
  have htrace : WordTrace (prefixWord ++ tailWord_2808625) baseStart_2808625 baseEnd_2808625 := by
    simpa [prefixWord, tailWord_2808625, baseEnd_2808625] using wordTrace_append hprefix tailTrace_2808625
  have hstable : (prefixWord ++ tailWord_2808625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808625).length < 2 ^ (prefixWord ++ tailWord_2808625).sum := by decide
  have hdescent : baseEnd_2808625 < baseStart_2808625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808638 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_2808638 : Nat := 118140960795 + 2808638 * 2 ^ 59
def prefixEnd_2808638 : Nat := 4983230072969 + 3 ^ 40 * 2808638 * 2
def baseEnd_2808638 : Nat := 1442181278482687424608315

theorem tailTrace_2808638 : CollatzResearch.WordTrace tailWord_2808638 prefixEnd_2808638 1442181278482687424608315 := by
  unfold tailWord_2808638
  simp only [CollatzResearch.WordTrace]
  refine ⟨12804930449848959753307321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68292962399194452017639045 12804930449848959753307321)
  ·
    refine ⟨9603697837386719814980491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12804930449848959753307321 9603697837386719814980491)
    ·
      refine ⟨14405546756080079722470737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9603697837386719814980491 14405546756080079722470737)
      ·
        refine ⟨10804160067060059791853053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14405546756080079722470737 10804160067060059791853053)
        ·
          refine ⟨4051560025147522421944895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10804160067060059791853053 4051560025147522421944895)
          ·
            refine ⟨6077340037721283632917343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051560025147522421944895 6077340037721283632917343)
            ·
              refine ⟨9116010056581925449376015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6077340037721283632917343 9116010056581925449376015)
              ·
                refine ⟨13674015084872888174064023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9116010056581925449376015 13674015084872888174064023)
                ·
                  refine ⟨20511022627309332261096035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13674015084872888174064023 20511022627309332261096035)
                  ·
                    refine ⟨30766533940963998391644053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20511022627309332261096035 30766533940963998391644053)
                    ·
                      refine ⟨1442181278482687424608315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30766533940963998391644053 1442181278482687424608315)
                      ·
                        rfl

theorem cell23_2808638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_2808638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808638 prefixEnd_2808638 := by exact prefixLift 2808638
  have htrace : WordTrace (prefixWord ++ tailWord_2808638) baseStart_2808638 baseEnd_2808638 := by
    simpa [prefixWord, tailWord_2808638, baseEnd_2808638] using wordTrace_append hprefix tailTrace_2808638
  have hstable : (prefixWord ++ tailWord_2808638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808638).length < 2 ^ (prefixWord ++ tailWord_2808638).sum := by decide
  have hdescent : baseEnd_2808638 < baseStart_2808638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808651 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 4, 7, 2]
def baseStart_2808651 : Nat := 118140960795 + 2808651 * 2 ^ 59
def prefixEnd_2808651 : Nat := 4983230072969 + 3 ^ 40 * 2808651 * 2
def baseEnd_2808651 : Nat := 1442187953731195873745755

theorem tailTrace_2808651 : CollatzResearch.WordTrace tailWord_2808651 prefixEnd_2808651 1442187953731195873745755 := by
  unfold tailWord_2808651
  simp only [CollatzResearch.WordTrace]
  refine ⟨102439917747744581246681807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68293278498496387497787871 102439917747744581246681807)
  ·
    refine ⟨153659876621616871870022711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102439917747744581246681807 153659876621616871870022711)
    ·
      refine ⟨230489814932425307805034067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153659876621616871870022711 230489814932425307805034067)
      ·
        refine ⟨345734722398637961707551101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230489814932425307805034067 345734722398637961707551101)
        ·
          refine ⟨129650520899489235640331663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345734722398637961707551101 129650520899489235640331663)
          ·
            refine ⟨194475781349233853460497495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129650520899489235640331663 194475781349233853460497495)
            ·
              refine ⟨291713672023850780190746243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194475781349233853460497495 291713672023850780190746243)
              ·
                refine ⟨437570508035776170286119365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291713672023850780190746243 437570508035776170286119365)
                ·
                  refine ⟨82044470256708031928647381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 437570508035776170286119365 82044470256708031928647381)
                  ·
                    refine ⟨1922917271641594498327673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 82044470256708031928647381 1922917271641594498327673)
                    ·
                      refine ⟨1442187953731195873745755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1922917271641594498327673 1442187953731195873745755)
                      ·
                        rfl

theorem cell23_2808651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 7, 2].length) (baseStart_2808651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808651 prefixEnd_2808651 := by exact prefixLift 2808651
  have htrace : WordTrace (prefixWord ++ tailWord_2808651) baseStart_2808651 baseEnd_2808651 := by
    simpa [prefixWord, tailWord_2808651, baseEnd_2808651] using wordTrace_append hprefix tailTrace_2808651
  have hstable : (prefixWord ++ tailWord_2808651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808651).length < 2 ^ (prefixWord ++ tailWord_2808651).sum := by decide
  have hdescent : baseEnd_2808651 < baseStart_2808651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808658 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_2808658 : Nat := 118140960795 + 2808658 * 2 ^ 59
def prefixEnd_2808658 : Nat := 4983230072969 + 3 ^ 40 * 2808658 * 2
def baseEnd_2808658 : Nat := 1442191548095777346358223

theorem tailTrace_2808658 : CollatzResearch.WordTrace tailWord_2808658 prefixEnd_2808658 1442191548095777346358223 := by
  unfold tailWord_2808658
  simp only [CollatzResearch.WordTrace]
  refine ⟨25610043264679805360546657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68293448705812814294791085 25610043264679805360546657)
  ·
    refine ⟨19207532448509854020409993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25610043264679805360546657 19207532448509854020409993)
    ·
      refine ⟨14405649336382390515307495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19207532448509854020409993 14405649336382390515307495)
      ·
        refine ⟨21608474004573585772961243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14405649336382390515307495 21608474004573585772961243)
        ·
          refine ⟨32412711006860378659441865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21608474004573585772961243 32412711006860378659441865)
          ·
            refine ⟨24309533255145283994581399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32412711006860378659441865 24309533255145283994581399)
            ·
              refine ⟨36464299882717925991872099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24309533255145283994581399 36464299882717925991872099)
              ·
                refine ⟨54696449824076888987808149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36464299882717925991872099 54696449824076888987808149)
                ·
                  refine ⟨2563896085503604171303507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54696449824076888987808149 2563896085503604171303507)
                  ·
                    refine ⟨3845844128255406256955261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2563896085503604171303507 3845844128255406256955261)
                    ·
                      refine ⟨1442191548095777346358223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3845844128255406256955261 1442191548095777346358223)
                      ·
                        rfl

theorem cell23_2808658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_2808658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808658 prefixEnd_2808658 := by exact prefixLift 2808658
  have htrace : WordTrace (prefixWord ++ tailWord_2808658) baseStart_2808658 baseEnd_2808658 := by
    simpa [prefixWord, tailWord_2808658, baseEnd_2808658] using wordTrace_append hprefix tailTrace_2808658
  have hstable : (prefixWord ++ tailWord_2808658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808658).length < 2 ^ (prefixWord ++ tailWord_2808658).sum := by decide
  have hdescent : baseEnd_2808658 < baseStart_2808658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808664 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 1, 2, 8]
def baseStart_2808664 : Nat := 118140960795 + 2808664 * 2 ^ 59
def prefixEnd_2808664 : Nat := 4983230072969 + 3 ^ 40 * 2808664 * 2
def baseEnd_2808664 : Nat := 1442194628979704322883195

theorem tailTrace_2808664 : CollatzResearch.WordTrace tailWord_2808664 prefixEnd_2808664 1442194628979704322883195 := by
  unfold tailWord_2808664
  simp only [CollatzResearch.WordTrace]
  refine ⟨51220195948348742233452523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68293594597798322977936697 51220195948348742233452523)
  ·
    refine ⟨76830293922523113350178785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51220195948348742233452523 76830293922523113350178785)
    ·
      refine ⟨57622720441892335012634089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76830293922523113350178785 57622720441892335012634089)
      ·
        refine ⟨43217040331419251259475567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57622720441892335012634089 43217040331419251259475567)
        ·
          refine ⟨64825560497128876889213351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43217040331419251259475567 64825560497128876889213351)
          ·
            refine ⟨97238340745693315333820027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64825560497128876889213351 97238340745693315333820027)
            ·
              refine ⟨145857511118539973000730041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97238340745693315333820027 145857511118539973000730041)
              ·
                refine ⟨109393133338904979750547531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145857511118539973000730041 109393133338904979750547531)
                ·
                  refine ⟨164089700008357469625821297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109393133338904979750547531 164089700008357469625821297)
                  ·
                    refine ⟨123067275006268102219365973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 164089700008357469625821297 123067275006268102219365973)
                    ·
                      refine ⟨1442194628979704322883195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 123067275006268102219365973 1442194628979704322883195)
                      ·
                        rfl

theorem cell23_2808664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_2808664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808664 prefixEnd_2808664 := by exact prefixLift 2808664
  have htrace : WordTrace (prefixWord ++ tailWord_2808664) baseStart_2808664 baseEnd_2808664 := by
    simpa [prefixWord, tailWord_2808664, baseEnd_2808664] using wordTrace_append hprefix tailTrace_2808664
  have hstable : (prefixWord ++ tailWord_2808664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808664).length < 2 ^ (prefixWord ++ tailWord_2808664).sum := by decide
  have hdescent : baseEnd_2808664 < baseStart_2808664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808698 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2]
def baseStart_2808698 : Nat := 118140960795 + 2808698 * 2 ^ 59
def prefixEnd_2808698 : Nat := 4983230072969 + 3 ^ 40 * 2808698 * 2
def baseEnd_2808698 : Nat := 1442212087321957189858039

theorem tailTrace_2808698 : CollatzResearch.WordTrace tailWord_2808698 prefixEnd_2808698 1442212087321957189858039 := by
  unfold tailWord_2808698
  simp only [CollatzResearch.WordTrace]
  refine ⟨25610407994643577068410687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68294421319049538849095165 25610407994643577068410687)
  ·
    refine ⟨38415611991965365602616031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25610407994643577068410687 38415611991965365602616031)
    ·
      refine ⟨57623417987948048403924047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38415611991965365602616031 57623417987948048403924047)
      ·
        refine ⟨86435126981922072605886071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57623417987948048403924047 86435126981922072605886071)
        ·
          refine ⟨129652690472883108908829107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86435126981922072605886071 129652690472883108908829107)
          ·
            refine ⟨194479035709324663363243661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129652690472883108908829107 194479035709324663363243661)
            ·
              refine ⟨72929638390996748761216373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194479035709324663363243661 72929638390996748761216373)
              ·
                refine ⟨6837153599155945196364035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72929638390996748761216373 6837153599155945196364035)
                ·
                  refine ⟨10255730398733917794546053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6837153599155945196364035 10255730398733917794546053)
                  ·
                    refine ⟨1922949449762609586477385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10255730398733917794546053 1922949449762609586477385)
                    ·
                      refine ⟨1442212087321957189858039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1922949449762609586477385 1442212087321957189858039)
                      ·
                        rfl

theorem cell23_2808698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2].length) (baseStart_2808698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808698 prefixEnd_2808698 := by exact prefixLift 2808698
  have htrace : WordTrace (prefixWord ++ tailWord_2808698) baseStart_2808698 baseEnd_2808698 := by
    simpa [prefixWord, tailWord_2808698, baseEnd_2808698] using wordTrace_append hprefix tailTrace_2808698
  have hstable : (prefixWord ++ tailWord_2808698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808698).length < 2 ^ (prefixWord ++ tailWord_2808698).sum := by decide
  have hdescent : baseEnd_2808698 < baseStart_2808698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808701 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_2808701 : Nat := 118140960795 + 2808701 * 2 ^ 59
def prefixEnd_2808701 : Nat := 4983230072969 + 3 ^ 40 * 2808701 * 2
def baseEnd_2808701 : Nat := 1442213627763920678120525

theorem tailTrace_2808701 : CollatzResearch.WordTrace tailWord_2808701 prefixEnd_2808701 1442213627763920678120525 := by
  unfold tailWord_2808701
  simp only [CollatzResearch.WordTrace]
  refine ⟨102441741397563439786001957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68294494265042293190667971 102441741397563439786001957)
  ·
    refine ⟨19207826512043144959875367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102441741397563439786001957 19207826512043144959875367)
    ·
      refine ⟨28811739768064717439813051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19207826512043144959875367 28811739768064717439813051)
      ·
        refine ⟨43217609652097076159719577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28811739768064717439813051 43217609652097076159719577)
        ·
          refine ⟨32413207239072807119789683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43217609652097076159719577 32413207239072807119789683)
          ·
            refine ⟨48619810858609210679684525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32413207239072807119789683 48619810858609210679684525)
            ·
              refine ⟨18232429071978454004881697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48619810858609210679684525 18232429071978454004881697)
              ·
                refine ⟨13674321803983840503661273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18232429071978454004881697 13674321803983840503661273)
                ·
                  refine ⟨10255741352987880377745955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13674321803983840503661273 10255741352987880377745955)
                  ·
                    refine ⟨15383612029481820566618933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10255741352987880377745955 15383612029481820566618933)
                    ·
                      refine ⟨1442213627763920678120525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15383612029481820566618933 1442213627763920678120525)
                      ·
                        rfl

theorem cell23_2808701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_2808701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808701 prefixEnd_2808701 := by exact prefixLift 2808701
  have htrace : WordTrace (prefixWord ++ tailWord_2808701) baseStart_2808701 baseEnd_2808701 := by
    simpa [prefixWord, tailWord_2808701, baseEnd_2808701] using wordTrace_append hprefix tailTrace_2808701
  have hstable : (prefixWord ++ tailWord_2808701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808701).length < 2 ^ (prefixWord ++ tailWord_2808701).sum := by decide
  have hdescent : baseEnd_2808701 < baseStart_2808701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808726 : List Nat := [5, 3, 1, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_2808726 : Nat := 118140960795 + 2808726 * 2 ^ 59
def prefixEnd_2808726 : Nat := 4983230072969 + 3 ^ 40 * 2808726 * 2
def baseEnd_2808726 : Nat := 1442226464780283080307911

theorem tailTrace_2808726 : CollatzResearch.WordTrace tailWord_2808726 prefixEnd_2808726 1442226464780283080307911 := by
  unfold tailWord_2808726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6402665826404554315978877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68295102148315246037108021 6402665826404554315978877)
  ·
    refine ⟨2400999684901707868492079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6402665826404554315978877 2400999684901707868492079)
    ·
      refine ⟨3601499527352561802738119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2400999684901707868492079 3601499527352561802738119)
      ·
        refine ⟨5402249291028842704107179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3601499527352561802738119 5402249291028842704107179)
        ·
          refine ⟨8103373936543264056160769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5402249291028842704107179 8103373936543264056160769)
          ·
            refine ⟨6077530452407448042120577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8103373936543264056160769 6077530452407448042120577)
            ·
              refine ⟨4558147839305586031590433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6077530452407448042120577 4558147839305586031590433)
              ·
                refine ⟨3418610879479189523692825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4558147839305586031590433 3418610879479189523692825)
                ·
                  refine ⟨2563958159609392142769619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3418610879479189523692825 2563958159609392142769619)
                  ·
                    refine ⟨3845937239414088214154429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2563958159609392142769619 3845937239414088214154429)
                    ·
                      refine ⟨1442226464780283080307911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3845937239414088214154429 1442226464780283080307911)
                      ·
                        rfl

theorem cell23_2808726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_2808726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808726 prefixEnd_2808726 := by exact prefixLift 2808726
  have htrace : WordTrace (prefixWord ++ tailWord_2808726) baseStart_2808726 baseEnd_2808726 := by
    simpa [prefixWord, tailWord_2808726, baseEnd_2808726] using wordTrace_append hprefix tailTrace_2808726
  have hstable : (prefixWord ++ tailWord_2808726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808726).length < 2 ^ (prefixWord ++ tailWord_2808726).sum := by decide
  have hdescent : baseEnd_2808726 < baseStart_2808726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808749 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_2808749 : Nat := 118140960795 + 2808749 * 2 ^ 59
def prefixEnd_2808749 : Nat := 4983230072969 + 3 ^ 40 * 2808749 * 2
def baseEnd_2808749 : Nat := 1442238274835336490320305

theorem tailTrace_2808749 : CollatzResearch.WordTrace tailWord_2808749 prefixEnd_2808749 1442238274835336490320305 := by
  unfold tailWord_2808749
  simp only [CollatzResearch.WordTrace]
  refine ⟨102443492101389543983749301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68295661400926362655832867 102443492101389543983749301)
  ·
    refine ⟨9604077384505269748476497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102443492101389543983749301 9604077384505269748476497)
    ·
      refine ⟨7203058038378952311357373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9604077384505269748476497 7203058038378952311357373)
      ·
        refine ⟨2701146764392107116759015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7203058038378952311357373 2701146764392107116759015)
        ·
          refine ⟨4051720146588160675138523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2701146764392107116759015 4051720146588160675138523)
          ·
            refine ⟨6077580219882241012707785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051720146588160675138523 6077580219882241012707785)
            ·
              refine ⟨4558185164911680759530839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6077580219882241012707785 4558185164911680759530839)
              ·
                refine ⟨6837277747367521139296259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4558185164911680759530839 6837277747367521139296259)
                ·
                  refine ⟨10255916621051281708944389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6837277747367521139296259 10255916621051281708944389)
                  ·
                    refine ⟨1922984366447115320427073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10255916621051281708944389 1922984366447115320427073)
                    ·
                      refine ⟨1442238274835336490320305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1922984366447115320427073 1442238274835336490320305)
                      ·
                        rfl

theorem cell23_2808749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_2808749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808749 prefixEnd_2808749 := by exact prefixLift 2808749
  have htrace : WordTrace (prefixWord ++ tailWord_2808749) baseStart_2808749 baseEnd_2808749 := by
    simpa [prefixWord, tailWord_2808749, baseEnd_2808749] using wordTrace_append hprefix tailTrace_2808749
  have hstable : (prefixWord ++ tailWord_2808749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808749).length < 2 ^ (prefixWord ++ tailWord_2808749).sum := by decide
  have hdescent : baseEnd_2808749 < baseStart_2808749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808768 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 2, 5]
def baseStart_2808768 : Nat := 118140960795 + 2808768 * 2 ^ 59
def prefixEnd_2808768 : Nat := 4983230072969 + 3 ^ 40 * 2808768 * 2
def baseEnd_2808768 : Nat := 480749343655923971994239

theorem tailTrace_2808768 : CollatzResearch.WordTrace tailWord_2808768 prefixEnd_2808768 480749343655923971994239 := by
  unfold tailWord_2808768
  simp only [CollatzResearch.WordTrace]
  refine ⟨51222092544160355114345479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68296123392213806819127305 51222092544160355114345479)
  ·
    refine ⟨76833138816240532671518219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51222092544160355114345479 76833138816240532671518219)
    ·
      refine ⟨115249708224360799007277329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76833138816240532671518219 115249708224360799007277329)
      ·
        refine ⟨86437281168270599255457997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115249708224360799007277329 86437281168270599255457997)
        ·
          refine ⟨32413980438101474720796749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86437281168270599255457997 32413980438101474720796749)
          ·
            refine ⟨12155242664288053020298781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32413980438101474720796749 12155242664288053020298781)
            ·
              refine ⟨4558215999108019882612043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12155242664288053020298781 4558215999108019882612043)
              ·
                refine ⟨6837323998662029823918065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4558215999108019882612043 6837323998662029823918065)
                ·
                  refine ⟨5127992998996522367938549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6837323998662029823918065 5127992998996522367938549)
                  ·
                    refine ⟨480749343655923971994239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5127992998996522367938549 480749343655923971994239)
                    ·
                      rfl

theorem cell23_2808768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 2, 5].length) (baseStart_2808768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808768 prefixEnd_2808768 := by exact prefixLift 2808768
  have htrace : WordTrace (prefixWord ++ tailWord_2808768) baseStart_2808768 baseEnd_2808768 := by
    simpa [prefixWord, tailWord_2808768, baseEnd_2808768] using wordTrace_append hprefix tailTrace_2808768
  have hstable : (prefixWord ++ tailWord_2808768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808768).length < 2 ^ (prefixWord ++ tailWord_2808768).sum := by decide
  have hdescent : baseEnd_2808768 < baseStart_2808768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808771 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 4]
def baseStart_2808771 : Nat := 118140960795 + 2808771 * 2 ^ 59
def prefixEnd_2808771 : Nat := 4983230072969 + 3 ^ 40 * 2808771 * 2
def baseEnd_2808771 : Nat := 1442249571409735404245203

theorem tailTrace_2808771 : CollatzResearch.WordTrace tailWord_2808771 prefixEnd_2808771 1442249571409735404245203 := by
  unfold tailWord_2808771
  simp only [CollatzResearch.WordTrace]
  refine ⟨102444294507309841741050167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68296196338206561160700111 102444294507309841741050167)
  ·
    refine ⟨153666441760964762611575251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102444294507309841741050167 153666441760964762611575251)
    ·
      refine ⟨230499662641447143917362877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153666441760964762611575251 230499662641447143917362877)
      ·
        refine ⟨86437373490542678969011079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230499662641447143917362877 86437373490542678969011079)
        ·
          refine ⟨129656060235814018453516619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86437373490542678969011079 129656060235814018453516619)
          ·
            refine ⟨194484090353721027680274929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129656060235814018453516619 194484090353721027680274929)
            ·
              refine ⟨145863067765290770760206197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194484090353721027680274929 145863067765290770760206197)
              ·
                refine ⟨13674662602996009758769331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145863067765290770760206197 13674662602996009758769331)
                ·
                  refine ⟨20511993904494014638153997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13674662602996009758769331 20511993904494014638153997)
                  ·
                    refine ⟨7691997714185255489307749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20511993904494014638153997 7691997714185255489307749)
                    ·
                      refine ⟨1442249571409735404245203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7691997714185255489307749 1442249571409735404245203)
                      ·
                        rfl

theorem cell23_2808771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_2808771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808771 prefixEnd_2808771 := by exact prefixLift 2808771
  have htrace : WordTrace (prefixWord ++ tailWord_2808771) baseStart_2808771 baseEnd_2808771 := by
    simpa [prefixWord, tailWord_2808771, baseEnd_2808771] using wordTrace_append hprefix tailTrace_2808771
  have hstable : (prefixWord ++ tailWord_2808771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808771).length < 2 ^ (prefixWord ++ tailWord_2808771).sum := by decide
  have hdescent : baseEnd_2808771 < baseStart_2808771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808801 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_2808801 : Nat := 118140960795 + 2808801 * 2 ^ 59
def prefixEnd_2808801 : Nat := 4983230072969 + 3 ^ 40 * 2808801 * 2
def baseEnd_2808801 : Nat := 1442264975829370286870065

theorem tailTrace_2808801 : CollatzResearch.WordTrace tailWord_2808801 prefixEnd_2808801 1442264975829370286870065 := by
  unfold tailWord_2808801
  simp only [CollatzResearch.WordTrace]
  refine ⟨102445388697201156864642257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68296925798134104576428171 102445388697201156864642257)
  ·
    refine ⟨76834041522900867648481693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102445388697201156864642257 76834041522900867648481693)
    ·
      refine ⟨28812765571087825368180635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76834041522900867648481693 28812765571087825368180635)
      ·
        refine ⟨43219148356631738052270953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28812765571087825368180635 43219148356631738052270953)
        ·
          refine ⟨32414361267473803539203215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43219148356631738052270953 32414361267473803539203215)
          ·
            refine ⟨48621541901210705308804823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32414361267473803539203215 48621541901210705308804823)
            ·
              refine ⟨72932312851816057963207235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48621541901210705308804823 72932312851816057963207235)
              ·
                refine ⟨109398469277724086944810853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72932312851816057963207235 109398469277724086944810853)
                ·
                  refine ⟨20512212989573266302152035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109398469277724086944810853 20512212989573266302152035)
                  ·
                    refine ⟨30768319484359899453228053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20512212989573266302152035 30768319484359899453228053)
                    ·
                      refine ⟨1442264975829370286870065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30768319484359899453228053 1442264975829370286870065)
                      ·
                        rfl

theorem cell23_2808801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_2808801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808801 prefixEnd_2808801 := by exact prefixLift 2808801
  have htrace : WordTrace (prefixWord ++ tailWord_2808801) baseStart_2808801 baseEnd_2808801 := by
    simpa [prefixWord, tailWord_2808801, baseEnd_2808801] using wordTrace_append hprefix tailTrace_2808801
  have hstable : (prefixWord ++ tailWord_2808801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808801).length < 2 ^ (prefixWord ++ tailWord_2808801).sum := by decide
  have hdescent : baseEnd_2808801 < baseStart_2808801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808808 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_2808808 : Nat := 118140960795 + 2808808 * 2 ^ 59
def prefixEnd_2808808 : Nat := 4983230072969 + 3 ^ 40 * 2808808 * 2
def baseEnd_2808808 : Nat := 1442268570193951759482533

theorem tailTrace_2808808 : CollatzResearch.WordTrace tailWord_2808808 prefixEnd_2808808 1442268570193951759482533 := by
  unfold tailWord_2808808
  simp only [CollatzResearch.WordTrace]
  refine ⟨51222822004087898530073539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68297096005450531373431385 51222822004087898530073539)
  ·
    refine ⟨76834233006131847795110309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51222822004087898530073539 76834233006131847795110309)
    ·
      refine ⟨14406418688649721461583183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76834233006131847795110309 14406418688649721461583183)
      ·
        refine ⟨21609628032974582192374775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14406418688649721461583183 21609628032974582192374775)
        ·
          refine ⟨32414442049461873288562163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21609628032974582192374775 32414442049461873288562163)
          ·
            refine ⟨48621663074192809932843245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32414442049461873288562163 48621663074192809932843245)
            ·
              refine ⟨18233123652822303724816217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48621663074192809932843245 18233123652822303724816217)
              ·
                refine ⟨13674842739616727793612163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18233123652822303724816217 13674842739616727793612163)
                ·
                  refine ⟨20512264109425091690418245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13674842739616727793612163 20512264109425091690418245)
                  ·
                    refine ⟨3846049520517204691953421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20512264109425091690418245 3846049520517204691953421)
                    ·
                      refine ⟨1442268570193951759482533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3846049520517204691953421 1442268570193951759482533)
                      ·
                        rfl

theorem cell23_2808808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_2808808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808808 prefixEnd_2808808 := by exact prefixLift 2808808
  have htrace : WordTrace (prefixWord ++ tailWord_2808808) baseStart_2808808 baseEnd_2808808 := by
    simpa [prefixWord, tailWord_2808808, baseEnd_2808808] using wordTrace_append hprefix tailTrace_2808808
  have hstable : (prefixWord ++ tailWord_2808808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808808).length < 2 ^ (prefixWord ++ tailWord_2808808).sum := by decide
  have hdescent : baseEnd_2808808 < baseStart_2808808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808851 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 7]
def baseStart_2808851 : Nat := 118140960795 + 2808851 * 2 ^ 59
def prefixEnd_2808851 : Nat := 4983230072969 + 3 ^ 40 * 2808851 * 2
def baseEnd_2808851 : Nat := 1442290649862095091244835

theorem tailTrace_2808851 : CollatzResearch.WordTrace tailWord_2808851 prefixEnd_2808851 1442290649862095091244835 := by
  unfold tailWord_2808851
  simp only [CollatzResearch.WordTrace]
  refine ⟨102447212347020015403962407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68298141564680010269308271 102447212347020015403962407)
  ·
    refine ⟨153670818520530023105943611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102447212347020015403962407 153670818520530023105943611)
    ·
      refine ⟨230506227780795034658915417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153670818520530023105943611 230506227780795034658915417)
      ·
        refine ⟨172879670835596275994186563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230506227780795034658915417 172879670835596275994186563)
        ·
          refine ⟨259319506253394413991279845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172879670835596275994186563 259319506253394413991279845)
          ·
            refine ⟨48622407422511452623364971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 259319506253394413991279845 48622407422511452623364971)
            ·
              refine ⟨72933611133767178935047457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48622407422511452623364971 72933611133767178935047457)
              ·
                refine ⟨54700208350325384201285593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72933611133767178935047457 54700208350325384201285593)
                ·
                  refine ⟨41025156262744038150964195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54700208350325384201285593 41025156262744038150964195)
                  ·
                    refine ⟨61537734394116057226446293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41025156262744038150964195 61537734394116057226446293)
                    ·
                      refine ⟨1442290649862095091244835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61537734394116057226446293 1442290649862095091244835)
                      ·
                        rfl

theorem cell23_2808851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_2808851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808851 prefixEnd_2808851 := by exact prefixLift 2808851
  have htrace : WordTrace (prefixWord ++ tailWord_2808851) baseStart_2808851 baseEnd_2808851 := by
    simpa [prefixWord, tailWord_2808851, baseEnd_2808851] using wordTrace_append hprefix tailTrace_2808851
  have hstable : (prefixWord ++ tailWord_2808851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808851).length < 2 ^ (prefixWord ++ tailWord_2808851).sum := by decide
  have hdescent : baseEnd_2808851 < baseStart_2808851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808858 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 3, 5]
def baseStart_2808858 : Nat := 118140960795 + 2808858 * 2 ^ 59
def prefixEnd_2808858 : Nat := 4983230072969 + 3 ^ 40 * 2808858 * 2
def baseEnd_2808858 : Nat := 480764748075558854619101

theorem tailTrace_2808858 : CollatzResearch.WordTrace tailWord_2808858 prefixEnd_2808858 480764748075558854619101 := by
  unfold tailWord_2808858
  simp only [CollatzResearch.WordTrace]
  refine ⟨25611866914498663899866807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68298311771996437066311485 25611866914498663899866807)
  ·
    refine ⟨38417800371747995849800211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25611866914498663899866807 38417800371747995849800211)
    ·
      refine ⟨57626700557621993774700317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38417800371747995849800211 57626700557621993774700317)
      ·
        refine ⟨21610012709108247665512619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57626700557621993774700317 21610012709108247665512619)
        ·
          refine ⟨32415019063662371498268929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21610012709108247665512619 32415019063662371498268929)
          ·
            refine ⟨24311264297746778623701697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32415019063662371498268929 24311264297746778623701697)
            ·
              refine ⟨18233448223310083967776273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24311264297746778623701697 18233448223310083967776273)
              ·
                refine ⟨13675086167482562975832205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18233448223310083967776273 13675086167482562975832205)
                ·
                  refine ⟨5128157312805961115937077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13675086167482562975832205 5128157312805961115937077)
                  ·
                    refine ⟨480764748075558854619101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5128157312805961115937077 480764748075558854619101)
                    ·
                      rfl

theorem cell23_2808858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_2808858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808858 prefixEnd_2808858 := by exact prefixLift 2808858
  have htrace : WordTrace (prefixWord ++ tailWord_2808858) baseStart_2808858 baseEnd_2808858 := by
    simpa [prefixWord, tailWord_2808858, baseEnd_2808858] using wordTrace_append hprefix tailTrace_2808858
  have hstable : (prefixWord ++ tailWord_2808858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808858).length < 2 ^ (prefixWord ++ tailWord_2808858).sum := by decide
  have hdescent : baseEnd_2808858 < baseStart_2808858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808882 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2]
def baseStart_2808882 : Nat := 118140960795 + 2808882 * 2 ^ 59
def prefixEnd_2808882 : Nat := 4983230072969 + 3 ^ 40 * 2808882 * 2
def baseEnd_2808882 : Nat := 1442306567762384469957193

theorem tailTrace_2808882 : CollatzResearch.WordTrace tailWord_2808882 prefixEnd_2808882 1442306567762384469957193 := by
  unfold tailWord_2808882
  simp only [CollatzResearch.WordTrace]
  refine ⟨25612085752476926924585225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68298895339938471798893933 25612085752476926924585225)
  ·
    refine ⟨19209064314357695193438919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25612085752476926924585225 19209064314357695193438919)
    ·
      refine ⟨28813596471536542790158379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19209064314357695193438919 28813596471536542790158379)
      ·
        refine ⟨43220394707304814185237569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28813596471536542790158379 43220394707304814185237569)
        ·
          refine ⟨32415296030478610638928177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43220394707304814185237569 32415296030478610638928177)
          ·
            refine ⟨24311472022858957979196133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32415296030478610638928177 24311472022858957979196133)
            ·
              refine ⟨4558401004286054621099275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24311472022858957979196133 4558401004286054621099275)
              ·
                refine ⟨6837601506429081931648913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4558401004286054621099275 6837601506429081931648913)
                ·
                  refine ⟨5128201129821811448736685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6837601506429081931648913 5128201129821811448736685)
                  ·
                    refine ⟨1923075423683179293276257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5128201129821811448736685 1923075423683179293276257)
                    ·
                      refine ⟨1442306567762384469957193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1923075423683179293276257 1442306567762384469957193)
                      ·
                        rfl

theorem cell23_2808882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_2808882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808882 prefixEnd_2808882 := by exact prefixLift 2808882
  have htrace : WordTrace (prefixWord ++ tailWord_2808882) baseStart_2808882 baseEnd_2808882 := by
    simpa [prefixWord, tailWord_2808882, baseEnd_2808882] using wordTrace_append hprefix tailTrace_2808882
  have hstable : (prefixWord ++ tailWord_2808882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808882).length < 2 ^ (prefixWord ++ tailWord_2808882).sum := by decide
  have hdescent : baseEnd_2808882 < baseStart_2808882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808888 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 3, 6]
def baseStart_2808888 : Nat := 118140960795 + 2808888 * 2 ^ 59
def prefixEnd_2808888 : Nat := 4983230072969 + 3 ^ 40 * 2808888 * 2
def baseEnd_2808888 : Nat := 480769882882103815494055

theorem tailTrace_2808888 : CollatzResearch.WordTrace tailWord_2808888 prefixEnd_2808888 480769882882103815494055 := by
  unfold tailWord_2808888
  simp only [CollatzResearch.WordTrace]
  refine ⟨51224280923942985361529659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68299041231923980482039545 51224280923942985361529659)
  ·
    refine ⟨76836421385914478042294489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51224280923942985361529659 76836421385914478042294489)
    ·
      refine ⟨57627316039435858531720867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76836421385914478042294489 57627316039435858531720867)
      ·
        refine ⟨86440974059153787797581301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57627316039435858531720867 86440974059153787797581301)
        ·
          refine ⟨8103841318045667606023247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86440974059153787797581301 8103841318045667606023247)
          ·
            refine ⟨12155761977068501409034871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8103841318045667606023247 12155761977068501409034871)
            ·
              refine ⟨18233642965602752113552307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12155761977068501409034871 18233642965602752113552307)
              ·
                refine ⟨27350464448404128170328461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18233642965602752113552307 27350464448404128170328461)
                ·
                  refine ⟨10256424168151548063873173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27350464448404128170328461 10256424168151548063873173)
                  ·
                    refine ⟨480769882882103815494055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10256424168151548063873173 480769882882103815494055)
                    ·
                      rfl

theorem cell23_2808888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_2808888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808888 prefixEnd_2808888 := by exact prefixLift 2808888
  have htrace : WordTrace (prefixWord ++ tailWord_2808888) baseStart_2808888 baseEnd_2808888 := by
    simpa [prefixWord, tailWord_2808888, baseEnd_2808888] using wordTrace_append hprefix tailTrace_2808888
  have hstable : (prefixWord ++ tailWord_2808888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808888).length < 2 ^ (prefixWord ++ tailWord_2808888).sum := by decide
  have hdescent : baseEnd_2808888 < baseStart_2808888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808892 : List Nat := [2, 2, 2, 2, 2, 3, 3, 1, 1, 5]
def baseStart_2808892 : Nat := 118140960795 + 2808892 * 2 ^ 59
def prefixEnd_2808892 : Nat := 4983230072969 + 3 ^ 40 * 2808892 * 2
def baseEnd_2808892 : Nat := 480770567522976476944049

theorem tailTrace_2808892 : CollatzResearch.WordTrace tailWord_2808892 prefixEnd_2808892 480770567522976476944049 := by
  unfold tailWord_2808892
  simp only [CollatzResearch.WordTrace]
  refine ⟨51224353869935739703102465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68299138493247652937469953 51224353869935739703102465)
  ·
    refine ⟨38418265402451804777326849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51224353869935739703102465 38418265402451804777326849)
    ·
      refine ⟨28813699051838853582995137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38418265402451804777326849 28813699051838853582995137)
      ·
        refine ⟨21610274288879140187246353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28813699051838853582995137 21610274288879140187246353)
        ·
          refine ⟨16207705716659355140434765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21610274288879140187246353 16207705716659355140434765)
          ·
            refine ⟨6077889643747258177663037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16207705716659355140434765 6077889643747258177663037)
            ·
              refine ⟨2279208616405221816623639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6077889643747258177663037 2279208616405221816623639)
              ·
                refine ⟨3418812924607832724935459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279208616405221816623639 3418812924607832724935459)
                ·
                  refine ⟨5128219386911749087403189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3418812924607832724935459 5128219386911749087403189)
                  ·
                    refine ⟨480770567522976476944049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5128219386911749087403189 480770567522976476944049)
                    ·
                      rfl

theorem cell23_2808892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_2808892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808892 prefixEnd_2808892 := by exact prefixLift 2808892
  have htrace : WordTrace (prefixWord ++ tailWord_2808892) baseStart_2808892 baseEnd_2808892 := by
    simpa [prefixWord, tailWord_2808892, baseEnd_2808892] using wordTrace_append hprefix tailTrace_2808892
  have hstable : (prefixWord ++ tailWord_2808892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808892).length < 2 ^ (prefixWord ++ tailWord_2808892).sum := by decide
  have hdescent : baseEnd_2808892 < baseStart_2808892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808908 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 5, 2, 4]
def baseStart_2808908 : Nat := 118140960795 + 2808908 * 2 ^ 59
def prefixEnd_2808908 : Nat := 4983230072969 + 3 ^ 40 * 2808908 * 2
def baseEnd_2808908 : Nat := 1442319918259401368232073

theorem tailTrace_2808908 : CollatzResearch.WordTrace tailWord_2808908 prefixEnd_2808908 1442319918259401368232073 := by
  unfold tailWord_2808908
  simp only [CollatzResearch.WordTrace]
  refine ⟨51224645653906757069393689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68299527538542342759191585 51224645653906757069393689)
  ·
    refine ⟨38418484240430067802045267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51224645653906757069393689 38418484240430067802045267)
    ·
      refine ⟨57627726360645101703067901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38418484240430067802045267 57627726360645101703067901)
      ·
        refine ⟨21610397385241913138650463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57627726360645101703067901 21610397385241913138650463)
        ·
          refine ⟨32415596077862869707975695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21610397385241913138650463 32415596077862869707975695)
          ·
            refine ⟨48623394116794304561963543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32415596077862869707975695 48623394116794304561963543)
            ·
              refine ⟨72935091175191456842945315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48623394116794304561963543 72935091175191456842945315)
              ·
                refine ⟨109402636762787185264417973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72935091175191456842945315 109402636762787185264417973)
                ·
                  refine ⟨10256497196511298618539185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109402636762787185264417973 10256497196511298618539185)
                  ·
                    refine ⟨7692372897383473963904389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10256497196511298618539185 7692372897383473963904389)
                    ·
                      refine ⟨1442319918259401368232073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7692372897383473963904389 1442319918259401368232073)
                      ·
                        rfl

theorem cell23_2808908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_2808908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808908 prefixEnd_2808908 := by exact prefixLift 2808908
  have htrace : WordTrace (prefixWord ++ tailWord_2808908) baseStart_2808908 baseEnd_2808908 := by
    simpa [prefixWord, tailWord_2808908, baseEnd_2808908] using wordTrace_append hprefix tailTrace_2808908
  have hstable : (prefixWord ++ tailWord_2808908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808908).length < 2 ^ (prefixWord ++ tailWord_2808908).sum := by decide
  have hdescent : baseEnd_2808908 < baseStart_2808908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808935 : List Nat := [1, 1, 5, 1, 1, 4, 3, 7]
def baseStart_2808935 : Nat := 118140960795 + 2808935 * 2 ^ 59
def prefixEnd_2808935 : Nat := 4983230072969 + 3 ^ 40 * 2808935 * 2
def baseEnd_2808935 : Nat := 53419769712484176392387

theorem tailTrace_2808935 : CollatzResearch.WordTrace tailWord_2808935 prefixEnd_2808935 53419769712484176392387 := by
  unfold tailWord_2808935
  simp only [CollatzResearch.WordTrace]
  refine ⟨102450276078715697750020259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68300184052477131833346839 102450276078715697750020259)
  ·
    refine ⟨153675414118073546625030389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102450276078715697750020259 153675414118073546625030389)
    ·
      refine ⟨14407070073569394996096599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153675414118073546625030389 14407070073569394996096599)
      ·
        refine ⟨21610605110354092494144899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14407070073569394996096599 21610605110354092494144899)
        ·
          refine ⟨32415907665531138741217349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21610605110354092494144899 32415907665531138741217349)
          ·
            refine ⟨6077982687287088513978253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32415907665531138741217349 6077982687287088513978253)
            ·
              refine ⟨2279243507732658192741845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6077982687287088513978253 2279243507732658192741845)
              ·
                refine ⟨53419769712484176392387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2279243507732658192741845 53419769712484176392387)
                ·
                  rfl

theorem cell23_2808935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 7].length) (baseStart_2808935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808935 prefixEnd_2808935 := by exact prefixLift 2808935
  have htrace : WordTrace (prefixWord ++ tailWord_2808935) baseStart_2808935 baseEnd_2808935 := by
    simpa [prefixWord, tailWord_2808935, baseEnd_2808935] using wordTrace_append hprefix tailTrace_2808935
  have hstable : (prefixWord ++ tailWord_2808935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808935).length < 2 ^ (prefixWord ++ tailWord_2808935).sum := by decide
  have hdescent : baseEnd_2808935 < baseStart_2808935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808946 : List Nat := [3, 2, 1, 2, 2, 1, 4, 3, 1, 2, 2]
def baseStart_2808946 : Nat := 118140960795 + 2808946 * 2 ^ 59
def prefixEnd_2808946 : Nat := 4983230072969 + 3 ^ 40 * 2808946 * 2
def baseEnd_2808946 : Nat := 1442339430524272219556899

theorem tailTrace_2808946 : CollatzResearch.WordTrace tailWord_2808946 prefixEnd_2808946 1442339430524272219556899 := by
  unfold tailWord_2808946
  simp only [CollatzResearch.WordTrace]
  refine ⟨25612669320418961657167673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68300451521117231085780461 25612669320418961657167673)
  ·
    refine ⟨19209501990314221242875755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25612669320418961657167673 19209501990314221242875755)
    ·
      refine ⟨28814252985471331864313633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19209501990314221242875755 28814252985471331864313633)
      ·
        refine ⟨21610689739103498898235225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28814252985471331864313633 21610689739103498898235225)
        ·
          refine ⟨16208017304327624173676419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21610689739103498898235225 16208017304327624173676419)
          ·
            refine ⟨24312025956491436260514629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16208017304327624173676419 24312025956491436260514629)
            ·
              refine ⟨4558504866842144298846493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24312025956491436260514629 4558504866842144298846493)
              ·
                refine ⟨1709439325065804112067435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4558504866842144298846493 1709439325065804112067435)
                ·
                  refine ⟨2564158987598706168101153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1709439325065804112067435 2564158987598706168101153)
                  ·
                    refine ⟨1923119240699029626075865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2564158987598706168101153 1923119240699029626075865)
                    ·
                      refine ⟨1442339430524272219556899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1923119240699029626075865 1442339430524272219556899)
                      ·
                        rfl

theorem cell23_2808946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_2808946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808946 prefixEnd_2808946 := by exact prefixLift 2808946
  have htrace : WordTrace (prefixWord ++ tailWord_2808946) baseStart_2808946 baseEnd_2808946 := by
    simpa [prefixWord, tailWord_2808946, baseEnd_2808946] using wordTrace_append hprefix tailTrace_2808946
  have hstable : (prefixWord ++ tailWord_2808946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808946).length < 2 ^ (prefixWord ++ tailWord_2808946).sum := by decide
  have hdescent : baseEnd_2808946 < baseStart_2808946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2808989 : List Nat := [1, 4, 2, 1, 1, 2, 4, 2, 1, 3, 2]
def baseStart_2808989 : Nat := 118140960795 + 2808989 * 2 ^ 59
def prefixEnd_2808989 : Nat := 4983230072969 + 3 ^ 40 * 2808989 * 2
def baseEnd_2808989 : Nat := 1442361510192415551319201

theorem tailTrace_2808989 : CollatzResearch.WordTrace tailWord_2808989 prefixEnd_2808989 1442361510192415551319201 := by
  unfold tailWord_2808989
  simp only [CollatzResearch.WordTrace]
  refine ⟨102452245620520064972486021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68301497080346709981657347 102452245620520064972486021)
  ·
    refine ⟨19209796053847512182341129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102452245620520064972486021 19209796053847512182341129)
    ·
      refine ⟨14407347040385634136755847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19209796053847512182341129 14407347040385634136755847)
      ·
        refine ⟨21611020560578451205133771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14407347040385634136755847 21611020560578451205133771)
        ·
          refine ⟨32416530840867676807700657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21611020560578451205133771 32416530840867676807700657)
          ·
            refine ⟨24312398130650757605775493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32416530840867676807700657 24312398130650757605775493)
            ·
              refine ⟨4558574649497017051082905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24312398130650757605775493 4558574649497017051082905)
              ·
                refine ⟨3418930987122762788312179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4558574649497017051082905 3418930987122762788312179)
                ·
                  refine ⟨5128396480684144182468269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3418930987122762788312179 5128396480684144182468269)
                  ·
                    refine ⟨1923148680256554068425601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5128396480684144182468269 1923148680256554068425601)
                    ·
                      refine ⟨1442361510192415551319201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1923148680256554068425601 1442361510192415551319201)
                      ·
                        rfl

theorem cell23_2808989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_2808989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2808989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2808989 prefixEnd_2808989 := by exact prefixLift 2808989
  have htrace : WordTrace (prefixWord ++ tailWord_2808989) baseStart_2808989 baseEnd_2808989 := by
    simpa [prefixWord, tailWord_2808989, baseEnd_2808989] using wordTrace_append hprefix tailTrace_2808989
  have hstable : (prefixWord ++ tailWord_2808989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2808989).length < 2 ^ (prefixWord ++ tailWord_2808989).sum := by decide
  have hdescent : baseEnd_2808989 < baseStart_2808989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2808989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809018 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9]
def baseStart_2809018 : Nat := 118140960795 + 2809018 * 2 ^ 59
def prefixEnd_2809018 : Nat := 4983230072969 + 3 ^ 40 * 2809018 * 2
def baseEnd_2809018 : Nat := 1442376401131395937856567

theorem tailTrace_2809018 : CollatzResearch.WordTrace tailWord_2809018 prefixEnd_2809018 1442376401131395937856567 := by
  unfold tailWord_2809018
  simp only [CollatzResearch.WordTrace]
  refine ⟨25613325834353750731322927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68302202224943335283527805 25613325834353750731322927)
  ·
    refine ⟨38419988751530626096984391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25613325834353750731322927 38419988751530626096984391)
    ·
      refine ⟨57629983127295939145476587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38419988751530626096984391 57629983127295939145476587)
      ·
        refine ⟨86444974690943908718214881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57629983127295939145476587 86444974690943908718214881)
        ·
          refine ⟨64833731018207931538661161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86444974690943908718214881 64833731018207931538661161)
          ·
            refine ⟨48625298263655948653995871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64833731018207931538661161 48625298263655948653995871)
            ·
              refine ⟨72937947395483922980993807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48625298263655948653995871 72937947395483922980993807)
              ·
                refine ⟨109406921093225884471490711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72937947395483922980993807 109406921093225884471490711)
                ·
                  refine ⟨164110381639838826707236067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109406921093225884471490711 164110381639838826707236067)
                  ·
                    refine ⟨246165572459758240060854101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 164110381639838826707236067 246165572459758240060854101)
                    ·
                      refine ⟨1442376401131395937856567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 246165572459758240060854101 1442376401131395937856567)
                      ·
                        rfl

theorem cell23_2809018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_2809018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809018 prefixEnd_2809018 := by exact prefixLift 2809018
  have htrace : WordTrace (prefixWord ++ tailWord_2809018) baseStart_2809018 baseEnd_2809018 := by
    simpa [prefixWord, tailWord_2809018, baseEnd_2809018] using wordTrace_append hprefix tailTrace_2809018
  have hstable : (prefixWord ++ tailWord_2809018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809018).length < 2 ^ (prefixWord ++ tailWord_2809018).sum := by decide
  have hdescent : baseEnd_2809018 < baseStart_2809018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
