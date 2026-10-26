import V185TrunkScan23Chunk0644

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3813470 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 8]
def baseStart_3813470 : Nat := 118140960795 + 3813470 * 2 ^ 59
def prefixEnd_3813470 : Nat := 4983230072969 + 3 ^ 40 * 3813470 * 2
def baseEnd_3813470 : Nat := 217571452389033334976353

theorem tailTrace_3813470 : CollatzResearch.WordTrace tailWord_3813470 prefixEnd_3813470 217571452389033334976353 := by
  unfold tailWord_3813470
  simp only [CollatzResearch.WordTrace]
  refine ⟨17386084686807119208669733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92725784996304635779571909 17386084686807119208669733)
  ·
    refine ⟨3259890878776334851625575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17386084686807119208669733 3259890878776334851625575)
    ·
      refine ⟨4889836318164502277438363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3259890878776334851625575 4889836318164502277438363)
      ·
        refine ⟨7334754477246753416157545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4889836318164502277438363 7334754477246753416157545)
        ·
          refine ⟨5501065857935065062118159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7334754477246753416157545 5501065857935065062118159)
          ·
            refine ⟨8251598786902597593177239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5501065857935065062118159 8251598786902597593177239)
            ·
              refine ⟨12377398180353896389765859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8251598786902597593177239 12377398180353896389765859)
              ·
                refine ⟨18566097270530844584648789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12377398180353896389765859 18566097270530844584648789)
                ·
                  refine ⟨217571452389033334976353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18566097270530844584648789 217571452389033334976353)
                  ·
                    rfl

theorem cell23_3813470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_3813470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813470 prefixEnd_3813470 := by exact prefixLift 3813470
  have htrace : WordTrace (prefixWord ++ tailWord_3813470) baseStart_3813470 baseEnd_3813470 := by
    simpa [prefixWord, tailWord_3813470, baseEnd_3813470] using wordTrace_append hprefix tailTrace_3813470
  have hstable : (prefixWord ++ tailWord_3813470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813470).length < 2 ^ (prefixWord ++ tailWord_3813470).sum := by decide
  have hdescent : baseEnd_3813470 < baseStart_3813470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813537 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 3, 2, 2]
def baseStart_3813537 : Nat := 118140960795 + 3813537 * 2 ^ 59
def prefixEnd_3813537 : Nat := 4983230072969 + 3 ^ 40 * 3813537 * 2
def baseEnd_3813537 : Nat := 1958177474705151252649369

theorem tailTrace_3813537 : CollatzResearch.WordTrace tailWord_3813537 prefixEnd_3813537 1958177474705151252649369 := by
  unfold tailWord_3813537
  simp only [CollatzResearch.WordTrace]
  refine ⟨139091121185214224112046865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92727414123476149408031243 139091121185214224112046865)
  ·
    refine ⟨104318340888910668084035149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139091121185214224112046865 104318340888910668084035149)
    ·
      refine ⟨39119377833341500531513181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104318340888910668084035149 39119377833341500531513181)
      ·
        refine ⟨14669766687503062699317443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39119377833341500531513181 14669766687503062699317443)
        ·
          refine ⟨22004650031254594048976165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14669766687503062699317443 22004650031254594048976165)
          ·
            refine ⟨4125871880860236384183031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22004650031254594048976165 4125871880860236384183031)
            ·
              refine ⟨6188807821290354576274547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4125871880860236384183031 6188807821290354576274547)
              ·
                refine ⟨9283211731935531864411821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6188807821290354576274547 9283211731935531864411821)
                ·
                  refine ⟨3481204399475824449154433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9283211731935531864411821 3481204399475824449154433)
                  ·
                    refine ⟨2610903299606868336865825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3481204399475824449154433 2610903299606868336865825)
                    ·
                      refine ⟨1958177474705151252649369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610903299606868336865825 1958177474705151252649369)
                      ·
                        rfl

theorem cell23_3813537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_3813537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813537 prefixEnd_3813537 := by exact prefixLift 3813537
  have htrace : WordTrace (prefixWord ++ tailWord_3813537) baseStart_3813537 baseEnd_3813537 := by
    simpa [prefixWord, tailWord_3813537, baseEnd_3813537] using wordTrace_append hprefix tailTrace_3813537
  have hstable : (prefixWord ++ tailWord_3813537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813537).length < 2 ^ (prefixWord ++ tailWord_3813537).sum := by decide
  have hdescent : baseEnd_3813537 < baseStart_3813537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813543 : List Nat := [1, 1, 6, 2, 2, 1, 2, 8]
def baseStart_3813543 : Nat := 118140960795 + 3813543 * 2 ^ 59
def prefixEnd_3813543 : Nat := 4983230072969 + 3 ^ 40 * 3813543 * 2
def baseEnd_3813543 : Nat := 72525205762558452932383

theorem tailTrace_3813543 : CollatzResearch.WordTrace tailWord_3813543 prefixEnd_3813543 72525205762558452932383 := by
  unfold tailWord_3813543
  simp only [CollatzResearch.WordTrace]
  refine ⟨139091340023192487136765283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92727560015461658091176855 139091340023192487136765283)
  ·
    refine ⟨208637010034788730705147925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139091340023192487136765283 208637010034788730705147925)
    ·
      refine ⟨9779859845380721751803809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 208637010034788730705147925 9779859845380721751803809)
      ·
        refine ⟨7334894884035541313852857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9779859845380721751803809 7334894884035541313852857)
        ·
          refine ⟨5501171163026655985389643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7334894884035541313852857 5501171163026655985389643)
          ·
            refine ⟨8251756744539983978084465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5501171163026655985389643 8251756744539983978084465)
            ·
              refine ⟨6188817558404987983563349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8251756744539983978084465 6188817558404987983563349)
              ·
                refine ⟨72525205762558452932383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6188817558404987983563349 72525205762558452932383)
                ·
                  rfl

theorem cell23_3813543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 8].length) (baseStart_3813543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813543 prefixEnd_3813543 := by exact prefixLift 3813543
  have htrace : WordTrace (prefixWord ++ tailWord_3813543) baseStart_3813543 baseEnd_3813543 := by
    simpa [prefixWord, tailWord_3813543, baseEnd_3813543] using wordTrace_append hprefix tailTrace_3813543
  have hstable : (prefixWord ++ tailWord_3813543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813543).length < 2 ^ (prefixWord ++ tailWord_3813543).sum := by decide
  have hdescent : baseEnd_3813543 < baseStart_3813543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813563 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 3, 3, 2]
def baseStart_3813563 : Nat := 118140960795 + 3813563 * 2 ^ 59
def prefixEnd_3813563 : Nat := 4983230072969 + 3 ^ 40 * 3813563 * 2
def baseEnd_3813563 : Nat := 1958190825202168150924249

theorem tailTrace_3813563 : CollatzResearch.WordTrace tailWord_3813563 prefixEnd_3813563 1958190825202168150924249 := by
  unfold tailWord_3813563
  simp only [CollatzResearch.WordTrace]
  refine ⟨139092069483120030552493343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92728046322080020368328895 139092069483120030552493343)
  ·
    refine ⟨208638104224680045828740015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139092069483120030552493343 208638104224680045828740015)
    ·
      refine ⟨312957156337020068743110023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208638104224680045828740015 312957156337020068743110023)
      ·
        refine ⟨469435734505530103114665035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312957156337020068743110023 469435734505530103114665035)
        ·
          refine ⟨704153601758295154671997553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469435734505530103114665035 704153601758295154671997553)
          ·
            refine ⟨528115201318721366003998165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704153601758295154671997553 528115201318721366003998165)
            ·
              refine ⟨12377700030907532015718707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 528115201318721366003998165 12377700030907532015718707)
              ·
                refine ⟨18566550046361298023578061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12377700030907532015718707 18566550046361298023578061)
                ·
                  refine ⟨6962456267385486758841773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18566550046361298023578061 6962456267385486758841773)
                  ·
                    refine ⟨2610921100269557534565665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6962456267385486758841773 2610921100269557534565665)
                    ·
                      refine ⟨1958190825202168150924249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610921100269557534565665 1958190825202168150924249)
                      ·
                        rfl

theorem cell23_3813563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 3, 2].length) (baseStart_3813563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813563 prefixEnd_3813563 := by exact prefixLift 3813563
  have htrace : WordTrace (prefixWord ++ tailWord_3813563) baseStart_3813563 baseEnd_3813563 := by
    simpa [prefixWord, tailWord_3813563, baseEnd_3813563] using wordTrace_append hprefix tailTrace_3813563
  have hstable : (prefixWord ++ tailWord_3813563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813563).length < 2 ^ (prefixWord ++ tailWord_3813563).sum := by decide
  have hdescent : baseEnd_3813563 < baseStart_3813563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813610 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 1, 4, 2]
def baseStart_3813610 : Nat := 118140960795 + 3813610 * 2 ^ 59
def prefixEnd_3813610 : Nat := 4983230072969 + 3 ^ 40 * 3813610 * 2
def baseEnd_3813610 : Nat := 1958214958792929467036533

theorem tailTrace_3813610 : CollatzResearch.WordTrace tailWord_3813610 prefixEnd_3813610 1958214958792929467036533 := by
  unfold tailWord_3813610
  simp only [CollatzResearch.WordTrace]
  refine ⟨34773445928487439394863571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92729189142633171719636189 34773445928487439394863571)
  ·
    refine ⟨52160168892731159092295357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34773445928487439394863571 52160168892731159092295357)
    ·
      refine ⟨19560063334774184659610759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52160168892731159092295357 19560063334774184659610759)
      ·
        refine ⟨29340095002161276989416139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19560063334774184659610759 29340095002161276989416139)
        ·
          refine ⟨44010142503241915484124209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29340095002161276989416139 44010142503241915484124209)
          ·
            refine ⟨33007606877431436613093157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44010142503241915484124209 33007606877431436613093157)
            ·
              refine ⟨6188926289518394364954967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33007606877431436613093157 6188926289518394364954967)
              ·
                refine ⟨9283389434277591547432451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6188926289518394364954967 9283389434277591547432451)
                ·
                  refine ⟨13925084151416387321148677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9283389434277591547432451 13925084151416387321148677)
                  ·
                    refine ⟨2610953278390572622715377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13925084151416387321148677 2610953278390572622715377)
                    ·
                      refine ⟨1958214958792929467036533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610953278390572622715377 1958214958792929467036533)
                      ·
                        rfl

theorem cell23_3813610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_3813610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813610 prefixEnd_3813610 := by exact prefixLift 3813610
  have htrace : WordTrace (prefixWord ++ tailWord_3813610) baseStart_3813610 baseEnd_3813610 := by
    simpa [prefixWord, tailWord_3813610, baseEnd_3813610] using wordTrace_append hprefix tailTrace_3813610
  have hstable : (prefixWord ++ tailWord_3813610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813610).length < 2 ^ (prefixWord ++ tailWord_3813610).sum := by decide
  have hdescent : baseEnd_3813610 < baseStart_3813610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813653 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 1, 7, 2]
def baseStart_3813653 : Nat := 118140960795 + 3813653 * 2 ^ 59
def prefixEnd_3813653 : Nat := 4983230072969 + 3 ^ 40 * 3813653 * 2
def baseEnd_3813653 : Nat := 1958237038461072798798835

theorem tailTrace_3813653 : CollatzResearch.WordTrace tailWord_3813653 prefixEnd_3813653 1958237038461072798798835 := by
  unfold tailWord_3813653
  simp only [CollatzResearch.WordTrace]
  refine ⟨139095352052793975923269613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92730234701862650615513075 139095352052793975923269613)
  ·
    refine ⟨52160757019797740971226105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139095352052793975923269613 52160757019797740971226105)
    ·
      refine ⟨39120567764848305728419579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52160757019797740971226105 39120567764848305728419579)
      ·
        refine ⟨58680851647272458592629369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39120567764848305728419579 58680851647272458592629369)
        ·
          refine ⟨44010638735454343944472027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58680851647272458592629369 44010638735454343944472027)
          ·
            refine ⟨66015958103181515916708041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44010638735454343944472027 66015958103181515916708041)
            ·
              refine ⟨49511968577386136937531031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66015958103181515916708041 49511968577386136937531031)
              ·
                refine ⟨74267952866079205406296547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49511968577386136937531031 74267952866079205406296547)
                ·
                  refine ⟨111401929299118808109444821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74267952866079205406296547 111401929299118808109444821)
                  ·
                    refine ⟨2610982717948097065065113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 111401929299118808109444821 2610982717948097065065113)
                    ·
                      refine ⟨1958237038461072798798835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610982717948097065065113 1958237038461072798798835)
                      ·
                        rfl

theorem cell23_3813653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_3813653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813653 prefixEnd_3813653 := by exact prefixLift 3813653
  have htrace : WordTrace (prefixWord ++ tailWord_3813653) baseStart_3813653 baseEnd_3813653 := by
    simpa [prefixWord, tailWord_3813653, baseEnd_3813653] using wordTrace_append hprefix tailTrace_3813653
  have hstable : (prefixWord ++ tailWord_3813653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813653).length < 2 ^ (prefixWord ++ tailWord_3813653).sum := by decide
  have hdescent : baseEnd_3813653 < baseStart_3813653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813656 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 1, 1, 7]
def baseStart_3813656 : Nat := 118140960795 + 3813656 * 2 ^ 59
def prefixEnd_3813656 : Nat := 4983230072969 + 3 ^ 40 * 3813656 * 2
def baseEnd_3813656 : Nat := 1958238578903036287061321

theorem tailTrace_3813656 : CollatzResearch.WordTrace tailWord_3813656 prefixEnd_3813656 1958238578903036287061321 := by
  unfold tailWord_3813656
  simp only [CollatzResearch.WordTrace]
  refine ⟨69547730735891553717814411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92730307647855404957085881 69547730735891553717814411)
  ·
    refine ⟨104321596103837330576721617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69547730735891553717814411 104321596103837330576721617)
    ·
      refine ⟨78241197077877997932541213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104321596103837330576721617 78241197077877997932541213)
      ·
        refine ⟨29340448904204249224702955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78241197077877997932541213 29340448904204249224702955)
        ·
          refine ⟨44010673356306373837054433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29340448904204249224702955 44010673356306373837054433)
          ·
            refine ⟨33008005017229780377790825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44010673356306373837054433 33008005017229780377790825)
            ·
              refine ⟨24756003762922335283343119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33008005017229780377790825 24756003762922335283343119)
              ·
                refine ⟨37134005644383502925014679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24756003762922335283343119 37134005644383502925014679)
                ·
                  refine ⟨55701008466575254387522019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37134005644383502925014679 55701008466575254387522019)
                  ·
                    refine ⟨83551512699862881581283029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55701008466575254387522019 83551512699862881581283029)
                    ·
                      refine ⟨1958238578903036287061321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83551512699862881581283029 1958238578903036287061321)
                      ·
                        rfl

theorem cell23_3813656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_3813656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813656 prefixEnd_3813656 := by exact prefixLift 3813656
  have htrace : WordTrace (prefixWord ++ tailWord_3813656) baseStart_3813656 baseEnd_3813656 := by
    simpa [prefixWord, tailWord_3813656, baseEnd_3813656] using wordTrace_append hprefix tailTrace_3813656
  have hstable : (prefixWord ++ tailWord_3813656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813656).length < 2 ^ (prefixWord ++ tailWord_3813656).sum := by decide
  have hdescent : baseEnd_3813656 < baseStart_3813656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813661 : List Nat := [1, 4, 2, 3, 2, 1, 3, 1, 2, 2, 2]
def baseStart_3813661 : Nat := 118140960795 + 3813661 * 2 ^ 59
def prefixEnd_3813661 : Nat := 4983230072969 + 3 ^ 40 * 3813661 * 2
def baseEnd_3813661 : Nat := 1958241146306308767498799

theorem tailTrace_3813661 : CollatzResearch.WordTrace tailWord_3813661 prefixEnd_3813661 1958241146306308767498799 := by
  unfold tailWord_3813661
  simp only [CollatzResearch.WordTrace]
  refine ⟨139095643836764993289560837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92730429224509995526373891 139095643836764993289560837)
  ·
    refine ⟨26080433219393436241792657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139095643836764993289560837 26080433219393436241792657)
    ·
      refine ⟨19560324914545077181344493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26080433219393436241792657 19560324914545077181344493)
      ·
        refine ⟨7335121842954403943004185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19560324914545077181344493 7335121842954403943004185)
        ·
          refine ⟨5501341382215802957253139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7335121842954403943004185 5501341382215802957253139)
          ·
            refine ⟨8252012073323704435879709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5501341382215802957253139 8252012073323704435879709)
            ·
              refine ⟨3094504527496389163454891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8252012073323704435879709 3094504527496389163454891)
              ·
                refine ⟨4641756791244583745182337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3094504527496389163454891 4641756791244583745182337)
                ·
                  refine ⟨3481317593433437808886753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4641756791244583745182337 3481317593433437808886753)
                  ·
                    refine ⟨2610988195075078356665065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3481317593433437808886753 2610988195075078356665065)
                    ·
                      refine ⟨1958241146306308767498799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610988195075078356665065 1958241146306308767498799)
                      ·
                        rfl

theorem cell23_3813661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_3813661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813661 prefixEnd_3813661 := by exact prefixLift 3813661
  have htrace : WordTrace (prefixWord ++ tailWord_3813661) baseStart_3813661 baseEnd_3813661 := by
    simpa [prefixWord, tailWord_3813661, baseEnd_3813661] using wordTrace_append hprefix tailTrace_3813661
  have hstable : (prefixWord ++ tailWord_3813661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813661).length < 2 ^ (prefixWord ++ tailWord_3813661).sum := by decide
  have hdescent : baseEnd_3813661 < baseStart_3813661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813683 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 4]
def baseStart_3813683 : Nat := 118140960795 + 3813683 * 2 ^ 59
def prefixEnd_3813683 : Nat := 4983230072969 + 3 ^ 40 * 3813683 * 2
def baseEnd_3813683 : Nat := 1958252442880707681423697

theorem tailTrace_3813683 : CollatzResearch.WordTrace tailWord_3813683 prefixEnd_3813683 1958252442880707681423697 := by
  unfold tailWord_3813683
  simp only [CollatzResearch.WordTrace]
  refine ⟨139096446242685291046861703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92730964161790194031241135 139096446242685291046861703)
  ·
    refine ⟨208644669364027936570292555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139096446242685291046861703 208644669364027936570292555)
    ·
      refine ⟨312967004046041904855438833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208644669364027936570292555 312967004046041904855438833)
      ·
        refine ⟨234725253034531428641579125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312967004046041904855438833 234725253034531428641579125)
        ·
          refine ⟨22005492471987321435148043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234725253034531428641579125 22005492471987321435148043)
          ·
            refine ⟨33008238707980982152722065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22005492471987321435148043 33008238707980982152722065)
            ·
              refine ⟨24756179030985736614541549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33008238707980982152722065 24756179030985736614541549)
              ·
                refine ⟨9283567136619651230453081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24756179030985736614541549 9283567136619651230453081)
                ·
                  refine ⟨6962675352464738422839811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9283567136619651230453081 6962675352464738422839811)
                  ·
                    refine ⟨10444013028697107634259717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6962675352464738422839811 10444013028697107634259717)
                    ·
                      refine ⟨1958252442880707681423697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10444013028697107634259717 1958252442880707681423697)
                      ·
                        rfl

theorem cell23_3813683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 4].length) (baseStart_3813683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813683 prefixEnd_3813683 := by exact prefixLift 3813683
  have htrace : WordTrace (prefixWord ++ tailWord_3813683) baseStart_3813683 baseEnd_3813683 := by
    simpa [prefixWord, tailWord_3813683, baseEnd_3813683] using wordTrace_append hprefix tailTrace_3813683
  have hstable : (prefixWord ++ tailWord_3813683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813683).length < 2 ^ (prefixWord ++ tailWord_3813683).sum := by decide
  have hdescent : baseEnd_3813683 < baseStart_3813683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813696 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 6]
def baseStart_3813696 : Nat := 118140960795 + 3813696 * 2 ^ 59
def prefixEnd_3813696 : Nat := 4983230072969 + 3 ^ 40 * 3813696 * 2
def baseEnd_3813696 : Nat := 1958259118129216130561137

theorem tailTrace_3813696 : CollatzResearch.WordTrace tailWord_3813696 prefixEnd_3813696 1958259118129216130561137 := by
  unfold tailWord_3813696
  simp only [CollatzResearch.WordTrace]
  refine ⟨69548460195819097133542471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92731280261092129511389961 69548460195819097133542471)
  ·
    refine ⟨104322690293728645700313707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69548460195819097133542471 104322690293728645700313707)
    ·
      refine ⟨156484035440592968550470561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104322690293728645700313707 156484035440592968550470561)
      ·
        refine ⟨117363026580444726412852921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156484035440592968550470561 117363026580444726412852921)
        ·
          refine ⟨88022269935333544809639691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117363026580444726412852921 88022269935333544809639691)
          ·
            refine ⟨132033404903000317214459537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88022269935333544809639691 132033404903000317214459537)
            ·
              refine ⟨99025053677250237910844653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132033404903000317214459537 99025053677250237910844653)
              ·
                refine ⟨37134395128968839216566745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99025053677250237910844653 37134395128968839216566745)
                ·
                  refine ⟨27850796346726629412425059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37134395128968839216566745 27850796346726629412425059)
                  ·
                    refine ⟨41776194520089944118637589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27850796346726629412425059 41776194520089944118637589)
                    ·
                      refine ⟨1958259118129216130561137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41776194520089944118637589 1958259118129216130561137)
                      ·
                        rfl

theorem cell23_3813696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_3813696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813696 prefixEnd_3813696 := by exact prefixLift 3813696
  have htrace : WordTrace (prefixWord ++ tailWord_3813696) baseStart_3813696 baseEnd_3813696 := by
    simpa [prefixWord, tailWord_3813696, baseEnd_3813696] using wordTrace_append hprefix tailTrace_3813696
  have hstable : (prefixWord ++ tailWord_3813696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813696).length < 2 ^ (prefixWord ++ tailWord_3813696).sum := by decide
  have hdescent : baseEnd_3813696 < baseStart_3813696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813761 : List Nat := [1, 2, 4, 3, 1, 3, 2, 2, 1, 4]
def baseStart_3813761 : Nat := 118140960795 + 3813761 * 2 ^ 59
def prefixEnd_3813761 : Nat := 4983230072969 + 3 ^ 40 * 3813761 * 2
def baseEnd_3813761 : Nat := 652764164790586125416113

theorem tailTrace_3813761 : CollatzResearch.WordTrace tailWord_3813761 prefixEnd_3813761 652764164790586125416113 := by
  unfold tailWord_3813761
  simp only [CollatzResearch.WordTrace]
  refine ⟨139099291136402710368201137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92732860757601806912134091 139099291136402710368201137)
  ·
    refine ⟨104324468352302032776150853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139099291136402710368201137 104324468352302032776150853)
    ·
      refine ⟨19560837816056631145528285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104324468352302032776150853 19560837816056631145528285)
      ·
        refine ⟨7335314181021236679573107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19560837816056631145528285 7335314181021236679573107)
        ·
          refine ⟨11002971271531855019359661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7335314181021236679573107 11002971271531855019359661)
          ·
            refine ⟨4126114226824445632259873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11002971271531855019359661 4126114226824445632259873)
            ·
              refine ⟨3094585670118334224194905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4126114226824445632259873 3094585670118334224194905)
              ·
                refine ⟨2320939252588750668146179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3094585670118334224194905 2320939252588750668146179)
                ·
                  refine ⟨3481408878883126002219269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2320939252588750668146179 3481408878883126002219269)
                  ·
                    refine ⟨652764164790586125416113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3481408878883126002219269 652764164790586125416113)
                    ·
                      rfl

theorem cell23_3813761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_3813761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813761 prefixEnd_3813761 := by exact prefixLift 3813761
  have htrace : WordTrace (prefixWord ++ tailWord_3813761) baseStart_3813761 baseEnd_3813761 := by
    simpa [prefixWord, tailWord_3813761, baseEnd_3813761] using wordTrace_append hprefix tailTrace_3813761
  have hstable : (prefixWord ++ tailWord_3813761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813761).length < 2 ^ (prefixWord ++ tailWord_3813761).sum := by decide
  have hdescent : baseEnd_3813761 < baseStart_3813761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813783 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 1, 6]
def baseStart_3813783 : Nat := 118140960795 + 3813783 * 2 ^ 59
def prefixEnd_3813783 : Nat := 4983230072969 + 3 ^ 40 * 3813783 * 2
def baseEnd_3813783 : Nat := 652767930315385763391079

theorem tailTrace_3813783 : CollatzResearch.WordTrace tailWord_3813783 prefixEnd_3813783 652767930315385763391079 := by
  unfold tailWord_3813783
  simp only [CollatzResearch.WordTrace]
  refine ⟨139100093542323008125502003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92733395694882005417001335 139100093542323008125502003)
  ·
    refine ⟨208650140313484512188253005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139100093542323008125502003 208650140313484512188253005)
    ·
      refine ⟨78243802617556692070594877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208650140313484512188253005 78243802617556692070594877)
      ·
        refine ⟨29341425981583759526473079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78243802617556692070594877 29341425981583759526473079)
        ·
          refine ⟨44012138972375639289709619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29341425981583759526473079 44012138972375639289709619)
          ·
            refine ⟨66018208458563458934564429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44012138972375639289709619 66018208458563458934564429)
            ·
              refine ⟨24756828171961297100461661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66018208458563458934564429 24756828171961297100461661)
              ·
                refine ⟨9283810564485486412673123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24756828171961297100461661 9283810564485486412673123)
                ·
                  refine ⟨13925715846728229619009685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9283810564485486412673123 13925715846728229619009685)
                  ·
                    refine ⟨652767930315385763391079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13925715846728229619009685 652767930315385763391079)
                    ·
                      rfl

theorem cell23_3813783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_3813783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813783 prefixEnd_3813783 := by exact prefixLift 3813783
  have htrace : WordTrace (prefixWord ++ tailWord_3813783) baseStart_3813783 baseEnd_3813783 := by
    simpa [prefixWord, tailWord_3813783, baseEnd_3813783] using wordTrace_append hprefix tailTrace_3813783
  have hstable : (prefixWord ++ tailWord_3813783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813783).length < 2 ^ (prefixWord ++ tailWord_3813783).sum := by decide
  have hdescent : baseEnd_3813783 < baseStart_3813783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813817 : List Nat := [1, 2, 1, 4, 3, 1, 3, 2, 2, 4]
def baseStart_3813817 : Nat := 118140960795 + 3813817 * 2 ^ 59
def prefixEnd_3813817 : Nat := 4983230072969 + 3 ^ 40 * 3813817 * 2
def baseEnd_3813817 : Nat := 652773749762803385716027

theorem tailTrace_3813817 : CollatzResearch.WordTrace tailWord_3813817 prefixEnd_3813817 652773749762803385716027 := by
  unfold tailWord_3813817
  simp only [CollatzResearch.WordTrace]
  refine ⟨139101333624199831932239705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92734222416133221288159803 139101333624199831932239705)
  ·
    refine ⟨104326000218149873949179779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139101333624199831932239705 104326000218149873949179779)
    ·
      refine ⟨156489000327224810923769669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104326000218149873949179779 156489000327224810923769669)
      ·
        refine ⟨29341687561354652048206813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156489000327224810923769669 29341687561354652048206813)
        ·
          refine ⟨11003132835507994518077555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29341687561354652048206813 11003132835507994518077555)
          ·
            refine ⟨16504699253261991777116333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11003132835507994518077555 16504699253261991777116333)
            ·
              refine ⟨6189262219973246916418625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16504699253261991777116333 6189262219973246916418625)
              ·
                refine ⟨4641946664979935187313969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6189262219973246916418625 4641946664979935187313969)
                ·
                  refine ⟨3481459998734951390485477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4641946664979935187313969 3481459998734951390485477)
                  ·
                    refine ⟨652773749762803385716027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3481459998734951390485477 652773749762803385716027)
                    ·
                      rfl

theorem cell23_3813817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 4].length) (baseStart_3813817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813817 prefixEnd_3813817 := by exact prefixLift 3813817
  have htrace : WordTrace (prefixWord ++ tailWord_3813817) baseStart_3813817 baseEnd_3813817 := by
    simpa [prefixWord, tailWord_3813817, baseEnd_3813817] using wordTrace_append hprefix tailTrace_3813817
  have hstable : (prefixWord ++ tailWord_3813817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813817).length < 2 ^ (prefixWord ++ tailWord_3813817).sum := by decide
  have hdescent : baseEnd_3813817 < baseStart_3813817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813823 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 3]
def baseStart_3813823 : Nat := 118140960795 + 3813823 * 2 ^ 59
def prefixEnd_3813823 : Nat := 4983230072969 + 3 ^ 40 * 3813823 * 2
def baseEnd_3813823 : Nat := 1958324330172337133673053

theorem tailTrace_3813823 : CollatzResearch.WordTrace tailWord_3813823 prefixEnd_3813823 1958324330172337133673053 := by
  unfold tailWord_3813823
  simp only [CollatzResearch.WordTrace]
  refine ⟨139101552462178094956958123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92734368308118729971305415 139101552462178094956958123)
  ·
    refine ⟨208652328693267142435437185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139101552462178094956958123 208652328693267142435437185)
    ·
      refine ⟨156489246519950356826577889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208652328693267142435437185 156489246519950356826577889)
      ·
        refine ⟨117366934889962767619933417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156489246519950356826577889 117366934889962767619933417)
        ·
          refine ⟨88025201167472075714950063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117366934889962767619933417 88025201167472075714950063)
          ·
            refine ⟨132037801751208113572425095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88025201167472075714950063 132037801751208113572425095)
            ·
              refine ⟨198056702626812170358637643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132037801751208113572425095 198056702626812170358637643)
              ·
                refine ⟨297085053940218255537956465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198056702626812170358637643 297085053940218255537956465)
                ·
                  refine ⟨222813790455163691653467349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297085053940218255537956465 222813790455163691653467349)
                  ·
                    refine ⟨5222198213792899023128141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 222813790455163691653467349 5222198213792899023128141)
                    ·
                      refine ⟨1958324330172337133673053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5222198213792899023128141 1958324330172337133673053)
                      ·
                        rfl

theorem cell23_3813823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_3813823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813823 prefixEnd_3813823 := by exact prefixLift 3813823
  have htrace : WordTrace (prefixWord ++ tailWord_3813823) baseStart_3813823 baseEnd_3813823 := by
    simpa [prefixWord, tailWord_3813823, baseEnd_3813823] using wordTrace_append hprefix tailTrace_3813823
  have hstable : (prefixWord ++ tailWord_3813823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813823).length < 2 ^ (prefixWord ++ tailWord_3813823).sum := by decide
  have hdescent : baseEnd_3813823 < baseStart_3813823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813840 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 8, 1, 3]
def baseStart_3813840 : Nat := 118140960795 + 3813840 * 2 ^ 59
def prefixEnd_3813840 : Nat := 4983230072969 + 3 ^ 40 * 3813840 * 2
def baseEnd_3813840 : Nat := 1958333059343463567160475

theorem tailTrace_3813840 : CollatzResearch.WordTrace tailWord_3813840 prefixEnd_3813840 1958333059343463567160475 := by
  unfold tailWord_3813840
  simp only [CollatzResearch.WordTrace]
  refine ⟨69551086251558253430163487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92734781668744337906884649 69551086251558253430163487)
  ·
    refine ⟨104326629377337380145245231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69551086251558253430163487 104326629377337380145245231)
    ·
      refine ⟨156489944066006070217867847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104326629377337380145245231 156489944066006070217867847)
      ·
        refine ⟨234734916099009105326801771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156489944066006070217867847 234734916099009105326801771)
        ·
          refine ⟨352102374148513657990202657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234734916099009105326801771 352102374148513657990202657)
          ·
            refine ⟨264076780611385243492651993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352102374148513657990202657 264076780611385243492651993)
            ·
              refine ⟨198057585458538932619488995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264076780611385243492651993 198057585458538932619488995)
              ·
                refine ⟨297086378187808398929233493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198057585458538932619488995 297086378187808398929233493)
                ·
                  refine ⟨3481480994388379674951955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 297086378187808398929233493 3481480994388379674951955)
                  ·
                    refine ⟨5222221491582569512427933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3481480994388379674951955 5222221491582569512427933)
                    ·
                      refine ⟨1958333059343463567160475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5222221491582569512427933 1958333059343463567160475)
                      ·
                        rfl

theorem cell23_3813840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 8, 1, 3].length) (baseStart_3813840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813840 prefixEnd_3813840 := by exact prefixLift 3813840
  have htrace : WordTrace (prefixWord ++ tailWord_3813840) baseStart_3813840 baseEnd_3813840 := by
    simpa [prefixWord, tailWord_3813840, baseEnd_3813840] using wordTrace_append hprefix tailTrace_3813840
  have hstable : (prefixWord ++ tailWord_3813840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813840).length < 2 ^ (prefixWord ++ tailWord_3813840).sum := by decide
  have hdescent : baseEnd_3813840 < baseStart_3813840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813844 : List Nat := [2, 4, 1, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_3813844 : Nat := 118140960795 + 3813844 * 2 ^ 59
def prefixEnd_3813844 : Nat := 4983230072969 + 3 ^ 40 * 3813844 * 2
def baseEnd_3813844 : Nat := 1958335113266081551510457

theorem tailTrace_3813844 : CollatzResearch.WordTrace tailWord_3813844 prefixEnd_3813844 1958335113266081551510457 := by
  unfold tailWord_3813844
  simp only [CollatzResearch.WordTrace]
  refine ⟨69551159197551007771736293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92734878930068010362315057 69551159197551007771736293)
  ·
    refine ⟨13040842349540813957200555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69551159197551007771736293 13040842349540813957200555)
    ·
      refine ⟨19561263524311220935800833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13040842349540813957200555 19561263524311220935800833)
      ·
        refine ⟨14670947643233415701850625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19561263524311220935800833 14670947643233415701850625)
        ·
          refine ⟨11003210732425061776387969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14670947643233415701850625 11003210732425061776387969)
          ·
            refine ⟨8252408049318796332290977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11003210732425061776387969 8252408049318796332290977)
            ·
              refine ⟨6189306036989097249218233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8252408049318796332290977 6189306036989097249218233)
              ·
                refine ⟨4641979527741822936913675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6189306036989097249218233 4641979527741822936913675)
                ·
                  refine ⟨6962969291612734405370513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4641979527741822936913675 6962969291612734405370513)
                  ·
                    refine ⟨5222226968709550804027885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6962969291612734405370513 5222226968709550804027885)
                    ·
                      refine ⟨1958335113266081551510457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5222226968709550804027885 1958335113266081551510457)
                      ·
                        rfl

theorem cell23_3813844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_3813844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813844 prefixEnd_3813844 := by exact prefixLift 3813844
  have htrace : WordTrace (prefixWord ++ tailWord_3813844) baseStart_3813844 baseEnd_3813844 := by
    simpa [prefixWord, tailWord_3813844, baseEnd_3813844] using wordTrace_append hprefix tailTrace_3813844
  have hstable : (prefixWord ++ tailWord_3813844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813844).length < 2 ^ (prefixWord ++ tailWord_3813844).sum := by decide
  have hdescent : baseEnd_3813844 < baseStart_3813844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813867 : List Nat := [1, 1, 1, 1, 2, 3, 3, 5, 1, 3, 2]
def baseStart_3813867 : Nat := 118140960795 + 3813867 * 2 ^ 59
def prefixEnd_3813867 : Nat := 4983230072969 + 3 ^ 40 * 3813867 * 2
def baseEnd_3813867 : Nat := 1958346923321134961522851

theorem tailTrace_3813867 : CollatzResearch.WordTrace tailWord_3813867 prefixEnd_3813867 1958346923321134961522851 := by
  unfold tailWord_3813867
  simp only [CollatzResearch.WordTrace]
  refine ⟨139103157274018690471559855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92735438182679126981039903 139103157274018690471559855)
  ·
    refine ⟨208654735911028035707339783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139103157274018690471559855 208654735911028035707339783)
    ·
      refine ⟨312982103866542053561009675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208654735911028035707339783 312982103866542053561009675)
      ·
        refine ⟨469473155799813080341514513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312982103866542053561009675 469473155799813080341514513)
        ·
          refine ⟨352104866849859810256135885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469473155799813080341514513 352104866849859810256135885)
          ·
            refine ⟨132039325068697428846050957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352104866849859810256135885 132039325068697428846050957)
            ·
              refine ⟨49514746900761535817269109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132039325068697428846050957 49514746900761535817269109)
              ·
                refine ⟨4642007521946393982868979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49514746900761535817269109 4642007521946393982868979)
                ·
                  refine ⟨6963011282919590974303469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4642007521946393982868979 6963011282919590974303469)
                  ·
                    refine ⟨2611129231094846615363801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6963011282919590974303469 2611129231094846615363801)
                    ·
                      refine ⟨1958346923321134961522851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2611129231094846615363801 1958346923321134961522851)
                      ·
                        rfl

theorem cell23_3813867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 3, 2].length) (baseStart_3813867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813867 prefixEnd_3813867 := by exact prefixLift 3813867
  have htrace : WordTrace (prefixWord ++ tailWord_3813867) baseStart_3813867 baseEnd_3813867 := by
    simpa [prefixWord, tailWord_3813867, baseEnd_3813867] using wordTrace_append hprefix tailTrace_3813867
  have hstable : (prefixWord ++ tailWord_3813867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813867).length < 2 ^ (prefixWord ++ tailWord_3813867).sum := by decide
  have hdescent : baseEnd_3813867 < baseStart_3813867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813883 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 5]
def baseStart_3813883 : Nat := 118140960795 + 3813883 * 2 ^ 59
def prefixEnd_3813883 : Nat := 4983230072969 + 3 ^ 40 * 3813883 * 2
def baseEnd_3813883 : Nat := 1958355139011606898922777

theorem tailTrace_3813883 : CollatzResearch.WordTrace tailWord_3813883 prefixEnd_3813883 1958355139011606898922777 := by
  unfold tailWord_3813883
  simp only [CollatzResearch.WordTrace]
  refine ⟨139103740841960725204142303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92735827227973816802761535 139103740841960725204142303)
  ·
    refine ⟨208655611262941087806213455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139103740841960725204142303 208655611262941087806213455)
    ·
      refine ⟨312983416894411631709320183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208655611262941087806213455 312983416894411631709320183)
      ·
        refine ⟨469475125341617447563980275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312983416894411631709320183 469475125341617447563980275)
        ·
          refine ⟨704212688012426171345970413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469475125341617447563980275 704212688012426171345970413)
          ·
            refine ⟨264079758004659814254738905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 704212688012426171345970413 264079758004659814254738905)
            ·
              refine ⟨198059818503494860691054179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264079758004659814254738905 198059818503494860691054179)
              ·
                refine ⟨297089727755242291036581269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198059818503494860691054179 297089727755242291036581269)
                ·
                  refine ⟨13926080988526982392339747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 297089727755242291036581269 13926080988526982392339747)
                  ·
                    refine ⟨20889121482790473588509621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13926080988526982392339747 20889121482790473588509621)
                    ·
                      refine ⟨1958355139011606898922777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20889121482790473588509621 1958355139011606898922777)
                      ·
                        rfl

theorem cell23_3813883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 5].length) (baseStart_3813883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813883 prefixEnd_3813883 := by exact prefixLift 3813883
  have htrace : WordTrace (prefixWord ++ tailWord_3813883) baseStart_3813883 baseEnd_3813883 := by
    simpa [prefixWord, tailWord_3813883, baseEnd_3813883] using wordTrace_append hprefix tailTrace_3813883
  have hstable : (prefixWord ++ tailWord_3813883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813883).length < 2 ^ (prefixWord ++ tailWord_3813883).sum := by decide
  have hdescent : baseEnd_3813883 < baseStart_3813883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813897 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 6, 2, 2]
def baseStart_3813897 : Nat := 118140960795 + 3813897 * 2 ^ 59
def prefixEnd_3813897 : Nat := 4983230072969 + 3 ^ 40 * 3813897 * 2
def baseEnd_3813897 : Nat := 1958362327740769844147713

theorem tailTrace_3813897 : CollatzResearch.WordTrace tailWord_3813897 prefixEnd_3813897 1958362327740769844147713 := by
  unfold tailWord_3813897
  simp only [CollatzResearch.WordTrace]
  refine ⟨139104251463910005595151945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92736167642606670396767963 139104251463910005595151945)
  ·
    refine ⟨104328188597932504196363959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139104251463910005595151945 104328188597932504196363959)
    ·
      refine ⟨156492282896898756294545939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104328188597932504196363959 156492282896898756294545939)
      ·
        refine ⟨234738424345348134441818909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156492282896898756294545939 234738424345348134441818909)
        ·
          refine ⟨88026909129505550415682091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234738424345348134441818909 88026909129505550415682091)
          ·
            refine ⟨132040363694258325623523137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88026909129505550415682091 132040363694258325623523137)
            ·
              refine ⟨99030272770693744217642353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132040363694258325623523137 99030272770693744217642353)
              ·
                refine ⟨74272704578020308163231765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99030272770693744217642353 74272704578020308163231765)
                ·
                  refine ⟨3481533027094701945151489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74272704578020308163231765 3481533027094701945151489)
                  ·
                    refine ⟨2611149770321026458863617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3481533027094701945151489 2611149770321026458863617)
                    ·
                      refine ⟨1958362327740769844147713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2611149770321026458863617 1958362327740769844147713)
                      ·
                        rfl

theorem cell23_3813897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 2, 2].length) (baseStart_3813897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813897 prefixEnd_3813897 := by exact prefixLift 3813897
  have htrace : WordTrace (prefixWord ++ tailWord_3813897) baseStart_3813897 baseEnd_3813897 := by
    simpa [prefixWord, tailWord_3813897, baseEnd_3813897] using wordTrace_append hprefix tailTrace_3813897
  have hstable : (prefixWord ++ tailWord_3813897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813897).length < 2 ^ (prefixWord ++ tailWord_3813897).sum := by decide
  have hdescent : baseEnd_3813897 < baseStart_3813897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813900 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 2, 1, 5]
def baseStart_3813900 : Nat := 118140960795 + 3813900 * 2 ^ 59
def prefixEnd_3813900 : Nat := 4983230072969 + 3 ^ 40 * 3813900 * 2
def baseEnd_3813900 : Nat := 1958363868182733332410199

theorem tailTrace_3813900 : CollatzResearch.WordTrace tailWord_3813900 prefixEnd_3813900 1958363868182733332410199 := by
  unfold tailWord_3813900
  simp only [CollatzResearch.WordTrace]
  refine ⟨69552180441449568553755577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92736240588599424738340769 69552180441449568553755577)
  ·
    refine ⟨52164135331087176415316683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69552180441449568553755577 52164135331087176415316683)
    ·
      refine ⟨78246202996630764622975025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52164135331087176415316683 78246202996630764622975025)
      ·
        refine ⟨58684652247473073467231269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78246202996630764622975025 58684652247473073467231269)
        ·
          refine ⟨11003372296401201275105863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58684652247473073467231269 11003372296401201275105863)
          ·
            refine ⟨16505058444601801912658795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11003372296401201275105863 16505058444601801912658795)
            ·
              refine ⟨24757587666902702868988193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16505058444601801912658795 24757587666902702868988193)
              ·
                refine ⟨18568190750177027151741145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24757587666902702868988193 18568190750177027151741145)
                ·
                  refine ⟨13926143062632770363805859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18568190750177027151741145 13926143062632770363805859)
                  ·
                    refine ⟨20889214593949155545708789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13926143062632770363805859 20889214593949155545708789)
                    ·
                      refine ⟨1958363868182733332410199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20889214593949155545708789 1958363868182733332410199)
                      ·
                        rfl

theorem cell23_3813900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_3813900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813900 prefixEnd_3813900 := by exact prefixLift 3813900
  have htrace : WordTrace (prefixWord ++ tailWord_3813900) baseStart_3813900 baseEnd_3813900 := by
    simpa [prefixWord, tailWord_3813900, baseEnd_3813900] using wordTrace_append hprefix tailTrace_3813900
  have hstable : (prefixWord ++ tailWord_3813900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813900).length < 2 ^ (prefixWord ++ tailWord_3813900).sum := by decide
  have hdescent : baseEnd_3813900 < baseStart_3813900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813987 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 4, 4, 2]
def baseStart_3813987 : Nat := 118140960795 + 3813987 * 2 ^ 59
def prefixEnd_3813987 : Nat := 4983230072969 + 3 ^ 40 * 3813987 * 2
def baseEnd_3813987 : Nat := 1958408540999674492022299

theorem tailTrace_3813987 : CollatzResearch.WordTrace tailWord_3813987 prefixEnd_3813987 1958408540999674492022299 := by
  unfold tailWord_3813987
  simp only [CollatzResearch.WordTrace]
  refine ⟨139107534033583950965928215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92738356022389300643952143 139107534033583950965928215)
  ·
    refine ⟨208661301050375926448892323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139107534033583950965928215 208661301050375926448892323)
    ·
      refine ⟨312991951575563889673338485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208661301050375926448892323 312991951575563889673338485)
      ·
        refine ⟨29342995460209114656875483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 312991951575563889673338485 29342995460209114656875483)
        ·
          refine ⟨44014493190313671985313225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29342995460209114656875483 44014493190313671985313225)
          ·
            refine ⟨33010869892735253988984919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44014493190313671985313225 33010869892735253988984919)
            ·
              refine ⟨49516304839102880983477379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33010869892735253988984919 49516304839102880983477379)
              ·
                refine ⟨74274457258654321475216069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49516304839102880983477379 74274457258654321475216069)
                ·
                  refine ⟨13926460735997685276603013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74274457258654321475216069 13926460735997685276603013)
                  ·
                    refine ⟨2611211387999565989363065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13926460735997685276603013 2611211387999565989363065)
                    ·
                      refine ⟨1958408540999674492022299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2611211387999565989363065 1958408540999674492022299)
                      ·
                        rfl

theorem cell23_3813987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_3813987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813987 prefixEnd_3813987 := by exact prefixLift 3813987
  have htrace : WordTrace (prefixWord ++ tailWord_3813987) baseStart_3813987 baseEnd_3813987 := by
    simpa [prefixWord, tailWord_3813987, baseEnd_3813987] using wordTrace_append hprefix tailTrace_3813987
  have hstable : (prefixWord ++ tailWord_3813987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813987).length < 2 ^ (prefixWord ++ tailWord_3813987).sum := by decide
  have hdescent : baseEnd_3813987 < baseStart_3813987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814048 : List Nat := [2, 1, 1, 4, 4, 1, 3, 2, 1, 4]
def baseStart_3814048 : Nat := 118140960795 + 3814048 * 2 ^ 59
def prefixEnd_3814048 : Nat := 4983230072969 + 3 ^ 40 * 3814048 * 2
def baseEnd_3814048 : Nat := 652813287773199584453173

theorem tailTrace_3814048 : CollatzResearch.WordTrace tailWord_3814048 prefixEnd_3814048 652813287773199584453173 := by
  unfold tailWord_3814048
  simp only [CollatzResearch.WordTrace]
  refine ⟨69554879443181479191949399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92739839257575305589265865 69554879443181479191949399)
  ·
    refine ⟨104332319164772218787924099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69554879443181479191949399 104332319164772218787924099)
    ·
      refine ⟨156498478747158328181886149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104332319164772218787924099 156498478747158328181886149)
      ·
        refine ⟨29343464765092186534103653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156498478747158328181886149 29343464765092186534103653)
        ·
          refine ⟨5501899643454784975144435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29343464765092186534103653 5501899643454784975144435)
          ·
            refine ⟨8252849465182177462716653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5501899643454784975144435 8252849465182177462716653)
            ·
              refine ⟨3094818549443316548518745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8252849465182177462716653 3094818549443316548518745)
              ·
                refine ⟨2321113912082487411389059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3094818549443316548518745 2321113912082487411389059)
                ·
                  refine ⟨3481670868123731117083589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2321113912082487411389059 3481670868123731117083589)
                  ·
                    refine ⟨652813287773199584453173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3481670868123731117083589 652813287773199584453173)
                    ·
                      rfl

theorem cell23_3814048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 1, 4].length) (baseStart_3814048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814048 prefixEnd_3814048 := by exact prefixLift 3814048
  have htrace : WordTrace (prefixWord ++ tailWord_3814048) baseStart_3814048 baseEnd_3814048 := by
    simpa [prefixWord, tailWord_3814048, baseEnd_3814048] using wordTrace_append hprefix tailTrace_3814048
  have hstable : (prefixWord ++ tailWord_3814048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814048).length < 2 ^ (prefixWord ++ tailWord_3814048).sum := by decide
  have hdescent : baseEnd_3814048 < baseStart_3814048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814061 : List Nat := [1, 5, 2, 1, 1, 4, 2, 1, 6]
def baseStart_3814061 : Nat := 118140960795 + 3814061 * 2 ^ 59
def prefixEnd_3814061 : Nat := 4983230072969 + 3 ^ 40 * 3814061 * 2
def baseEnd_3814061 : Nat := 217605170952011911388551

theorem tailTrace_3814061 : CollatzResearch.WordTrace tailWord_3814061 prefixEnd_3814061 217605170952011911388551 := by
  unfold tailWord_3814061
  simp only [CollatzResearch.WordTrace]
  refine ⟨139110233035315861604122037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92740155356877241069414691 139110233035315861604122037)
  ·
    refine ⟨13041584347060862025386441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139110233035315861604122037 13041584347060862025386441)
    ·
      refine ⟨9781188260295646519039831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13041584347060862025386441 9781188260295646519039831)
      ·
        refine ⟨14671782390443469778559747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9781188260295646519039831 14671782390443469778559747)
        ·
          refine ⟨22007673585665204667839621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14671782390443469778559747 22007673585665204667839621)
          ·
            refine ⟨4126438797312225875219929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22007673585665204667839621 4126438797312225875219929)
            ·
              refine ⟨3094829097984169406414947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4126438797312225875219929 3094829097984169406414947)
              ·
                refine ⟨4642243646976254109622421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3094829097984169406414947 4642243646976254109622421)
                ·
                  refine ⟨217605170952011911388551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4642243646976254109622421 217605170952011911388551)
                  ·
                    rfl

theorem cell23_3814061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_3814061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814061 prefixEnd_3814061 := by exact prefixLift 3814061
  have htrace : WordTrace (prefixWord ++ tailWord_3814061) baseStart_3814061 baseEnd_3814061 := by
    simpa [prefixWord, tailWord_3814061, baseEnd_3814061] using wordTrace_append hprefix tailTrace_3814061
  have hstable : (prefixWord ++ tailWord_3814061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814061).length < 2 ^ (prefixWord ++ tailWord_3814061).sum := by decide
  have hdescent : baseEnd_3814061 < baseStart_3814061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814087 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 4, 4]
def baseStart_3814087 : Nat := 118140960795 + 3814087 * 2 ^ 59
def prefixEnd_3814087 : Nat := 4983230072969 + 3 ^ 40 * 3814087 * 2
def baseEnd_3814087 : Nat := 652819963021708033590613

theorem tailTrace_3814087 : CollatzResearch.WordTrace tailWord_3814087 prefixEnd_3814087 652819963021708033590613 := by
  unfold tailWord_3814087
  simp only [CollatzResearch.WordTrace]
  refine ⟨139111181333221668044568515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92740787555481112029712343 139111181333221668044568515)
  ·
    refine ⟨208666771999832502066852773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139111181333221668044568515 208666771999832502066852773)
    ·
      refine ⟨39125019749968594137534895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208666771999832502066852773 39125019749968594137534895)
      ·
        refine ⟨58687529624952891206302343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39125019749968594137534895 58687529624952891206302343)
        ·
          refine ⟨88031294437429336809453515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58687529624952891206302343 88031294437429336809453515)
          ·
            refine ⟨132046941656144005214180273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88031294437429336809453515 132046941656144005214180273)
            ·
              refine ⟨99035206242108003910635205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132046941656144005214180273 99035206242108003910635205)
              ·
                refine ⟨18569101170395250733244101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99035206242108003910635205 18569101170395250733244101)
                ·
                  refine ⟨3481706469449109512483269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18569101170395250733244101 3481706469449109512483269)
                  ·
                    refine ⟨652819963021708033590613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3481706469449109512483269 652819963021708033590613)
                    ·
                      rfl

theorem cell23_3814087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_3814087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814087 prefixEnd_3814087 := by exact prefixLift 3814087
  have htrace : WordTrace (prefixWord ++ tailWord_3814087) baseStart_3814087 baseEnd_3814087 := by
    simpa [prefixWord, tailWord_3814087, baseEnd_3814087] using wordTrace_append hprefix tailTrace_3814087
  have hstable : (prefixWord ++ tailWord_3814087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814087).length < 2 ^ (prefixWord ++ tailWord_3814087).sum := by decide
  have hdescent : baseEnd_3814087 < baseStart_3814087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814104 : List Nat := [2, 1, 2, 2, 3, 2, 1, 4, 2, 4]
def baseStart_3814104 : Nat := 118140960795 + 3814104 * 2 ^ 59
def prefixEnd_3814104 : Nat := 4983230072969 + 3 ^ 40 * 3814104 * 2
def baseEnd_3814104 : Nat := 652822872745416844753087

theorem tailTrace_3814104 : CollatzResearch.WordTrace tailWord_3814104 prefixEnd_3814104 652822872745416844753087 := by
  unfold tailWord_3814104
  simp only [CollatzResearch.WordTrace]
  refine ⟨69555900687080039973968683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92741200916106719965291577 69555900687080039973968683)
  ·
    refine ⟨104333851030620059960953025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69555900687080039973968683 104333851030620059960953025)
    ·
      refine ⟨78250388272965044970714769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104333851030620059960953025 78250388272965044970714769)
      ·
        refine ⟨58687791204723783728036077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78250388272965044970714769 58687791204723783728036077)
        ·
          refine ⟨22007921701771418898013529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58687791204723783728036077 22007921701771418898013529)
          ·
            refine ⟨16505941276328564173510147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22007921701771418898013529 16505941276328564173510147)
            ·
              refine ⟨24758911914492846260265221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16505941276328564173510147 24758911914492846260265221)
              ·
                refine ⟨4642295983967408673799729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24758911914492846260265221 4642295983967408673799729)
                ·
                  refine ⟨3481721987975556505349797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4642295983967408673799729 3481721987975556505349797)
                  ·
                    refine ⟨652822872745416844753087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3481721987975556505349797 652822872745416844753087)
                    ·
                      rfl

theorem cell23_3814104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_3814104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814104 prefixEnd_3814104 := by exact prefixLift 3814104
  have htrace : WordTrace (prefixWord ++ tailWord_3814104) baseStart_3814104 baseEnd_3814104 := by
    simpa [prefixWord, tailWord_3814104, baseEnd_3814104] using wordTrace_append hprefix tailTrace_3814104
  have hstable : (prefixWord ++ tailWord_3814104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814104).length < 2 ^ (prefixWord ++ tailWord_3814104).sum := by decide
  have hdescent : baseEnd_3814104 < baseStart_3814104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814117 : List Nat := [1, 3, 1, 4, 1, 2, 3, 8]
def baseStart_3814117 : Nat := 118140960795 + 3814117 * 2 ^ 59
def prefixEnd_3814117 : Nat := 4983230072969 + 3 ^ 40 * 3814117 * 2
def baseEnd_3814117 : Nat := 72536121980916999385063

theorem tailTrace_3814117 : CollatzResearch.WordTrace tailWord_3814117 prefixEnd_3814117 72536121980916999385063 := by
  unfold tailWord_3814117
  simp only [CollatzResearch.WordTrace]
  refine ⟨139112275523112983168160605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92741517015408655445440403 139112275523112983168160605)
  ·
    refine ⟨52167103321167368688060227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139112275523112983168160605 52167103321167368688060227)
    ·
      refine ⟨78250654981751053032090341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52167103321167368688060227 78250654981751053032090341)
      ·
        refine ⟨14671997809078322443516939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78250654981751053032090341 14671997809078322443516939)
        ·
          refine ⟨22007996713617483665275409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14671997809078322443516939 22007996713617483665275409)
          ·
            refine ⟨16505997535213112748956557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22007996713617483665275409 16505997535213112748956557)
            ·
              refine ⟨6189749075704917280858709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16505997535213112748956557 6189749075704917280858709)
              ·
                refine ⟨72536121980916999385063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6189749075704917280858709 72536121980916999385063)
                ·
                  rfl

theorem cell23_3814117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 8].length) (baseStart_3814117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814117 prefixEnd_3814117 := by exact prefixLift 3814117
  have htrace : WordTrace (prefixWord ++ tailWord_3814117) baseStart_3814117 baseEnd_3814117 := by
    simpa [prefixWord, tailWord_3814117, baseEnd_3814117] using wordTrace_append hprefix tailTrace_3814117
  have hstable : (prefixWord ++ tailWord_3814117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814117).length < 2 ^ (prefixWord ++ tailWord_3814117).sum := by decide
  have hdescent : baseEnd_3814117 < baseStart_3814117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814132 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_3814132 : Nat := 118140960795 + 3814132 * 2 ^ 59
def prefixEnd_3814132 : Nat := 4983230072969 + 3 ^ 40 * 3814132 * 2
def baseEnd_3814132 : Nat := 1958482995694576424709133

theorem tailTrace_3814132 : CollatzResearch.WordTrace tailWord_3814132 prefixEnd_3814132 1958482995694576424709133 := by
  unfold tailWord_3814132
  simp only [CollatzResearch.WordTrace]
  refine ⟨69556411309029320364978325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92741881745372427153304433 69556411309029320364978325)
  ·
    refine ⟨3260456780110749392108359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69556411309029320364978325 3260456780110749392108359)
    ·
      refine ⟨4890685170166124088162539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3260456780110749392108359 4890685170166124088162539)
      ·
        refine ⟨7336027755249186132243809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4890685170166124088162539 7336027755249186132243809)
        ·
          refine ⟨5502020816436889599182857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7336027755249186132243809 5502020816436889599182857)
          ·
            refine ⟨4126515612327667199387143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5502020816436889599182857 4126515612327667199387143)
            ·
              refine ⟨6189773418491500799080715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4126515612327667199387143 6189773418491500799080715)
              ·
                refine ⟨9284660127737251198621073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6189773418491500799080715 9284660127737251198621073)
                ·
                  refine ⟨6963495095802938398965805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9284660127737251198621073 6963495095802938398965805)
                  ·
                    refine ⟨2611310660926101899612177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6963495095802938398965805 2611310660926101899612177)
                    ·
                      refine ⟨1958482995694576424709133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2611310660926101899612177 1958482995694576424709133)
                      ·
                        rfl

theorem cell23_3814132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_3814132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814132 prefixEnd_3814132 := by exact prefixLift 3814132
  have htrace : WordTrace (prefixWord ++ tailWord_3814132) baseStart_3814132 baseEnd_3814132 := by
    simpa [prefixWord, tailWord_3814132, baseEnd_3814132] using wordTrace_append hprefix tailTrace_3814132
  have hstable : (prefixWord ++ tailWord_3814132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814132).length < 2 ^ (prefixWord ++ tailWord_3814132).sum := by decide
  have hdescent : baseEnd_3814132 < baseStart_3814132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814134 : List Nat := [5, 1, 1, 1, 1, 2, 5, 7]
def baseStart_3814134 : Nat := 118140960795 + 3814134 * 2 ^ 59
def prefixEnd_3814134 : Nat := 4983230072969 + 3 ^ 40 * 3814134 * 2
def baseEnd_3814134 : Nat := 72536445283551311736449

theorem tailTrace_3814134 : CollatzResearch.WordTrace tailWord_3814134 prefixEnd_3814134 72536445283551311736449 := by
  unfold tailWord_3814134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8694555972753212191970591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92741930376034263381019637 8694555972753212191970591)
  ·
    refine ⟨13041833959129818287955887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8694555972753212191970591 13041833959129818287955887)
    ·
      refine ⟨19562750938694727431933831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13041833959129818287955887 19562750938694727431933831)
      ·
        refine ⟨29344126408042091147900747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19562750938694727431933831 29344126408042091147900747)
        ·
          refine ⟨44016189612063136721851121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29344126408042091147900747 44016189612063136721851121)
          ·
            refine ⟨33012142209047352541388341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44016189612063136721851121 33012142209047352541388341)
            ·
              refine ⟨3094888332098189300755157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33012142209047352541388341 3094888332098189300755157)
              ·
                refine ⟨72536445283551311736449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3094888332098189300755157 72536445283551311736449)
                ·
                  rfl

theorem cell23_3814134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_3814134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814134 prefixEnd_3814134 := by exact prefixLift 3814134
  have htrace : WordTrace (prefixWord ++ tailWord_3814134) baseStart_3814134 baseEnd_3814134 := by
    simpa [prefixWord, tailWord_3814134, baseEnd_3814134] using wordTrace_append hprefix tailTrace_3814134
  have hstable : (prefixWord ++ tailWord_3814134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814134).length < 2 ^ (prefixWord ++ tailWord_3814134).sum := by decide
  have hdescent : baseEnd_3814134 < baseStart_3814134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814161 : List Nat := [1, 2, 2, 1, 1, 3, 5, 2, 2, 1, 3]
def baseStart_3814161 : Nat := 118140960795 + 3814161 * 2 ^ 59
def prefixEnd_3814161 : Nat := 4983230072969 + 3 ^ 40 * 3814161 * 2
def baseEnd_3814161 : Nat := 1958497886633556811246499

theorem tailTrace_3814161 : CollatzResearch.WordTrace tailWord_3814161 prefixEnd_3814161 1958497886633556811246499 := by
  unfold tailWord_3814161
  simp only [CollatzResearch.WordTrace]
  refine ⟨139113880334953578682762337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92742586889969052455174891 139113880334953578682762337)
  ·
    refine ⟨104335410251215184012071753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139113880334953578682762337 104335410251215184012071753)
    ·
      refine ⟨78251557688411388009053815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104335410251215184012071753 78251557688411388009053815)
      ·
        refine ⟨117377336532617082013580723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78251557688411388009053815 117377336532617082013580723)
        ·
          refine ⟨176066004798925623020371085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117377336532617082013580723 176066004798925623020371085)
          ·
            refine ⟨66024751799597108632639157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176066004798925623020371085 66024751799597108632639157)
            ·
              refine ⟨6189820481212228934309921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66024751799597108632639157 6189820481212228934309921)
              ·
                refine ⟨4642365360909171700732441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6189820481212228934309921 4642365360909171700732441)
                ·
                  refine ⟨3481774020681878775549331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4642365360909171700732441 3481774020681878775549331)
                  ·
                    refine ⟨5222661031022818163323997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3481774020681878775549331 5222661031022818163323997)
                    ·
                      refine ⟨1958497886633556811246499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5222661031022818163323997 1958497886633556811246499)
                      ·
                        rfl

theorem cell23_3814161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_3814161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814161 prefixEnd_3814161 := by exact prefixLift 3814161
  have htrace : WordTrace (prefixWord ++ tailWord_3814161) baseStart_3814161 baseEnd_3814161 := by
    simpa [prefixWord, tailWord_3814161, baseEnd_3814161] using wordTrace_append hprefix tailTrace_3814161
  have hstable : (prefixWord ++ tailWord_3814161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814161).length < 2 ^ (prefixWord ++ tailWord_3814161).sum := by decide
  have hdescent : baseEnd_3814161 < baseStart_3814161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814177 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 2, 6]
def baseStart_3814177 : Nat := 118140960795 + 3814177 * 2 ^ 59
def prefixEnd_3814177 : Nat := 4983230072969 + 3 ^ 40 * 3814177 * 2
def baseEnd_3814177 : Nat := 652835367441342916215475

theorem tailTrace_3814177 : CollatzResearch.WordTrace tailWord_3814177 prefixEnd_3814177 652835367441342916215475 := by
  unfold tailWord_3814177
  simp only [CollatzResearch.WordTrace]
  refine ⟨139114463902895613415344785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92742975935263742276896523 139114463902895613415344785)
  ·
    refine ⟨104335847927171710061508589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139114463902895613415344785 104335847927171710061508589)
    ·
      refine ⟨39125942972689391273065721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104335847927171710061508589 39125942972689391273065721)
      ·
        refine ⟨29344457229517043454799291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39125942972689391273065721 29344457229517043454799291)
        ·
          refine ⟨44016685844275565182198937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29344457229517043454799291 44016685844275565182198937)
          ·
            refine ⟨33012514383206673886649203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44016685844275565182198937 33012514383206673886649203)
            ·
              refine ⟨49518771574810010829973805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33012514383206673886649203 49518771574810010829973805)
              ·
                refine ⟨18569539340553754061240177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49518771574810010829973805 18569539340553754061240177)
                ·
                  refine ⟨13927154505415315545930133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18569539340553754061240177 13927154505415315545930133)
                  ·
                    refine ⟨652835367441342916215475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13927154505415315545930133 652835367441342916215475)
                    ·
                      rfl

theorem cell23_3814177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_3814177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814177 prefixEnd_3814177 := by exact prefixLift 3814177
  have htrace : WordTrace (prefixWord ++ tailWord_3814177) baseStart_3814177 baseEnd_3814177 := by
    simpa [prefixWord, tailWord_3814177, baseEnd_3814177] using wordTrace_append hprefix tailTrace_3814177
  have hstable : (prefixWord ++ tailWord_3814177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814177).length < 2 ^ (prefixWord ++ tailWord_3814177).sum := by decide
  have hdescent : baseEnd_3814177 < baseStart_3814177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814187 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 3]
def baseStart_3814187 : Nat := 118140960795 + 3814187 * 2 ^ 59
def prefixEnd_3814187 : Nat := 4983230072969 + 3 ^ 40 * 3814187 * 2
def baseEnd_3814187 : Nat := 1958511237130573709521379

theorem tailTrace_3814187 : CollatzResearch.WordTrace tailWord_3814187 prefixEnd_3814187 1958511237130573709521379 := by
  unfold tailWord_3814187
  simp only [CollatzResearch.WordTrace]
  refine ⟨139114828632859385123208815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92743219088572923415472543 139114828632859385123208815)
  ·
    refine ⟨208672242949289077684813223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139114828632859385123208815 208672242949289077684813223)
    ·
      refine ⟨313008364423933616527219835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208672242949289077684813223 313008364423933616527219835)
      ·
        refine ⟨469512546635900424790829753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313008364423933616527219835 469512546635900424790829753)
        ·
          refine ⟨352134409976925318593122315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469512546635900424790829753 352134409976925318593122315)
          ·
            refine ⟨528201614965387977889683473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352134409976925318593122315 528201614965387977889683473)
            ·
              refine ⟨396151211224040983417262605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528201614965387977889683473 396151211224040983417262605)
              ·
                refine ⟨148556704209015368781473477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 396151211224040983417262605 148556704209015368781473477)
                ·
                  refine ⟨27854382039190381646526277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148556704209015368781473477 27854382039190381646526277)
                  ·
                    refine ⟨5222696632348196558723677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27854382039190381646526277 5222696632348196558723677)
                    ·
                      refine ⟨1958511237130573709521379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5222696632348196558723677 1958511237130573709521379)
                      ·
                        rfl

theorem cell23_3814187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 3].length) (baseStart_3814187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814187 prefixEnd_3814187 := by exact prefixLift 3814187
  have htrace : WordTrace (prefixWord ++ tailWord_3814187) baseStart_3814187 baseEnd_3814187 := by
    simpa [prefixWord, tailWord_3814187, baseEnd_3814187] using wordTrace_append hprefix tailTrace_3814187
  have hstable : (prefixWord ++ tailWord_3814187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814187).length < 2 ^ (prefixWord ++ tailWord_3814187).sum := by decide
  have hdescent : baseEnd_3814187 < baseStart_3814187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814224 : List Nat := [2, 1, 1, 1, 1, 4, 2, 6, 5]
def baseStart_3814224 : Nat := 118140960795 + 3814224 * 2 ^ 59
def prefixEnd_3814224 : Nat := 4983230072969 + 3 ^ 40 * 3814224 * 2
def baseEnd_3814224 : Nat := 217614470657198896084301

theorem tailTrace_3814224 : CollatzResearch.WordTrace tailWord_3814224 prefixEnd_3814224 217614470657198896084301 := by
  unfold tailWord_3814224
  simp only [CollatzResearch.WordTrace]
  refine ⟨69558089066862670221152863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92744118755816893628203817 69558089066862670221152863)
  ·
    refine ⟨104337133600294005331729295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69558089066862670221152863 104337133600294005331729295)
    ·
      refine ⟨156505700400441007997593943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104337133600294005331729295 156505700400441007997593943)
      ·
        refine ⟨234758550600661511996390915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156505700400441007997593943 234758550600661511996390915)
        ·
          refine ⟨352137825900992267994586373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234758550600661511996390915 352137825900992267994586373)
          ·
            refine ⟨66025842356436050248984945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352137825900992267994586373 66025842356436050248984945)
            ·
              refine ⟨49519381767327037686738709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66025842356436050248984945 49519381767327037686738709)
              ·
                refine ⟨2321221020343454891565877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49519381767327037686738709 2321221020343454891565877)
                ·
                  refine ⟨217614470657198896084301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2321221020343454891565877 217614470657198896084301)
                  ·
                    rfl

theorem cell23_3814224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 5].length) (baseStart_3814224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814224 prefixEnd_3814224 := by exact prefixLift 3814224
  have htrace : WordTrace (prefixWord ++ tailWord_3814224) baseStart_3814224 baseEnd_3814224 := by
    simpa [prefixWord, tailWord_3814224, baseEnd_3814224] using wordTrace_append hprefix tailTrace_3814224
  have hstable : (prefixWord ++ tailWord_3814224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814224).length < 2 ^ (prefixWord ++ tailWord_3814224).sum := by decide
  have hdescent : baseEnd_3814224 < baseStart_3814224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814297 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 10]
def baseStart_3814297 : Nat := 118140960795 + 3814297 * 2 ^ 59
def prefixEnd_3814297 : Nat := 4983230072969 + 3 ^ 40 * 3814297 * 2
def baseEnd_3814297 : Nat := 217618635555840919905097

theorem tailTrace_3814297 : CollatzResearch.WordTrace tailWord_3814297 prefixEnd_3814297 217618635555840919905097 := by
  unfold tailWord_3814297
  simp only [CollatzResearch.WordTrace]
  refine ⟨139118840662460873909713145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92745893774973915939808763 139118840662460873909713145)
  ·
    refine ⟨104339130496845655432284859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139118840662460873909713145 104339130496845655432284859)
    ·
      refine ⟨156508695745268483148427289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104339130496845655432284859 156508695745268483148427289)
      ·
        refine ⟨117381521808951362361320467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156508695745268483148427289 117381521808951362361320467)
        ·
          refine ⟨176072282713427043541980701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117381521808951362361320467 176072282713427043541980701)
          ·
            refine ⟨66027106017535141328242763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176072282713427043541980701 66027106017535141328242763)
            ·
              refine ⟨99040659026302711992364145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66027106017535141328242763 99040659026302711992364145)
              ·
                refine ⟨74280494269727033994273109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99040659026302711992364145 74280494269727033994273109)
                ·
                  refine ⟨217618635555840919905097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 74280494269727033994273109 217618635555840919905097)
                  ·
                    rfl

theorem cell23_3814297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 10].length) (baseStart_3814297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814297 prefixEnd_3814297 := by exact prefixLift 3814297
  have htrace : WordTrace (prefixWord ++ tailWord_3814297) baseStart_3814297 baseEnd_3814297 := by
    simpa [prefixWord, tailWord_3814297, baseEnd_3814297] using wordTrace_append hprefix tailTrace_3814297
  have hstable : (prefixWord ++ tailWord_3814297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814297).length < 2 ^ (prefixWord ++ tailWord_3814297).sum := by decide
  have hdescent : baseEnd_3814297 < baseStart_3814297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814301 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 3, 4]
def baseStart_3814301 : Nat := 118140960795 + 3814301 * 2 ^ 59
def prefixEnd_3814301 : Nat := 4983230072969 + 3 ^ 40 * 3814301 * 2
def baseEnd_3814301 : Nat := 652856591308395421165285

theorem tailTrace_3814301 : CollatzResearch.WordTrace tailWord_3814301 prefixEnd_3814301 652856591308395421165285 := by
  unfold tailWord_3814301
  simp only [CollatzResearch.WordTrace]
  refine ⟨139118986554446382592858757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92745991036297588395239171 139118986554446382592858757)
  ·
    refine ⟨26084809978958696736161017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139118986554446382592858757 26084809978958696736161017)
    ·
      refine ⟨19563607484219022552120763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26084809978958696736161017 19563607484219022552120763)
      ·
        refine ⟨29345411226328533828181145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19563607484219022552120763 29345411226328533828181145)
        ·
          refine ⟨22009058419746400371135859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29345411226328533828181145 22009058419746400371135859)
          ·
            refine ⟨33013587629619600556703789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22009058419746400371135859 33013587629619600556703789)
            ·
              refine ⟨12380095361107350208763921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33013587629619600556703789 12380095361107350208763921)
              ·
                refine ⟨9285071520830512656572941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12380095361107350208763921 9285071520830512656572941)
                ·
                  refine ⟨3481901820311442246214853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9285071520830512656572941 3481901820311442246214853)
                  ·
                    refine ⟨652856591308395421165285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3481901820311442246214853 652856591308395421165285)
                    ·
                      rfl

theorem cell23_3814301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_3814301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814301 prefixEnd_3814301 := by exact prefixLift 3814301
  have htrace : WordTrace (prefixWord ++ tailWord_3814301) baseStart_3814301 baseEnd_3814301 := by
    simpa [prefixWord, tailWord_3814301, baseEnd_3814301] using wordTrace_append hprefix tailTrace_3814301
  have hstable : (prefixWord ++ tailWord_3814301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814301).length < 2 ^ (prefixWord ++ tailWord_3814301).sum := by decide
  have hdescent : baseEnd_3814301 < baseStart_3814301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814334 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_3814334 : Nat := 118140960795 + 3814334 * 2 ^ 59
def prefixEnd_3814334 : Nat := 4983230072969 + 3 ^ 40 * 3814334 * 2
def baseEnd_3814334 : Nat := 1958586718786784634383203

theorem tailTrace_3814334 : CollatzResearch.WordTrace tailWord_3814334 prefixEnd_3814334 1958586718786784634383203 := by
  unfold tailWord_3814334
  simp only [CollatzResearch.WordTrace]
  refine ⟨17390023770415853653601257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92746793442217886152540037 17390023770415853653601257)
  ·
    refine ⟨13042517827811890240200943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17390023770415853653601257 13042517827811890240200943)
    ·
      refine ⟨19563776741717835360301415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13042517827811890240200943 19563776741717835360301415)
      ·
        refine ⟨29345665112576753040452123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19563776741717835360301415 29345665112576753040452123)
        ·
          refine ⟨44018497668865129560678185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29345665112576753040452123 44018497668865129560678185)
          ·
            refine ⟨33013873251648847170508639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44018497668865129560678185 33013873251648847170508639)
            ·
              refine ⟨49520809877473270755762959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33013873251648847170508639 49520809877473270755762959)
              ·
                refine ⟨74281214816209906133644439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49520809877473270755762959 74281214816209906133644439)
                ·
                  refine ⟨111421822224314859200466659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74281214816209906133644439 111421822224314859200466659)
                  ·
                    refine ⟨167132733336472288800699989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111421822224314859200466659 167132733336472288800699989)
                    ·
                      refine ⟨1958586718786784634383203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 167132733336472288800699989 1958586718786784634383203)
                      ·
                        rfl

theorem cell23_3814334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_3814334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814334 prefixEnd_3814334 := by exact prefixLift 3814334
  have htrace : WordTrace (prefixWord ++ tailWord_3814334) baseStart_3814334 baseEnd_3814334 := by
    simpa [prefixWord, tailWord_3814334, baseEnd_3814334] using wordTrace_append hprefix tailTrace_3814334
  have hstable : (prefixWord ++ tailWord_3814334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814334).length < 2 ^ (prefixWord ++ tailWord_3814334).sum := by decide
  have hdescent : baseEnd_3814334 < baseStart_3814334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814351 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 1, 5, 2]
def baseStart_3814351 : Nat := 118140960795 + 3814351 * 2 ^ 59
def prefixEnd_3814351 : Nat := 4983230072969 + 3 ^ 40 * 3814351 * 2
def baseEnd_3814351 : Nat := 1958595447957911067870625

theorem tailTrace_3814351 : CollatzResearch.WordTrace tailWord_3814351 prefixEnd_3814351 1958595447957911067870625 := by
  unfold tailWord_3814351
  simp only [CollatzResearch.WordTrace]
  refine ⟨139120810204265241132178907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92747206802843494088119271 139120810204265241132178907)
  ·
    refine ⟨208681215306397861698268361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139120810204265241132178907 208681215306397861698268361)
    ·
      refine ⟨156510911479798396273701271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208681215306397861698268361 156510911479798396273701271)
      ·
        refine ⟨234766367219697594410551907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156510911479798396273701271 234766367219697594410551907)
        ·
          refine ⟨352149550829546391615827861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234766367219697594410551907 352149550829546391615827861)
          ·
            refine ⟨16507010195134987106991931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 352149550829546391615827861 16507010195134987106991931)
            ·
              refine ⟨24760515292702480660487897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16507010195134987106991931 24760515292702480660487897)
              ·
                refine ⟨18570386469526860495365923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24760515292702480660487897 18570386469526860495365923)
                ·
                  refine ⟨27855579704290290743048885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18570386469526860495365923 27855579704290290743048885)
                  ·
                    refine ⟨2611460597277214757160833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27855579704290290743048885 2611460597277214757160833)
                    ·
                      refine ⟨1958595447957911067870625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2611460597277214757160833 1958595447957911067870625)
                      ·
                        rfl

theorem cell23_3814351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 5, 2].length) (baseStart_3814351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814351 prefixEnd_3814351 := by exact prefixLift 3814351
  have htrace : WordTrace (prefixWord ++ tailWord_3814351) baseStart_3814351 baseEnd_3814351 := by
    simpa [prefixWord, tailWord_3814351, baseEnd_3814351] using wordTrace_append hprefix tailTrace_3814351
  have hstable : (prefixWord ++ tailWord_3814351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814351).length < 2 ^ (prefixWord ++ tailWord_3814351).sum := by decide
  have hdescent : baseEnd_3814351 < baseStart_3814351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814361 : List Nat := [1, 2, 1, 2, 5, 1, 1, 4, 1, 5]
def baseStart_3814361 : Nat := 118140960795 + 3814361 * 2 ^ 59
def prefixEnd_3814361 : Nat := 4983230072969 + 3 ^ 40 * 3814361 * 2
def baseEnd_3814361 : Nat := 652866860921485342915193

theorem tailTrace_3814361 : CollatzResearch.WordTrace tailWord_3814361 prefixEnd_3814361 652866860921485342915193 := by
  unfold tailWord_3814361
  simp only [CollatzResearch.WordTrace]
  refine ⟨139121174934229012840042937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92747449956152675226695291 139121174934229012840042937)
  ·
    refine ⟨104340881200671759630032203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139121174934229012840042937 104340881200671759630032203)
    ·
      refine ⟨156511321801007639445048305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104340881200671759630032203 156511321801007639445048305)
      ·
        refine ⟨117383491350755729583786229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156511321801007639445048305 117383491350755729583786229)
        ·
          refine ⟨11004702314133349648479959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117383491350755729583786229 11004702314133349648479959)
          ·
            refine ⟨16507053471200024472719939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11004702314133349648479959 16507053471200024472719939)
            ·
              refine ⟨24760580206800036709079909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16507053471200024472719939 24760580206800036709079909)
              ·
                refine ⟨4642608788775006882952483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24760580206800036709079909 4642608788775006882952483)
                ·
                  refine ⟨6963913183162510324428725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4642608788775006882952483 6963913183162510324428725)
                  ·
                    refine ⟨652866860921485342915193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6963913183162510324428725 652866860921485342915193)
                    ·
                      rfl

theorem cell23_3814361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 5].length) (baseStart_3814361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814361 prefixEnd_3814361 := by exact prefixLift 3814361
  have htrace : WordTrace (prefixWord ++ tailWord_3814361) baseStart_3814361 baseEnd_3814361 := by
    simpa [prefixWord, tailWord_3814361, baseEnd_3814361] using wordTrace_append hprefix tailTrace_3814361
  have hstable : (prefixWord ++ tailWord_3814361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814361).length < 2 ^ (prefixWord ++ tailWord_3814361).sum := by decide
  have hdescent : baseEnd_3814361 < baseStart_3814361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814401 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_3814401 : Nat := 118140960795 + 3814401 * 2 ^ 59
def prefixEnd_3814401 : Nat := 4983230072969 + 3 ^ 40 * 3814401 * 2
def baseEnd_3814401 : Nat := 1958621121990635872245395

theorem tailTrace_3814401 : CollatzResearch.WordTrace tailWord_3814401 prefixEnd_3814401 1958621121990635872245395 := by
  unfold tailWord_3814401
  simp only [CollatzResearch.WordTrace]
  refine ⟨139122633854084099671499057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92748422569389399780999371 139122633854084099671499057)
  ·
    refine ⟨104341975390563074753624293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139122633854084099671499057 104341975390563074753624293)
    ·
      refine ⟨19564120385730576516304555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104341975390563074753624293 19564120385730576516304555)
      ·
        refine ⟨29346180578595864774456833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19564120385730576516304555 29346180578595864774456833)
        ·
          refine ⟨22009635433946898580842625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29346180578595864774456833 22009635433946898580842625)
          ·
            refine ⟨16507226575460173935631969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22009635433946898580842625 16507226575460173935631969)
            ·
              refine ⟨12380419931595130451723977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16507226575460173935631969 12380419931595130451723977)
              ·
                refine ⟨9285314948696347838792983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12380419931595130451723977 9285314948696347838792983)
                ·
                  refine ⟨13927972423044521758189475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9285314948696347838792983 13927972423044521758189475)
                  ·
                    refine ⟨20891958634566782637284213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13927972423044521758189475 20891958634566782637284213)
                    ·
                      refine ⟨1958621121990635872245395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20891958634566782637284213 1958621121990635872245395)
                      ·
                        rfl

theorem cell23_3814401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_3814401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814401 prefixEnd_3814401 := by exact prefixLift 3814401
  have htrace : WordTrace (prefixWord ++ tailWord_3814401) baseStart_3814401 baseEnd_3814401 := by
    simpa [prefixWord, tailWord_3814401, baseEnd_3814401] using wordTrace_append hprefix tailTrace_3814401
  have hstable : (prefixWord ++ tailWord_3814401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814401).length < 2 ^ (prefixWord ++ tailWord_3814401).sum := by decide
  have hdescent : baseEnd_3814401 < baseStart_3814401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814408 : List Nat := [2, 1, 3, 2, 1, 4, 1, 3, 2, 4]
def baseStart_3814408 : Nat := 118140960795 + 3814408 * 2 ^ 59
def prefixEnd_3814408 : Nat := 4983230072969 + 3 ^ 40 * 3814408 * 2
def baseEnd_3814408 : Nat := 652874905451739114952621

theorem tailTrace_3814408 : CollatzResearch.WordTrace tailWord_3814408 prefixEnd_3814408 652874905451739114952621 := by
  unfold tailWord_3814408
  simp only [CollatzResearch.WordTrace]
  refine ⟨69561444582529369933501939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92748592776705826578002585 69561444582529369933501939)
  ·
    refine ⟨104342166873794054900252909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69561444582529369933501939 104342166873794054900252909)
    ·
      refine ⟨39128312577672770587594841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104342166873794054900252909 39128312577672770587594841)
      ·
        refine ⟨29346234433254577940696131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39128312577672770587594841 29346234433254577940696131)
        ·
          refine ⟨44019351649881866911044197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29346234433254577940696131 44019351649881866911044197)
          ·
            refine ⟨8253628434352850045820787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44019351649881866911044197 8253628434352850045820787)
            ·
              refine ⟨12380442651529275068731181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8253628434352850045820787 12380442651529275068731181)
              ·
                refine ⟨4642665994323478150774193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12380442651529275068731181 4642665994323478150774193)
                ·
                  refine ⟨3481999495742608613080645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4642665994323478150774193 3481999495742608613080645)
                  ·
                    refine ⟨652874905451739114952621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3481999495742608613080645 652874905451739114952621)
                    ·
                      rfl

theorem cell23_3814408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_3814408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814408 prefixEnd_3814408 := by exact prefixLift 3814408
  have htrace : WordTrace (prefixWord ++ tailWord_3814408) baseStart_3814408 baseEnd_3814408 := by
    simpa [prefixWord, tailWord_3814408, baseEnd_3814408] using wordTrace_append hprefix tailTrace_3814408
  have hstable : (prefixWord ++ tailWord_3814408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814408).length < 2 ^ (prefixWord ++ tailWord_3814408).sum := by decide
  have hdescent : baseEnd_3814408 < baseStart_3814408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814428 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_3814428 : Nat := 118140960795 + 3814428 * 2 ^ 59
def prefixEnd_3814428 : Nat := 4983230072969 + 3 ^ 40 * 3814428 * 2
def baseEnd_3814428 : Nat := 1958634985968307266607771

theorem tailTrace_3814428 : CollatzResearch.WordTrace tailWord_3814428 prefixEnd_3814428 1958634985968307266607771 := by
  unfold tailWord_3814428
  simp only [CollatzResearch.WordTrace]
  refine ⟨69561809312493141641365969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92749079083324188855154625 69561809312493141641365969)
  ·
    refine ⟨52171356984369856231024477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69561809312493141641365969 52171356984369856231024477)
    ·
      refine ⟨19564258869138696086634179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52171356984369856231024477 19564258869138696086634179)
      ·
        refine ⟨29346388303708044129951269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19564258869138696086634179 29346388303708044129951269)
        ·
          refine ⟨5502447806945258274365863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29346388303708044129951269 5502447806945258274365863)
          ·
            refine ⟨8253671710417887411548795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5502447806945258274365863 8253671710417887411548795)
            ·
              refine ⟨12380507565626831117323193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8253671710417887411548795 12380507565626831117323193)
              ·
                refine ⟨9285380674220123337992395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12380507565626831117323193 9285380674220123337992395)
                ·
                  refine ⟨13928071011330185006988593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9285380674220123337992395 13928071011330185006988593)
                  ·
                    refine ⟨10446053258497638755241445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13928071011330185006988593 10446053258497638755241445)
                    ·
                      refine ⟨1958634985968307266607771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10446053258497638755241445 1958634985968307266607771)
                      ·
                        rfl

theorem cell23_3814428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_3814428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814428 prefixEnd_3814428 := by exact prefixLift 3814428
  have htrace : WordTrace (prefixWord ++ tailWord_3814428) baseStart_3814428 baseEnd_3814428 := by
    simpa [prefixWord, tailWord_3814428, baseEnd_3814428] using wordTrace_append hprefix tailTrace_3814428
  have hstable : (prefixWord ++ tailWord_3814428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814428).length < 2 ^ (prefixWord ++ tailWord_3814428).sum := by decide
  have hdescent : baseEnd_3814428 < baseStart_3814428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814431 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 3]
def baseStart_3814431 : Nat := 118140960795 + 3814431 * 2 ^ 59
def prefixEnd_3814431 : Nat := 4983230072969 + 3 ^ 40 * 3814431 * 2
def baseEnd_3814431 : Nat := 1958636526410270754870257

theorem tailTrace_3814431 : CollatzResearch.WordTrace tailWord_3814431 prefixEnd_3814431 1958636526410270754870257 := by
  unfold tailWord_3814431
  simp only [CollatzResearch.WordTrace]
  refine ⟨139123728043975414795091147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92749152029316943196727431 139123728043975414795091147)
  ·
    refine ⟨208685592065963122192636721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139123728043975414795091147 208685592065963122192636721)
    ·
      refine ⟨156514194049472341644477541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208685592065963122192636721 156514194049472341644477541)
      ·
        refine ⟨29346411384276064058339539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156514194049472341644477541 29346411384276064058339539)
        ·
          refine ⟨44019617076414096087509309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29346411384276064058339539 44019617076414096087509309)
          ·
            refine ⟨16507356403655286032815991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44019617076414096087509309 16507356403655286032815991)
            ·
              refine ⟨24761034605482929049223987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16507356403655286032815991 24761034605482929049223987)
              ·
                refine ⟨37141551908224393573835981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24761034605482929049223987 37141551908224393573835981)
                ·
                  refine ⟨13928081965584147590188493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37141551908224393573835981 13928081965584147590188493)
                  ·
                    refine ⟨5223030737094055346320685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13928081965584147590188493 5223030737094055346320685)
                    ·
                      refine ⟨1958636526410270754870257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5223030737094055346320685 1958636526410270754870257)
                      ·
                        rfl

theorem cell23_3814431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_3814431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814431 prefixEnd_3814431 := by exact prefixLift 3814431
  have htrace : WordTrace (prefixWord ++ tailWord_3814431) baseStart_3814431 baseEnd_3814431 := by
    simpa [prefixWord, tailWord_3814431, baseEnd_3814431] using wordTrace_append hprefix tailTrace_3814431
  have hstable : (prefixWord ++ tailWord_3814431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814431).length < 2 ^ (prefixWord ++ tailWord_3814431).sum := by decide
  have hdescent : baseEnd_3814431 < baseStart_3814431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814432 : List Nat := [2, 1, 1, 7, 1, 1, 3, 1, 1, 1, 4]
def baseStart_3814432 : Nat := 118140960795 + 3814432 * 2 ^ 59
def prefixEnd_3814432 : Nat := 4983230072969 + 3 ^ 40 * 3814432 * 2
def baseEnd_3814432 : Nat := 1958637039890925250957753

theorem tailTrace_3814432 : CollatzResearch.WordTrace tailWord_3814432 prefixEnd_3814432 1958637039890925250957753 := by
  unfold tailWord_3814432
  simp only [CollatzResearch.WordTrace]
  refine ⟨69561882258485895982938775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92749176344647861310585033 69561882258485895982938775)
  ·
    refine ⟨104342823387728843974408163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69561882258485895982938775 104342823387728843974408163)
    ·
      refine ⟨156514235081593265961612245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104342823387728843974408163 156514235081593265961612245)
      ·
        refine ⟨3668302384724842170975287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 156514235081593265961612245 3668302384724842170975287)
        ·
          refine ⟨5502453577087263256462931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3668302384724842170975287 5502453577087263256462931)
          ·
            refine ⟨8253680365630894884694397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5502453577087263256462931 8253680365630894884694397)
            ·
              refine ⟨3095130137111585581760399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8253680365630894884694397 3095130137111585581760399)
              ·
                refine ⟨4642695205667378372640599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3095130137111585581760399 4642695205667378372640599)
                ·
                  refine ⟨6964042808501067558960899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4642695205667378372640599 6964042808501067558960899)
                  ·
                    refine ⟨10446064212751601338441349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6964042808501067558960899 10446064212751601338441349)
                    ·
                      refine ⟨1958637039890925250957753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10446064212751601338441349 1958637039890925250957753)
                      ·
                        rfl

theorem cell23_3814432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_3814432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814432 prefixEnd_3814432 := by exact prefixLift 3814432
  have htrace : WordTrace (prefixWord ++ tailWord_3814432) baseStart_3814432 baseEnd_3814432 := by
    simpa [prefixWord, tailWord_3814432, baseEnd_3814432] using wordTrace_append hprefix tailTrace_3814432
  have hstable : (prefixWord ++ tailWord_3814432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814432).length < 2 ^ (prefixWord ++ tailWord_3814432).sum := by decide
  have hdescent : baseEnd_3814432 < baseStart_3814432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814435 : List Nat := [1, 1, 1, 4, 3, 3, 3, 1, 1, 2, 3]
def baseStart_3814435 : Nat := 118140960795 + 3814435 * 2 ^ 59
def prefixEnd_3814435 : Nat := 4983230072969 + 3 ^ 40 * 3814435 * 2
def baseEnd_3814435 : Nat := 1958638580332888739220239

theorem tailTrace_3814435 : CollatzResearch.WordTrace tailWord_3814435 prefixEnd_3814435 1958638580332888739220239 := by
  unfold tailWord_3814435
  simp only [CollatzResearch.WordTrace]
  refine ⟨139123873935960923478236759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92749249290640615652157839 139123873935960923478236759)
  ·
    refine ⟨208685810903941385217355139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139123873935960923478236759 208685810903941385217355139)
    ·
      refine ⟨313028716355912077826032709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208685810903941385217355139 313028716355912077826032709)
      ·
        refine ⟨58692884316733514592381133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313028716355912077826032709 58692884316733514592381133)
        ·
          refine ⟨22009831618775067972142925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58692884316733514592381133 22009831618775067972142925)
          ·
            refine ⟨8253686857040650489553597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22009831618775067972142925 8253686857040650489553597)
            ·
              refine ⟨3095132571390243933582599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8253686857040650489553597 3095132571390243933582599)
              ·
                refine ⟨4642698857085365900373899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3095132571390243933582599 4642698857085365900373899)
                ·
                  refine ⟨6964048285628048850560849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4642698857085365900373899 6964048285628048850560849)
                  ·
                    refine ⟨5223036214221036637920637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6964048285628048850560849 5223036214221036637920637)
                    ·
                      refine ⟨1958638580332888739220239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5223036214221036637920637 1958638580332888739220239)
                      ·
                        rfl

theorem cell23_3814435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_3814435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814435 prefixEnd_3814435 := by exact prefixLift 3814435
  have htrace : WordTrace (prefixWord ++ tailWord_3814435) baseStart_3814435 baseEnd_3814435 := by
    simpa [prefixWord, tailWord_3814435, baseEnd_3814435] using wordTrace_append hprefix tailTrace_3814435
  have hstable : (prefixWord ++ tailWord_3814435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814435).length < 2 ^ (prefixWord ++ tailWord_3814435).sum := by decide
  have hdescent : baseEnd_3814435 < baseStart_3814435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814458 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2]
def baseStart_3814458 : Nat := 118140960795 + 3814458 * 2 ^ 59
def prefixEnd_3814458 : Nat := 4983230072969 + 3 ^ 40 * 3814458 * 2
def baseEnd_3814458 : Nat := 1958650390387942149232633

theorem tailTrace_3814458 : CollatzResearch.WordTrace tailWord_3814458 prefixEnd_3814458 1958650390387942149232633 := by
  unfold tailWord_3814458
  simp only [CollatzResearch.WordTrace]
  refine ⟨34781178203719399601581007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92749808543251732270882685 34781178203719399601581007)
  ·
    refine ⟨52171767305579099402371511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34781178203719399601581007 52171767305579099402371511)
    ·
      refine ⟨78257650958368649103557267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52171767305579099402371511 78257650958368649103557267)
      ·
        refine ⟨117386476437552973655335901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78257650958368649103557267 117386476437552973655335901)
        ·
          refine ⟨44019928664082365120750963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117386476437552973655335901 44019928664082365120750963)
          ·
            refine ⟨66029892996123547681126445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44019928664082365120750963 66029892996123547681126445)
            ·
              refine ⟨24761209873546330380422417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66029892996123547681126445 24761209873546330380422417)
              ·
                refine ⟨18570907405159747785316813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24761209873546330380422417 18570907405159747785316813)
                ·
                  refine ⟨6964090276934905419493805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18570907405159747785316813 6964090276934905419493805)
                  ·
                    refine ⟨2611533853850589532310177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6964090276934905419493805 2611533853850589532310177)
                    ·
                      refine ⟨1958650390387942149232633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2611533853850589532310177 1958650390387942149232633)
                      ·
                        rfl

theorem cell23_3814458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2].length) (baseStart_3814458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814458 prefixEnd_3814458 := by exact prefixLift 3814458
  have htrace : WordTrace (prefixWord ++ tailWord_3814458) baseStart_3814458 baseEnd_3814458 := by
    simpa [prefixWord, tailWord_3814458, baseEnd_3814458] using wordTrace_append hprefix tailTrace_3814458
  have hstable : (prefixWord ++ tailWord_3814458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814458).length < 2 ^ (prefixWord ++ tailWord_3814458).sum := by decide
  have hdescent : baseEnd_3814458 < baseStart_3814458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814465 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_3814465 : Nat := 118140960795 + 3814465 * 2 ^ 59
def prefixEnd_3814465 : Nat := 4983230072969 + 3 ^ 40 * 3814465 * 2
def baseEnd_3814465 : Nat := 1958653984752523621845101

theorem tailTrace_3814465 : CollatzResearch.WordTrace tailWord_3814465 prefixEnd_3814465 1958653984752523621845101 := by
  unfold tailWord_3814465
  simp only [CollatzResearch.WordTrace]
  refine ⟨139124968125852238601828849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92749978750568159067885899 139124968125852238601828849)
  ·
    refine ⟨104343726094389178951371637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139124968125852238601828849 104343726094389178951371637)
    ·
      refine ⟨9782224321348985526691091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104343726094389178951371637 9782224321348985526691091)
      ·
        refine ⟨14673336482023478290036637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9782224321348985526691091 14673336482023478290036637)
        ·
          refine ⟨5502501180758804358763739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14673336482023478290036637 5502501180758804358763739)
          ·
            refine ⟨8253751771138206538145609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5502501180758804358763739 8253751771138206538145609)
            ·
              refine ⟨6190313828353654903609207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8253751771138206538145609 6190313828353654903609207)
              ·
                refine ⟨9285470742530482355413811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6190313828353654903609207 9285470742530482355413811)
                ·
                  refine ⟨13928206113795723533120717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9285470742530482355413811 13928206113795723533120717)
                  ·
                    refine ⟨5223077292673396324920269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13928206113795723533120717 5223077292673396324920269)
                    ·
                      refine ⟨1958653984752523621845101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5223077292673396324920269 1958653984752523621845101)
                      ·
                        rfl

theorem cell23_3814465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_3814465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814465 prefixEnd_3814465 := by exact prefixLift 3814465
  have htrace : WordTrace (prefixWord ++ tailWord_3814465) baseStart_3814465 baseEnd_3814465 := by
    simpa [prefixWord, tailWord_3814465, baseEnd_3814465] using wordTrace_append hprefix tailTrace_3814465
  have hstable : (prefixWord ++ tailWord_3814465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814465).length < 2 ^ (prefixWord ++ tailWord_3814465).sum := by decide
  have hdescent : baseEnd_3814465 < baseStart_3814465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814486 : List Nat := [5, 2, 2, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_3814486 : Nat := 118140960795 + 3814486 * 2 ^ 59
def prefixEnd_3814486 : Nat := 4983230072969 + 3 ^ 40 * 3814486 * 2
def baseEnd_3814486 : Nat := 1958664767846268039682505

theorem tailTrace_3814486 : CollatzResearch.WordTrace tailWord_3814486 prefixEnd_3814486 1958664767846268039682505 := by
  unfold tailWord_3814486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8695358378673509949271457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92750489372517439458895541 8695358378673509949271457)
  ·
    refine ⟨6521518784005132461953593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8695358378673509949271457 6521518784005132461953593)
    ·
      refine ⟨4891139088003849346465195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6521518784005132461953593 4891139088003849346465195)
      ·
        refine ⟨7336708632005774019697793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4891139088003849346465195 7336708632005774019697793)
        ·
          refine ⟨5502531474004330514773345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7336708632005774019697793 5502531474004330514773345)
          ·
            refine ⟨4126898605503247886080009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5502531474004330514773345 4126898605503247886080009)
            ·
              refine ⟨3095173954127435914560007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4126898605503247886080009 3095173954127435914560007)
              ·
                refine ⟨4642760931191153871840011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3095173954127435914560007 4642760931191153871840011)
                ·
                  refine ⟨6964141396786730807760017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4642760931191153871840011 6964141396786730807760017)
                  ·
                    refine ⟨5223106047590048105820013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6964141396786730807760017 5223106047590048105820013)
                    ·
                      refine ⟨1958664767846268039682505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5223106047590048105820013 1958664767846268039682505)
                      ·
                        rfl

theorem cell23_3814486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_3814486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814486 prefixEnd_3814486 := by exact prefixLift 3814486
  have htrace : WordTrace (prefixWord ++ tailWord_3814486) baseStart_3814486 baseEnd_3814486 := by
    simpa [prefixWord, tailWord_3814486, baseEnd_3814486] using wordTrace_append hprefix tailTrace_3814486
  have hstable : (prefixWord ++ tailWord_3814486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814486).length < 2 ^ (prefixWord ++ tailWord_3814486).sum := by decide
  have hdescent : baseEnd_3814486 < baseStart_3814486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814488 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 1, 4, 2]
def baseStart_3814488 : Nat := 118140960795 + 3814488 * 2 ^ 59
def prefixEnd_3814488 : Nat := 4983230072969 + 3 ^ 40 * 3814488 * 2
def baseEnd_3814488 : Nat := 1958665794807577031857495

theorem tailTrace_3814488 : CollatzResearch.WordTrace tailWord_3814488 prefixEnd_3814488 1958665794807577031857495 := by
  unfold tailWord_3814488
  simp only [CollatzResearch.WordTrace]
  refine ⟨69562903502384456764958059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92750538003179275686610745 69562903502384456764958059)
  ·
    refine ⟨104344355253576685147437089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69562903502384456764958059 104344355253576685147437089)
    ·
      refine ⟨78258266440182513860577817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104344355253576685147437089 78258266440182513860577817)
      ·
        refine ⟨58693699830136885395433363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78258266440182513860577817 58693699830136885395433363)
        ·
          refine ⟨88040549745205328093150045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58693699830136885395433363 88040549745205328093150045)
          ·
            refine ⟨33015206154451998034931267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88040549745205328093150045 33015206154451998034931267)
            ·
              refine ⟨49522809231677997052396901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33015206154451998034931267 49522809231677997052396901)
              ·
                refine ⟨9285526730939624447324419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49522809231677997052396901 9285526730939624447324419)
                ·
                  refine ⟨13928290096409436670986629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9285526730939624447324419 13928290096409436670986629)
                  ·
                    refine ⟨2611554393076769375809993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13928290096409436670986629 2611554393076769375809993)
                    ·
                      refine ⟨1958665794807577031857495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2611554393076769375809993 1958665794807577031857495)
                      ·
                        rfl

theorem cell23_3814488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_3814488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814488 prefixEnd_3814488 := by exact prefixLift 3814488
  have htrace : WordTrace (prefixWord ++ tailWord_3814488) baseStart_3814488 baseEnd_3814488 := by
    simpa [prefixWord, tailWord_3814488, baseEnd_3814488] using wordTrace_append hprefix tailTrace_3814488
  have hstable : (prefixWord ++ tailWord_3814488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814488).length < 2 ^ (prefixWord ++ tailWord_3814488).sum := by decide
  have hdescent : baseEnd_3814488 < baseStart_3814488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814498 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_3814498 : Nat := 118140960795 + 3814498 * 2 ^ 59
def prefixEnd_3814498 : Nat := 4983230072969 + 3 ^ 40 * 3814498 * 2
def baseEnd_3814498 : Nat := 652890309871373997577483

theorem tailTrace_3814498 : CollatzResearch.WordTrace tailWord_3814498 prefixEnd_3814498 652890309871373997577483 := by
  unfold tailWord_3814498
  simp only [CollatzResearch.WordTrace]
  refine ⟨34781542933683171309445037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92750781156488456825186765 34781542933683171309445037)
  ·
    refine ⟨13043078600131189241041889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34781542933683171309445037 13043078600131189241041889)
    ·
      refine ⟨9782308950098391930781417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13043078600131189241041889 9782308950098391930781417)
      ·
        refine ⟨7336731712573793948086063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9782308950098391930781417 7336731712573793948086063)
        ·
          refine ⟨11005097568860690922129095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7336731712573793948086063 11005097568860690922129095)
          ·
            refine ⟨16507646353291036383193643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11005097568860690922129095 16507646353291036383193643)
            ·
              refine ⟨24761469529936554574790465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16507646353291036383193643 24761469529936554574790465)
              ·
                refine ⟨18571102147452415931092849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24761469529936554574790465 18571102147452415931092849)
                ·
                  refine ⟨13928326610589311948319637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18571102147452415931092849 13928326610589311948319637)
                  ·
                    refine ⟨652890309871373997577483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13928326610589311948319637 652890309871373997577483)
                    ·
                      rfl

theorem cell23_3814498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_3814498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814498 prefixEnd_3814498 := by exact prefixLift 3814498
  have htrace : WordTrace (prefixWord ++ tailWord_3814498) baseStart_3814498 baseEnd_3814498 := by
    simpa [prefixWord, tailWord_3814498, baseEnd_3814498] using wordTrace_append hprefix tailTrace_3814498
  have hstable : (prefixWord ++ tailWord_3814498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814498).length < 2 ^ (prefixWord ++ tailWord_3814498).sum := by decide
  have hdescent : baseEnd_3814498 < baseStart_3814498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814501 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 4, 2, 4]
def baseStart_3814501 : Nat := 118140960795 + 3814501 * 2 ^ 59
def prefixEnd_3814501 : Nat := 4983230072969 + 3 ^ 40 * 3814501 * 2
def baseEnd_3814501 : Nat := 1958672470056085480994935

theorem tailTrace_3814501 : CollatzResearch.WordTrace tailWord_3814501 prefixEnd_3814501 1958672470056085480994935 := by
  unfold tailWord_3814501
  simp only [CollatzResearch.WordTrace]
  refine ⟨139126281153721816750139357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92750854102481211166759571 139126281153721816750139357)
  ·
    refine ⟨52172355432645681281302259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139126281153721816750139357 52172355432645681281302259)
    ·
      refine ⟨78258533148968521921953389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52172355432645681281302259 78258533148968521921953389)
      ·
        refine ⟨29346949930863195720732521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78258533148968521921953389 29346949930863195720732521)
        ·
          refine ⟨22010212448147396790549391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29346949930863195720732521 22010212448147396790549391)
          ·
            refine ⟨33015318672221095185824087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22010212448147396790549391 33015318672221095185824087)
            ·
              refine ⟨49522978008331642778736131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33015318672221095185824087 49522978008331642778736131)
              ·
                refine ⟨74284467012497464168104197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49522978008331642778736131 74284467012497464168104197)
                ·
                  refine ⟨13928337564843274531519537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74284467012497464168104197 13928337564843274531519537)
                  ·
                    refine ⟨10446253173632455898639653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13928337564843274531519537 10446253173632455898639653)
                    ·
                      refine ⟨1958672470056085480994935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10446253173632455898639653 1958672470056085480994935)
                      ·
                        rfl

theorem cell23_3814501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_3814501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814501 prefixEnd_3814501 := by exact prefixLift 3814501
  have htrace : WordTrace (prefixWord ++ tailWord_3814501) baseStart_3814501 baseEnd_3814501 := by
    simpa [prefixWord, tailWord_3814501, baseEnd_3814501] using wordTrace_append hprefix tailTrace_3814501
  have hstable : (prefixWord ++ tailWord_3814501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814501).length < 2 ^ (prefixWord ++ tailWord_3814501).sum := by decide
  have hdescent : baseEnd_3814501 < baseStart_3814501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814505 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 4, 2, 2]
def baseStart_3814505 : Nat := 118140960795 + 3814505 * 2 ^ 59
def prefixEnd_3814505 : Nat := 4983230072969 + 3 ^ 40 * 3814505 * 2
def baseEnd_3814505 : Nat := 1958674523978703465344917

theorem tailTrace_3814505 : CollatzResearch.WordTrace tailWord_3814505 prefixEnd_3814505 1958674523978703465344917 := by
  unfold tailWord_3814505
  simp only [CollatzResearch.WordTrace]
  refine ⟨139126427045707325433284969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92750951363804883622189979 139126427045707325433284969)
  ·
    refine ⟨104344820284280494074963727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139126427045707325433284969 104344820284280494074963727)
    ·
      refine ⟨156517230426420741112445591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104344820284280494074963727 156517230426420741112445591)
      ·
        refine ⟨234775845639631111668668387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156517230426420741112445591 234775845639631111668668387)
        ·
          refine ⟨352163768459446667503002581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234775845639631111668668387 352163768459446667503002581)
          ·
            refine ⟨8253838323268281269601623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 352163768459446667503002581 8253838323268281269601623)
            ·
              refine ⟨12380757484902421904402435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8253838323268281269601623 12380757484902421904402435)
              ·
                refine ⟨18571136227353632856603653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12380757484902421904402435 18571136227353632856603653)
                ·
                  refine ⟨3482088042628806160613185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18571136227353632856603653 3482088042628806160613185)
                  ·
                    refine ⟨2611566031971604620459889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3482088042628806160613185 2611566031971604620459889)
                    ·
                      refine ⟨1958674523978703465344917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2611566031971604620459889 1958674523978703465344917)
                      ·
                        rfl

theorem cell23_3814505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 2, 2].length) (baseStart_3814505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814505 prefixEnd_3814505 := by exact prefixLift 3814505
  have htrace : WordTrace (prefixWord ++ tailWord_3814505) baseStart_3814505 baseEnd_3814505 := by
    simpa [prefixWord, tailWord_3814505, baseEnd_3814505] using wordTrace_append hprefix tailTrace_3814505
  have hstable : (prefixWord ++ tailWord_3814505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814505).length < 2 ^ (prefixWord ++ tailWord_3814505).sum := by decide
  have hdescent : baseEnd_3814505 < baseStart_3814505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814511 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 7]
def baseStart_3814511 : Nat := 118140960795 + 3814511 * 2 ^ 59
def prefixEnd_3814511 : Nat := 4983230072969 + 3 ^ 40 * 3814511 * 2
def baseEnd_3814511 : Nat := 217630844984736715763321

theorem tailTrace_3814511 : CollatzResearch.WordTrace tailWord_3814511 prefixEnd_3814511 217630844984736715763321 := by
  unfold tailWord_3814511
  simp only [CollatzResearch.WordTrace]
  refine ⟨139126645883685588458003387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92751097255790392305335591 139126645883685588458003387)
  ·
    refine ⟨208689968825528382687005081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139126645883685588458003387 208689968825528382687005081)
    ·
      refine ⟨156517476619146287015253811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208689968825528382687005081 156517476619146287015253811)
      ·
        refine ⟨234776214928719430522880717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156517476619146287015253811 234776214928719430522880717)
        ·
          refine ⟨88041080598269786446080269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234776214928719430522880717 88041080598269786446080269)
          ·
            refine ⟨33015405224351169917280101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88041080598269786446080269 33015405224351169917280101)
            ·
              refine ⟨6190388479565844359490019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33015405224351169917280101 6190388479565844359490019)
              ·
                refine ⟨9285582719348766539235029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6190388479565844359490019 9285582719348766539235029)
                ·
                  refine ⟨217630844984736715763321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9285582719348766539235029 217630844984736715763321)
                  ·
                    rfl

theorem cell23_3814511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 7].length) (baseStart_3814511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814511 prefixEnd_3814511 := by exact prefixLift 3814511
  have htrace : WordTrace (prefixWord ++ tailWord_3814511) baseStart_3814511 baseEnd_3814511 := by
    simpa [prefixWord, tailWord_3814511, baseEnd_3814511] using wordTrace_append hprefix tailTrace_3814511
  have hstable : (prefixWord ++ tailWord_3814511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814511).length < 2 ^ (prefixWord ++ tailWord_3814511).sum := by decide
  have hdescent : baseEnd_3814511 < baseStart_3814511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814518 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3814518 : Nat := 118140960795 + 3814518 * 2 ^ 59
def prefixEnd_3814518 : Nat := 4983230072969 + 3 ^ 40 * 3814518 * 2
def baseEnd_3814518 : Nat := 1958681199227211914482357

theorem tailTrace_3814518 : CollatzResearch.WordTrace tailWord_3814518 prefixEnd_3814518 1958681199227211914482357 := by
  unfold tailWord_3814518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8695431324666264290844263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92751267463106819102338805 8695431324666264290844263)
  ·
    refine ⟨13043146986999396436266395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8695431324666264290844263 13043146986999396436266395)
    ·
      refine ⟨19564720480499094654399593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13043146986999396436266395 19564720480499094654399593)
      ·
        refine ⟨14673540360374320990799695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19564720480499094654399593 14673540360374320990799695)
        ·
          refine ⟨22010310540561481486199543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14673540360374320990799695 22010310540561481486199543)
          ·
            refine ⟨33015465810842222229299315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22010310540561481486199543 33015465810842222229299315)
            ·
              refine ⟨49523198716263333343948973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33015465810842222229299315 49523198716263333343948973)
              ·
                refine ⟨18571199518598750003980865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49523198716263333343948973 18571199518598750003980865)
                ·
                  refine ⟨13928399638949062502985649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18571199518598750003980865 13928399638949062502985649)
                  ·
                    refine ⟨10446299729211796877239237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13928399638949062502985649 10446299729211796877239237)
                    ·
                      refine ⟨1958681199227211914482357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10446299729211796877239237 1958681199227211914482357)
                      ·
                        rfl

theorem cell23_3814518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3814518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814518 prefixEnd_3814518 := by exact prefixLift 3814518
  have htrace : WordTrace (prefixWord ++ tailWord_3814518) baseStart_3814518 baseEnd_3814518 := by
    simpa [prefixWord, tailWord_3814518, baseEnd_3814518] using wordTrace_append hprefix tailTrace_3814518
  have hstable : (prefixWord ++ tailWord_3814518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814518).length < 2 ^ (prefixWord ++ tailWord_3814518).sum := by decide
  have hdescent : baseEnd_3814518 < baseStart_3814518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814562 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 7]
def baseStart_3814562 : Nat := 118140960795 + 3814562 * 2 ^ 59
def prefixEnd_3814562 : Nat := 4983230072969 + 3 ^ 40 * 3814562 * 2
def baseEnd_3814562 : Nat := 217633754708445526925795

theorem tailTrace_3814562 : CollatzResearch.WordTrace tailWord_3814562 prefixEnd_3814562 217633754708445526925795 := by
  unfold tailWord_3814562
  simp only [CollatzResearch.WordTrace]
  refine ⟨34782126501625206042027485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92752337337667216112073293 34782126501625206042027485)
  ·
    refine ⟨13043297438109452265760307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34782126501625206042027485 13043297438109452265760307)
    ·
      refine ⟨19564946157164178398640461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13043297438109452265760307 19564946157164178398640461)
      ·
        refine ⟨7336854808936566899490173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19564946157164178398640461 7336854808936566899490173)
        ·
          refine ⟨2751320553351212587308815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7336854808936566899490173 2751320553351212587308815)
          ·
            refine ⟨4126980830026818880963223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2751320553351212587308815 4126980830026818880963223)
            ·
              refine ⟨6190471245040228321444835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4126980830026818880963223 6190471245040228321444835)
              ·
                refine ⟨9285706867560342482167253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6190471245040228321444835 9285706867560342482167253)
                ·
                  refine ⟨217633754708445526925795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9285706867560342482167253 217633754708445526925795)
                  ·
                    rfl

theorem cell23_3814562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_3814562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814562 prefixEnd_3814562 := by exact prefixLift 3814562
  have htrace : WordTrace (prefixWord ++ tailWord_3814562) baseStart_3814562 baseEnd_3814562 := by
    simpa [prefixWord, tailWord_3814562, baseEnd_3814562] using wordTrace_append hprefix tailTrace_3814562
  have hstable : (prefixWord ++ tailWord_3814562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814562).length < 2 ^ (prefixWord ++ tailWord_3814562).sum := by decide
  have hdescent : baseEnd_3814562 < baseStart_3814562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814573 : List Nat := [1, 5, 2, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_3814573 : Nat := 118140960795 + 3814573 * 2 ^ 59
def prefixEnd_3814573 : Nat := 4983230072969 + 3 ^ 40 * 3814573 * 2
def baseEnd_3814573 : Nat := 1958709440663209199294605

theorem tailTrace_3814573 : CollatzResearch.WordTrace tailWord_3814573 prefixEnd_3814573 1958709440663209199294605 := by
  unfold tailWord_3814573
  simp only [CollatzResearch.WordTrace]
  refine ⟨139128907209460973046760373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92752604806307315364506915 139128907209460973046760373)
  ·
    refine ⟨13043335050886966223133785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139128907209460973046760373 13043335050886966223133785)
    ·
      refine ⟨9782501288165224667350339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13043335050886966223133785 9782501288165224667350339)
      ·
        refine ⟨14673751932247837001025509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9782501288165224667350339 14673751932247837001025509)
        ·
          refine ⟨2751328487296469437692283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14673751932247837001025509 2751328487296469437692283)
          ·
            refine ⟨4126992730944704156538425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2751328487296469437692283 4126992730944704156538425)
            ·
              refine ⟨3095244548208528117403819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4126992730944704156538425 3095244548208528117403819)
              ·
                refine ⟨4642866822312792176105729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3095244548208528117403819 4642866822312792176105729)
                ·
                  refine ⟨3482150116734594132079297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4642866822312792176105729 3482150116734594132079297)
                  ·
                    refine ⟨2611612587550945599059473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3482150116734594132079297 2611612587550945599059473)
                    ·
                      refine ⟨1958709440663209199294605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2611612587550945599059473 1958709440663209199294605)
                      ·
                        rfl

theorem cell23_3814573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_3814573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814573 prefixEnd_3814573 := by exact prefixLift 3814573
  have htrace : WordTrace (prefixWord ++ tailWord_3814573) baseStart_3814573 baseEnd_3814573 := by
    simpa [prefixWord, tailWord_3814573, baseEnd_3814573] using wordTrace_append hprefix tailTrace_3814573
  have hstable : (prefixWord ++ tailWord_3814573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814573).length < 2 ^ (prefixWord ++ tailWord_3814573).sum := by decide
  have hdescent : baseEnd_3814573 < baseStart_3814573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814591 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 4]
def baseStart_3814591 : Nat := 118140960795 + 3814591 * 2 ^ 59
def prefixEnd_3814591 : Nat := 4983230072969 + 3 ^ 40 * 3814591 * 2
def baseEnd_3814591 : Nat := 1958718683314990128869521

theorem tailTrace_3814591 : CollatzResearch.WordTrace tailWord_3814591 prefixEnd_3814591 1958718683314990128869521 := by
  unfold tailWord_3814591
  simp only [CollatzResearch.WordTrace]
  refine ⟨139129563723395762120915627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92753042482263841413943751 139129563723395762120915627)
  ·
    refine ⟨208694345585093643181373441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139129563723395762120915627 208694345585093643181373441)
    ·
      refine ⟨156520759188820232386030081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208694345585093643181373441 156520759188820232386030081)
      ·
        refine ⟨117390569391615174289522561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156520759188820232386030081 117390569391615174289522561)
        ·
          refine ⟨88042927043711380717141921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117390569391615174289522561 88042927043711380717141921)
          ·
            refine ⟨66032195282783535537856441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88042927043711380717141921 66032195282783535537856441)
            ·
              refine ⟨49524146462087651653392331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66032195282783535537856441 49524146462087651653392331)
              ·
                refine ⟨74286219693131477480088497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49524146462087651653392331 74286219693131477480088497)
                ·
                  refine ⟨55714664769848608110066373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74286219693131477480088497 55714664769848608110066373)
                  ·
                    refine ⟨10446499644346614020637445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55714664769848608110066373 10446499644346614020637445)
                    ·
                      refine ⟨1958718683314990128869521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10446499644346614020637445 1958718683314990128869521)
                      ·
                        rfl

theorem cell23_3814591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_3814591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814591 prefixEnd_3814591 := by exact prefixLift 3814591
  have htrace : WordTrace (prefixWord ++ tailWord_3814591) baseStart_3814591 baseEnd_3814591 := by
    simpa [prefixWord, tailWord_3814591, baseEnd_3814591] using wordTrace_append hprefix tailTrace_3814591
  have hstable : (prefixWord ++ tailWord_3814591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814591).length < 2 ^ (prefixWord ++ tailWord_3814591).sum := by decide
  have hdescent : baseEnd_3814591 < baseStart_3814591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814641 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 7]
def baseStart_3814641 : Nat := 118140960795 + 3814641 * 2 ^ 59
def prefixEnd_3814641 : Nat := 4983230072969 + 3 ^ 40 * 3814641 * 2
def baseEnd_3814641 : Nat := 1958744357347714933244291

theorem tailTrace_3814641 : CollatzResearch.WordTrace tailWord_3814641 prefixEnd_3814641 1958744357347714933244291 := by
  unfold tailWord_3814641
  simp only [CollatzResearch.WordTrace]
  refine ⟨139131387373214620660235777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92754258248809747106823851 139131387373214620660235777)
  ·
    refine ⟨104348540529910965495176833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139131387373214620660235777 104348540529910965495176833)
    ·
      refine ⟨78261405397433224121382625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104348540529910965495176833 78261405397433224121382625)
      ·
        refine ⟨58696054048074918091036969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78261405397433224121382625 58696054048074918091036969)
        ·
          refine ⟨44022040536056188568277727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58696054048074918091036969 44022040536056188568277727)
          ·
            refine ⟨66033060804084282852416591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44022040536056188568277727 66033060804084282852416591)
            ·
              refine ⟨99049591206126424278624887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66033060804084282852416591 99049591206126424278624887)
              ·
                refine ⟨148574386809189636417937331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99049591206126424278624887 148574386809189636417937331)
                ·
                  refine ⟨222861580213784454626905997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148574386809189636417937331 222861580213784454626905997)
                  ·
                    refine ⟨83573092580169170485089749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 222861580213784454626905997 83573092580169170485089749)
                    ·
                      refine ⟨1958744357347714933244291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83573092580169170485089749 1958744357347714933244291)
                      ·
                        rfl

theorem cell23_3814641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_3814641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814641 prefixEnd_3814641 := by exact prefixLift 3814641
  have htrace : WordTrace (prefixWord ++ tailWord_3814641) baseStart_3814641 baseEnd_3814641 := by
    simpa [prefixWord, tailWord_3814641, baseEnd_3814641] using wordTrace_append hprefix tailTrace_3814641
  have hstable : (prefixWord ++ tailWord_3814641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814641).length < 2 ^ (prefixWord ++ tailWord_3814641).sum := by decide
  have hdescent : baseEnd_3814641 < baseStart_3814641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814655 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 1, 5, 2]
def baseStart_3814655 : Nat := 118140960795 + 3814655 * 2 ^ 59
def prefixEnd_3814655 : Nat := 4983230072969 + 3 ^ 40 * 3814655 * 2
def baseEnd_3814655 : Nat := 1958751546076877878469227

theorem tailTrace_3814655 : CollatzResearch.WordTrace tailWord_3814655 prefixEnd_3814655 1958751546076877878469227 := by
  unfold tailWord_3814655
  simp only [CollatzResearch.WordTrace]
  refine ⟨139131897995163901051245419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92754598663442600700830279 139131897995163901051245419)
  ·
    refine ⟨208697846992745851576868129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139131897995163901051245419 208697846992745851576868129)
    ·
      refine ⟨156523385244559388682651097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208697846992745851576868129 156523385244559388682651097)
      ·
        refine ⟨117392538933419541511988323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156523385244559388682651097 117392538933419541511988323)
        ·
          refine ⟨176088808400129312267982485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117392538933419541511988323 176088808400129312267982485)
          ·
            refine ⟨8254162893756061512561679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 176088808400129312267982485 8254162893756061512561679)
            ·
              refine ⟨12381244340634092268842519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8254162893756061512561679 12381244340634092268842519)
              ·
                refine ⟨18571866510951138403263779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12381244340634092268842519 18571866510951138403263779)
                ·
                  refine ⟨27857799766426707604895669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18571866510951138403263779 27857799766426707604895669)
                  ·
                    refine ⟨2611668728102503837958969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27857799766426707604895669 2611668728102503837958969)
                    ·
                      refine ⟨1958751546076877878469227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2611668728102503837958969 1958751546076877878469227)
                      ·
                        rfl

theorem cell23_3814655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 5, 2].length) (baseStart_3814655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814655 prefixEnd_3814655 := by exact prefixLift 3814655
  have htrace : WordTrace (prefixWord ++ tailWord_3814655) baseStart_3814655 baseEnd_3814655 := by
    simpa [prefixWord, tailWord_3814655, baseEnd_3814655] using wordTrace_append hprefix tailTrace_3814655
  have hstable : (prefixWord ++ tailWord_3814655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814655).length < 2 ^ (prefixWord ++ tailWord_3814655).sum := by decide
  have hdescent : baseEnd_3814655 < baseStart_3814655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814713 : List Nat := [1, 2, 1, 6, 3, 1, 1, 3, 1, 1, 3]
def baseStart_3814713 : Nat := 118140960795 + 3814713 * 2 ^ 59
def prefixEnd_3814713 : Nat := 4983230072969 + 3 ^ 40 * 3814713 * 2
def baseEnd_3814713 : Nat := 1958781327954838651543961

theorem tailTrace_3814713 : CollatzResearch.WordTrace tailWord_3814713 prefixEnd_3814713 1958781327954838651543961 := by
  unfold tailWord_3814713
  simp only [CollatzResearch.WordTrace]
  refine ⟨139134013428953776956856793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92756008952635851304571195 139134013428953776956856793)
  ·
    refine ⟨104350510071715332717642595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139134013428953776956856793 104350510071715332717642595)
    ·
      refine ⟨156525765107572999076463893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104350510071715332717642595 156525765107572999076463893)
      ·
        refine ⟨7337145239417484331709245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 156525765107572999076463893 7337145239417484331709245)
        ·
          refine ⟨2751429464781556624390967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7337145239417484331709245 2751429464781556624390967)
          ·
            refine ⟨4127144197172334936586451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2751429464781556624390967 4127144197172334936586451)
            ·
              refine ⟨6190716295758502404879677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4127144197172334936586451 6190716295758502404879677)
              ·
                refine ⟨2321518610909438401829879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6190716295758502404879677 2321518610909438401829879)
                ·
                  refine ⟨3482277916364157602744819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2321518610909438401829879 3482277916364157602744819)
                  ·
                    refine ⟨5223416874546236404117229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3482277916364157602744819 5223416874546236404117229)
                    ·
                      refine ⟨1958781327954838651543961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5223416874546236404117229 1958781327954838651543961)
                      ·
                        rfl

theorem cell23_3814713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_3814713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814713 prefixEnd_3814713 := by exact prefixLift 3814713
  have htrace : WordTrace (prefixWord ++ tailWord_3814713) baseStart_3814713 baseEnd_3814713 := by
    simpa [prefixWord, tailWord_3814713, baseEnd_3814713] using wordTrace_append hprefix tailTrace_3814713
  have hstable : (prefixWord ++ tailWord_3814713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814713).length < 2 ^ (prefixWord ++ tailWord_3814713).sum := by decide
  have hdescent : baseEnd_3814713 < baseStart_3814713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814736 : List Nat := [2, 1, 1, 1, 1, 5, 5, 2, 1, 2, 2]
def baseStart_3814736 : Nat := 118140960795 + 3814736 * 2 ^ 59
def prefixEnd_3814736 : Nat := 4983230072969 + 3 ^ 40 * 3814736 * 2
def baseEnd_3814736 : Nat := 1958793138009892061556355

theorem tailTrace_3814736 : CollatzResearch.WordTrace tailWord_3814736 prefixEnd_3814736 1958793138009892061556355 := by
  unfold tailWord_3814736
  simp only [CollatzResearch.WordTrace]
  refine ⟨69567426153935225942472031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92756568205246967923296041 69567426153935225942472031)
  ·
    refine ⟨104351139230902838913708047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69567426153935225942472031 104351139230902838913708047)
    ·
      refine ⟨156526708846354258370562071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104351139230902838913708047 156526708846354258370562071)
      ·
        refine ⟨234790063269531387555843107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156526708846354258370562071 234790063269531387555843107)
        ·
          refine ⟨352185094904297081333764661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234790063269531387555843107 352185094904297081333764661)
          ·
            refine ⟨33017352647277851375040437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 352185094904297081333764661 33017352647277851375040437)
            ·
              refine ⟨3095376810682298566410041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33017352647277851375040437 3095376810682298566410041)
              ·
                refine ⟨2321532608011723924807531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3095376810682298566410041 2321532608011723924807531)
                ·
                  refine ⟨3482298912017585887211297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2321532608011723924807531 3482298912017585887211297)
                  ·
                    refine ⟨2611724184013189415408473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3482298912017585887211297 2611724184013189415408473)
                    ·
                      refine ⟨1958793138009892061556355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2611724184013189415408473 1958793138009892061556355)
                      ·
                        rfl

theorem cell23_3814736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 1, 2, 2].length) (baseStart_3814736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814736 prefixEnd_3814736 := by exact prefixLift 3814736
  have htrace : WordTrace (prefixWord ++ tailWord_3814736) baseStart_3814736 baseEnd_3814736 := by
    simpa [prefixWord, tailWord_3814736, baseEnd_3814736] using wordTrace_append hprefix tailTrace_3814736
  have hstable : (prefixWord ++ tailWord_3814736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814736).length < 2 ^ (prefixWord ++ tailWord_3814736).sum := by decide
  have hdescent : baseEnd_3814736 < baseStart_3814736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814738 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 2, 7]
def baseStart_3814738 : Nat := 118140960795 + 3814738 * 2 ^ 59
def prefixEnd_3814738 : Nat := 4983230072969 + 3 ^ 40 * 3814738 * 2
def baseEnd_3814738 : Nat := 652931388323733684577115

theorem tailTrace_3814738 : CollatzResearch.WordTrace tailWord_3814738 prefixEnd_3814738 652931388323733684577115 := by
  unfold tailWord_3814738
  simp only [CollatzResearch.WordTrace]
  refine ⟨34783731313465801556629217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92756616835908804151011245 34783731313465801556629217)
  ·
    refine ⟨26087798485099351167471913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34783731313465801556629217 26087798485099351167471913)
    ·
      refine ⟨19565848863824513375603935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26087798485099351167471913 19565848863824513375603935)
      ·
        refine ⟨29348773295736770063405903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19565848863824513375603935 29348773295736770063405903)
        ·
          refine ⟨44023159943605155095108855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29348773295736770063405903 44023159943605155095108855)
          ·
            refine ⟨66034739915407732642663283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44023159943605155095108855 66034739915407732642663283)
            ·
              refine ⟨99052109873111598963994925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66034739915407732642663283 99052109873111598963994925)
              ·
                refine ⟨37144541202416849611498097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99052109873111598963994925 37144541202416849611498097)
                ·
                  refine ⟨27858405901812637208623573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37144541202416849611498097 27858405901812637208623573)
                  ·
                    refine ⟨652931388323733684577115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27858405901812637208623573 652931388323733684577115)
                    ·
                      rfl

theorem cell23_3814738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_3814738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814738 prefixEnd_3814738 := by exact prefixLift 3814738
  have htrace : WordTrace (prefixWord ++ tailWord_3814738) baseStart_3814738 baseEnd_3814738 := by
    simpa [prefixWord, tailWord_3814738, baseEnd_3814738] using wordTrace_append hprefix tailTrace_3814738
  have hstable : (prefixWord ++ tailWord_3814738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814738).length < 2 ^ (prefixWord ++ tailWord_3814738).sum := by decide
  have hdescent : baseEnd_3814738 < baseStart_3814738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814779 : List Nat := [1, 1, 1, 1, 1, 6, 5, 1, 1, 3, 2]
def baseStart_3814779 : Nat := 118140960795 + 3814779 * 2 ^ 59
def prefixEnd_3814779 : Nat := 4983230072969 + 3 ^ 40 * 3814779 * 2
def baseEnd_3814779 : Nat := 1958815217678035393318657

theorem tailTrace_3814779 : CollatzResearch.WordTrace tailWord_3814779 prefixEnd_3814779 1958815217678035393318657 := by
  unfold tailWord_3814779
  simp only [CollatzResearch.WordTrace]
  refine ⟨139136420646714670228759391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92757613764476446819172927 139136420646714670228759391)
  ·
    refine ⟨208704630970072005343139087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139136420646714670228759391 208704630970072005343139087)
    ·
      refine ⟨313056946455108008014708631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208704630970072005343139087 313056946455108008014708631)
      ·
        refine ⟨469585419682662012022062947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313056946455108008014708631 469585419682662012022062947)
        ·
          refine ⟨704378129523993018033094421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469585419682662012022062947 704378129523993018033094421)
          ·
            refine ⟨33017724821437172720301301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 704378129523993018033094421 33017724821437172720301301)
            ·
              refine ⟨3095411702009734942528247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33017724821437172720301301 3095411702009734942528247)
              ·
                refine ⟨4643117553014602413792371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3095411702009734942528247 4643117553014602413792371)
                ·
                  refine ⟨6964676329521903620688557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4643117553014602413792371 6964676329521903620688557)
                  ·
                    refine ⟨2611753623570713857758209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6964676329521903620688557 2611753623570713857758209)
                    ·
                      refine ⟨1958815217678035393318657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2611753623570713857758209 1958815217678035393318657)
                      ·
                        rfl

theorem cell23_3814779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 1, 3, 2].length) (baseStart_3814779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814779 prefixEnd_3814779 := by exact prefixLift 3814779
  have htrace : WordTrace (prefixWord ++ tailWord_3814779) baseStart_3814779 baseEnd_3814779 := by
    simpa [prefixWord, tailWord_3814779, baseEnd_3814779] using wordTrace_append hprefix tailTrace_3814779
  have hstable : (prefixWord ++ tailWord_3814779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814779).length < 2 ^ (prefixWord ++ tailWord_3814779).sum := by decide
  have hdescent : baseEnd_3814779 < baseStart_3814779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814786 : List Nat := [3, 4, 2, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_3814786 : Nat := 118140960795 + 3814786 * 2 ^ 59
def prefixEnd_3814786 : Nat := 4983230072969 + 3 ^ 40 * 3814786 * 2
def baseEnd_3814786 : Nat := 1958818812042616865931125

theorem tailTrace_3814786 : CollatzResearch.WordTrace tailWord_3814786 prefixEnd_3814786 1958818812042616865931125 := by
  unfold tailWord_3814786
  simp only [CollatzResearch.WordTrace]
  refine ⟨34784168989422327606066053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92757783971792873616176141 34784168989422327606066053)
  ·
    refine ⟨6522031685516686426137385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34784168989422327606066053 6522031685516686426137385)
    ·
      refine ⟨4891523764137514819603039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6522031685516686426137385 4891523764137514819603039)
      ·
        refine ⟨7337285646206272229404559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4891523764137514819603039 7337285646206272229404559)
        ·
          refine ⟨11005928469309408344106839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7337285646206272229404559 11005928469309408344106839)
          ·
            refine ⟨16508892703964112516160259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11005928469309408344106839 16508892703964112516160259)
            ·
              refine ⟨24763339055946168774240389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16508892703964112516160259 24763339055946168774240389)
              ·
                refine ⟨4643126072989906645170073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24763339055946168774240389 4643126072989906645170073)
                ·
                  refine ⟨3482344554742429983877555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4643126072989906645170073 3482344554742429983877555)
                  ·
                    refine ⟨5223516832113644975816333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3482344554742429983877555 5223516832113644975816333)
                    ·
                      refine ⟨1958818812042616865931125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5223516832113644975816333 1958818812042616865931125)
                      ·
                        rfl

theorem cell23_3814786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_3814786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814786 prefixEnd_3814786 := by exact prefixLift 3814786
  have htrace : WordTrace (prefixWord ++ tailWord_3814786) baseStart_3814786 baseEnd_3814786 := by
    simpa [prefixWord, tailWord_3814786, baseEnd_3814786] using wordTrace_append hprefix tailTrace_3814786
  have hstable : (prefixWord ++ tailWord_3814786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814786).length < 2 ^ (prefixWord ++ tailWord_3814786).sum := by decide
  have hdescent : baseEnd_3814786 < baseStart_3814786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814809 : List Nat := [1, 2, 1, 2, 1, 5, 2, 3, 2, 2, 2]
def baseStart_3814809 : Nat := 118140960795 + 3814809 * 2 ^ 59
def prefixEnd_3814809 : Nat := 4983230072969 + 3 ^ 40 * 3814809 * 2
def baseEnd_3814809 : Nat := 1958830622097670275943519

theorem tailTrace_3814809 : CollatzResearch.WordTrace tailWord_3814809 prefixEnd_3814809 1958830622097670275943519 := by
  unfold tailWord_3814809
  simp only [CollatzResearch.WordTrace]
  refine ⟨139137514836605985352351481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92758343224403990234900987 139137514836605985352351481)
  ·
    refine ⟨104353136127454489014263611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139137514836605985352351481 104353136127454489014263611)
    ·
      refine ⟨156529704191181733521395417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104353136127454489014263611 156529704191181733521395417)
      ·
        refine ⟨117397278143386300141046563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156529704191181733521395417 117397278143386300141046563)
        ·
          refine ⟨176095917215079450211569845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117397278143386300141046563 176095917215079450211569845)
          ·
            refine ⟨16508992238913698457334673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176095917215079450211569845 16508992238913698457334673)
            ·
              refine ⟨12381744179185273843001005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16508992238913698457334673 12381744179185273843001005)
              ·
                refine ⟨4643154067194477691125377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12381744179185273843001005 4643154067194477691125377)
                ·
                  refine ⟨3482365550395858268344033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4643154067194477691125377 3482365550395858268344033)
                  ·
                    refine ⟨2611774162796893701258025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3482365550395858268344033 2611774162796893701258025)
                    ·
                      refine ⟨1958830622097670275943519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2611774162796893701258025 1958830622097670275943519)
                      ·
                        rfl

theorem cell23_3814809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 2, 2].length) (baseStart_3814809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814809 prefixEnd_3814809 := by exact prefixLift 3814809
  have htrace : WordTrace (prefixWord ++ tailWord_3814809) baseStart_3814809 baseEnd_3814809 := by
    simpa [prefixWord, tailWord_3814809, baseEnd_3814809] using wordTrace_append hprefix tailTrace_3814809
  have hstable : (prefixWord ++ tailWord_3814809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814809).length < 2 ^ (prefixWord ++ tailWord_3814809).sum := by decide
  have hdescent : baseEnd_3814809 < baseStart_3814809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814815 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 7]
def baseStart_3814815 : Nat := 118140960795 + 3814815 * 2 ^ 59
def prefixEnd_3814815 : Nat := 4983230072969 + 3 ^ 40 * 3814815 * 2
def baseEnd_3814815 : Nat := 217648189220177472496499

theorem tailTrace_3814815 : CollatzResearch.WordTrace tailWord_3814815 prefixEnd_3814815 217648189220177472496499 := by
  unfold tailWord_3814815
  simp only [CollatzResearch.WordTrace]
  refine ⟨139137733674584248377069899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92758489116389498918046599 139137733674584248377069899)
  ·
    refine ⟨208706600511876372565604849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139137733674584248377069899 208706600511876372565604849)
    ·
      refine ⟨156529950383907279424203637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208706600511876372565604849 156529950383907279424203637)
      ·
        refine ⟨14674682848491307446019091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156529950383907279424203637 14674682848491307446019091)
        ·
          refine ⟨22012024272736961169028637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14674682848491307446019091 22012024272736961169028637)
          ·
            refine ⟨8254509102276360438385739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22012024272736961169028637 8254509102276360438385739)
            ·
              refine ⟨12381763653414540657578609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8254509102276360438385739 12381763653414540657578609)
              ·
                refine ⟨9286322740060905493183957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12381763653414540657578609 9286322740060905493183957)
                ·
                  refine ⟨217648189220177472496499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9286322740060905493183957 217648189220177472496499)
                  ·
                    rfl

theorem cell23_3814815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 7].length) (baseStart_3814815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814815 prefixEnd_3814815 := by exact prefixLift 3814815
  have htrace : WordTrace (prefixWord ++ tailWord_3814815) baseStart_3814815 baseEnd_3814815 := by
    simpa [prefixWord, tailWord_3814815, baseEnd_3814815] using wordTrace_append hprefix tailTrace_3814815
  have hstable : (prefixWord ++ tailWord_3814815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814815).length < 2 ^ (prefixWord ++ tailWord_3814815).sum := by decide
  have hdescent : baseEnd_3814815 < baseStart_3814815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814845 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 4, 5]
def baseStart_3814845 : Nat := 118140960795 + 3814845 * 2 ^ 59
def prefixEnd_3814845 : Nat := 4983230072969 + 3 ^ 40 * 3814845 * 2
def baseEnd_3814845 : Nat := 652949702467077378364451

theorem tailTrace_3814845 : CollatzResearch.WordTrace tailWord_3814845 prefixEnd_3814845 652949702467077378364451 := by
  unfold tailWord_3814845
  simp only [CollatzResearch.WordTrace]
  refine ⟨139138827864475563500661989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92759218576317042333774659 139138827864475563500661989)
  ·
    refine ⟨26088530224589168156374123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139138827864475563500661989 26088530224589168156374123)
    ·
      refine ⟨39132795336883752234561185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26088530224589168156374123 39132795336883752234561185)
      ·
        refine ⟨29349596502662814175920889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39132795336883752234561185 29349596502662814175920889)
        ·
          refine ⟨22012197376997110631940667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29349596502662814175920889 22012197376997110631940667)
          ·
            refine ⟨33018296065495665947911001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22012197376997110631940667 33018296065495665947911001)
            ·
              refine ⟨24763722049121749460933251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33018296065495665947911001 24763722049121749460933251)
              ·
                refine ⟨37145583073682624191399877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24763722049121749460933251 37145583073682624191399877)
                ·
                  refine ⟨6964796826315492035887477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37145583073682624191399877 6964796826315492035887477)
                  ·
                    refine ⟨652949702467077378364451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6964796826315492035887477 652949702467077378364451)
                    ·
                      rfl

theorem cell23_3814845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_3814845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814845 prefixEnd_3814845 := by exact prefixLift 3814845
  have htrace : WordTrace (prefixWord ++ tailWord_3814845) baseStart_3814845 baseEnd_3814845 := by
    simpa [prefixWord, tailWord_3814845, baseEnd_3814845] using wordTrace_append hprefix tailTrace_3814845
  have hstable : (prefixWord ++ tailWord_3814845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814845).length < 2 ^ (prefixWord ++ tailWord_3814845).sum := by decide
  have hdescent : baseEnd_3814845 < baseStart_3814845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814905 : List Nat := [1, 2, 1, 3, 1, 2, 1, 6, 6]
def baseStart_3814905 : Nat := 118140960795 + 3814905 * 2 ^ 59
def prefixEnd_3814905 : Nat := 4983230072969 + 3 ^ 40 * 3814905 * 2
def baseEnd_3814905 : Nat := 217653324026722433371453

theorem tailTrace_3814905 : CollatzResearch.WordTrace tailWord_3814905 prefixEnd_3814905 217653324026722433371453 := by
  unfold tailWord_3814905
  simp only [CollatzResearch.WordTrace]
  refine ⟨139141016244258193747846169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92760677496172129165230779 139141016244258193747846169)
  ·
    refine ⟨104355762183193645310884627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139141016244258193747846169 104355762183193645310884627)
    ·
      refine ⟨156533643274790467966326941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104355762183193645310884627 156533643274790467966326941)
      ·
        refine ⟨58700116228046425487372603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156533643274790467966326941 58700116228046425487372603)
        ·
          refine ⟨88050174342069638231058905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58700116228046425487372603 88050174342069638231058905)
          ·
            refine ⟨66037630756552228673294179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88050174342069638231058905 66037630756552228673294179)
            ·
              refine ⟨99056446134828343009941269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66037630756552228673294179 99056446134828343009941269)
              ·
                refine ⟨4643270912570078578590997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99056446134828343009941269 4643270912570078578590997)
                ·
                  refine ⟨217653324026722433371453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4643270912570078578590997 217653324026722433371453)
                  ·
                    rfl

theorem cell23_3814905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 6].length) (baseStart_3814905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814905 prefixEnd_3814905 := by exact prefixLift 3814905
  have htrace : WordTrace (prefixWord ++ tailWord_3814905) baseStart_3814905 baseEnd_3814905 := by
    simpa [prefixWord, tailWord_3814905, baseEnd_3814905] using wordTrace_append hprefix tailTrace_3814905
  have hstable : (prefixWord ++ tailWord_3814905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814905).length < 2 ^ (prefixWord ++ tailWord_3814905).sum := by decide
  have hdescent : baseEnd_3814905 < baseStart_3814905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814909 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 3, 4]
def baseStart_3814909 : Nat := 118140960795 + 3814909 * 2 ^ 59
def prefixEnd_3814909 : Nat := 4983230072969 + 3 ^ 40 * 3814909 * 2
def baseEnd_3814909 : Nat := 652960656721039961564353

theorem tailTrace_3814909 : CollatzResearch.WordTrace tailWord_3814909 prefixEnd_3814909 652960656721039961564353 := by
  unfold tailWord_3814909
  simp only [CollatzResearch.WordTrace]
  refine ⟨139141162136243702430991781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92760774757495801620661187 139141162136243702430991781)
  ·
    refine ⟨26088967900545694205810959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139141162136243702430991781 26088967900545694205810959)
    ·
      refine ⟨39133451850818541308716439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26088967900545694205810959 39133451850818541308716439)
      ·
        refine ⟨58700177776227811963074659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39133451850818541308716439 58700177776227811963074659)
        ·
          refine ⟨88050266664341717944611989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58700177776227811963074659 88050266664341717944611989)
          ·
            refine ⟨4127356249891018028653687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88050266664341717944611989 4127356249891018028653687)
            ·
              refine ⟨6191034374836527042980531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4127356249891018028653687 6191034374836527042980531)
              ·
                refine ⟨9286551562254790564470797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6191034374836527042980531 9286551562254790564470797)
                ·
                  refine ⟨3482456835845546461676549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9286551562254790564470797 3482456835845546461676549)
                  ·
                    refine ⟨652960656721039961564353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3482456835845546461676549 652960656721039961564353)
                    ·
                      rfl

theorem cell23_3814909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_3814909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814909 prefixEnd_3814909 := by exact prefixLift 3814909
  have htrace : WordTrace (prefixWord ++ tailWord_3814909) baseStart_3814909 baseEnd_3814909 := by
    simpa [prefixWord, tailWord_3814909, baseEnd_3814909] using wordTrace_append hprefix tailTrace_3814909
  have hstable : (prefixWord ++ tailWord_3814909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814909).length < 2 ^ (prefixWord ++ tailWord_3814909).sum := by decide
  have hdescent : baseEnd_3814909 < baseStart_3814909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814915 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 3]
def baseStart_3814915 : Nat := 118140960795 + 3814915 * 2 ^ 59
def prefixEnd_3814915 : Nat := 4983230072969 + 3 ^ 40 * 3814915 * 2
def baseEnd_3814915 : Nat := 1958885051047046861218031

theorem tailTrace_3814915 : CollatzResearch.WordTrace tailWord_3814915 prefixEnd_3814915 1958885051047046861218031 := by
  unfold tailWord_3814915
  simp only [CollatzResearch.WordTrace]
  refine ⟨139141380974221965455710199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92760920649481310303806799 139141380974221965455710199)
  ·
    refine ⟨208712071461332948183565299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139141380974221965455710199 208712071461332948183565299)
    ·
      refine ⟨313068107191999422275347949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208712071461332948183565299 313068107191999422275347949)
      ·
        refine ⟨117400540196999783353255481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313068107191999422275347949 117400540196999783353255481)
        ·
          refine ⟨88050405147749837514941611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117400540196999783353255481 88050405147749837514941611)
          ·
            refine ⟨132075607721624756272412417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88050405147749837514941611 132075607721624756272412417)
            ·
              refine ⟨99056705791218567204309313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132075607721624756272412417 99056705791218567204309313)
              ·
                refine ⟨74292529343413925403231985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99056705791218567204309313 74292529343413925403231985)
                ·
                  refine ⟨55719397007560444052423989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74292529343413925403231985 55719397007560444052423989)
                  ·
                    refine ⟨5223693469458791629914749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55719397007560444052423989 5223693469458791629914749)
                    ·
                      refine ⟨1958885051047046861218031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5223693469458791629914749 1958885051047046861218031)
                      ·
                        rfl

theorem cell23_3814915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_3814915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814915 prefixEnd_3814915 := by exact prefixLift 3814915
  have htrace : WordTrace (prefixWord ++ tailWord_3814915) baseStart_3814915 baseEnd_3814915 := by
    simpa [prefixWord, tailWord_3814915, baseEnd_3814915] using wordTrace_append hprefix tailTrace_3814915
  have hstable : (prefixWord ++ tailWord_3814915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814915).length < 2 ^ (prefixWord ++ tailWord_3814915).sum := by decide
  have hdescent : baseEnd_3814915 < baseStart_3814915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814922 : List Nat := [3, 1, 2, 2, 2, 3, 1, 3, 6]
def baseStart_3814922 : Nat := 118140960795 + 3814922 * 2 ^ 59
def prefixEnd_3814922 : Nat := 4983230072969 + 3 ^ 40 * 3814922 * 2
def baseEnd_3814922 : Nat := 217654293934625370425611

theorem tailTrace_3814922 : CollatzResearch.WordTrace tailWord_3814922 prefixEnd_3814922 217654293934625370425611 := by
  unfold tailWord_3814922
  simp only [CollatzResearch.WordTrace]
  refine ⟨34785409071299151412803755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92761090856797737100810013 34785409071299151412803755)
  ·
    refine ⟨52178113606948727119205633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34785409071299151412803755 52178113606948727119205633)
    ·
      refine ⟨39133585205211545339404225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52178113606948727119205633 39133585205211545339404225)
      ·
        refine ⟨29350188903908659004553169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39133585205211545339404225 29350188903908659004553169)
        ·
          refine ⟨22012641677931494253414877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29350188903908659004553169 22012641677931494253414877)
          ·
            refine ⟨8254740629224310345030579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22012641677931494253414877 8254740629224310345030579)
            ·
              refine ⟨12382110943836465517545869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8254740629224310345030579 12382110943836465517545869)
              ·
                refine ⟨4643291603938674569079701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12382110943836465517545869 4643291603938674569079701)
                ·
                  refine ⟨217654293934625370425611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4643291603938674569079701 217654293934625370425611)
                  ·
                    rfl

theorem cell23_3814922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 6].length) (baseStart_3814922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814922 prefixEnd_3814922 := by exact prefixLift 3814922
  have htrace : WordTrace (prefixWord ++ tailWord_3814922) baseStart_3814922 baseEnd_3814922 := by
    simpa [prefixWord, tailWord_3814922, baseEnd_3814922] using wordTrace_append hprefix tailTrace_3814922
  have hstable : (prefixWord ++ tailWord_3814922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814922).length < 2 ^ (prefixWord ++ tailWord_3814922).sum := by decide
  have hdescent : baseEnd_3814922 < baseStart_3814922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814985 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 1, 1, 6]
def baseStart_3814985 : Nat := 118140960795 + 3814985 * 2 ^ 59
def prefixEnd_3814985 : Nat := 4983230072969 + 3 ^ 40 * 3814985 * 2
def baseEnd_3814985 : Nat := 1958920994692861587342709

theorem tailTrace_3814985 : CollatzResearch.WordTrace tailWord_3814985 prefixEnd_3814985 1958920994692861587342709 := by
  unfold tailWord_3814985
  simp only [CollatzResearch.WordTrace]
  refine ⟨139143934083968367410758409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92762622722645578273838939 139143934083968367410758409)
  ·
    refine ⟨104357950562976275558068807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139143934083968367410758409 104357950562976275558068807)
    ·
      refine ⟨156536925844464413337103211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104357950562976275558068807 156536925844464413337103211)
      ·
        refine ⟨234805388766696620005654817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156536925844464413337103211 234805388766696620005654817)
        ·
          refine ⟨176104041575022465004241113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234805388766696620005654817 176104041575022465004241113)
          ·
            refine ⟨132078031181266848753180835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176104041575022465004241113 132078031181266848753180835)
            ·
              refine ⟨198117046771900273129771253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132078031181266848753180835 198117046771900273129771253)
              ·
                refine ⟨18573473134865650605916055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198117046771900273129771253 18573473134865650605916055)
                ·
                  refine ⟨27860209702298475908874083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18573473134865650605916055 27860209702298475908874083)
                  ·
                    refine ⟨41790314553447713863311125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27860209702298475908874083 41790314553447713863311125)
                    ·
                      refine ⟨1958920994692861587342709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41790314553447713863311125 1958920994692861587342709)
                      ·
                        rfl

theorem cell23_3814985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_3814985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814985 prefixEnd_3814985 := by exact prefixLift 3814985
  have htrace : WordTrace (prefixWord ++ tailWord_3814985) baseStart_3814985 baseEnd_3814985 := by
    simpa [prefixWord, tailWord_3814985, baseEnd_3814985] using wordTrace_append hprefix tailTrace_3814985
  have hstable : (prefixWord ++ tailWord_3814985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814985).length < 2 ^ (prefixWord ++ tailWord_3814985).sum := by decide
  have hdescent : baseEnd_3814985 < baseStart_3814985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814992 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 3]
def baseStart_3814992 : Nat := 118140960795 + 3814992 * 2 ^ 59
def prefixEnd_3814992 : Nat := 4983230072969 + 3 ^ 40 * 3814992 * 2
def baseEnd_3814992 : Nat := 1958924589057443059955177

theorem tailTrace_3814992 : CollatzResearch.WordTrace tailWord_3814992 prefixEnd_3814992 1958924589057443059955177 := by
  unfold tailWord_3814992
  simp only [CollatzResearch.WordTrace]
  refine ⟨69572094697471503803131615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92762792929962005070842153 69572094697471503803131615)
  ·
    refine ⟨104358142046207255704697423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69572094697471503803131615 104358142046207255704697423)
    ·
      refine ⟨156537213069310883557046135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104358142046207255704697423 156537213069310883557046135)
      ·
        refine ⟨234805819603966325335569203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156537213069310883557046135 234805819603966325335569203)
        ·
          refine ⟨352208729405949488003353805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234805819603966325335569203 352208729405949488003353805)
          ·
            refine ⟨132078273527231058001257677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352208729405949488003353805 132078273527231058001257677)
            ·
              refine ⟨49529352572711646750471629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132078273527231058001257677 49529352572711646750471629)
              ·
                refine ⟨18573507214766867531426861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49529352572711646750471629 18573507214766867531426861)
                ·
                  refine ⟨6965065205537575324285073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18573507214766867531426861 6965065205537575324285073)
                  ·
                    refine ⟨5223798904153181493213805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6965065205537575324285073 5223798904153181493213805)
                    ·
                      refine ⟨1958924589057443059955177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5223798904153181493213805 1958924589057443059955177)
                      ·
                        rfl

theorem cell23_3814992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 3].length) (baseStart_3814992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3814992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3814992 prefixEnd_3814992 := by exact prefixLift 3814992
  have htrace : WordTrace (prefixWord ++ tailWord_3814992) baseStart_3814992 baseEnd_3814992 := by
    simpa [prefixWord, tailWord_3814992, baseEnd_3814992] using wordTrace_append hprefix tailTrace_3814992
  have hstable : (prefixWord ++ tailWord_3814992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814992).length < 2 ^ (prefixWord ++ tailWord_3814992).sum := by decide
  have hdescent : baseEnd_3814992 < baseStart_3814992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815009 : List Nat := [1, 2, 3, 1, 1, 3, 3, 3, 1, 2, 3]
def baseStart_3815009 : Nat := 118140960795 + 3815009 * 2 ^ 59
def prefixEnd_3815009 : Nat := 4983230072969 + 3 ^ 40 * 3815009 * 2
def baseEnd_3815009 : Nat := 1958933318228569493442599

theorem tailTrace_3815009 : CollatzResearch.WordTrace tailWord_3815009 prefixEnd_3815009 1958933318228569493442599 := by
  unfold tailWord_3815009
  simp only [CollatzResearch.WordTrace]
  refine ⟨139144809435881419509632081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92763206290587613006421387 139144809435881419509632081)
  ·
    refine ⟨104358607076911064632224061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139144809435881419509632081 104358607076911064632224061)
    ·
      refine ⟨39134477653841649237084023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104358607076911064632224061 39134477653841649237084023)
      ·
        refine ⟨58701716480762473855626035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39134477653841649237084023 58701716480762473855626035)
        ·
          refine ⟨88052574721143710783439053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58701716480762473855626035 88052574721143710783439053)
          ·
            refine ⟨33019715520428891543789645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88052574721143710783439053 33019715520428891543789645)
            ·
              refine ⟨12382393320160834328921117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33019715520428891543789645 12382393320160834328921117)
              ·
                refine ⟨4643397495060312873345419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12382393320160834328921117 4643397495060312873345419)
                ·
                  refine ⟨6965096242590469310018129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4643397495060312873345419 6965096242590469310018129)
                  ·
                    refine ⟨5223822181942851982513597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6965096242590469310018129 5223822181942851982513597)
                    ·
                      refine ⟨1958933318228569493442599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5223822181942851982513597 1958933318228569493442599)
                      ·
                        rfl

theorem cell23_3815009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_3815009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815009 prefixEnd_3815009 := by exact prefixLift 3815009
  have htrace : WordTrace (prefixWord ++ tailWord_3815009) baseStart_3815009 baseEnd_3815009 := by
    simpa [prefixWord, tailWord_3815009, baseEnd_3815009] using wordTrace_append hprefix tailTrace_3815009
  have hstable : (prefixWord ++ tailWord_3815009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815009).length < 2 ^ (prefixWord ++ tailWord_3815009).sum := by decide
  have hdescent : baseEnd_3815009 < baseStart_3815009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815016 : List Nat := [2, 1, 4, 3, 1, 1, 3, 2, 2, 4]
def baseStart_3815016 : Nat := 118140960795 + 3815016 * 2 ^ 59
def prefixEnd_3815016 : Nat := 4983230072969 + 3 ^ 40 * 3815016 * 2
def baseEnd_3815016 : Nat := 652978970864383655351689

theorem tailTrace_3815016 : CollatzResearch.WordTrace tailWord_3815016 prefixEnd_3815016 652978970864383655351689 := by
  unfold tailWord_3815016
  simp only [CollatzResearch.WordTrace]
  refine ⟨69572532373428029852568451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92763376497904039803424601 69572532373428029852568451)
  ·
    refine ⟨104358798560142044778852677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69572532373428029852568451 104358798560142044778852677)
    ·
      refine ⟨19567274730026633396034877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104358798560142044778852677 19567274730026633396034877)
      ·
        refine ⟨7337728023759987523513079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19567274730026633396034877 7337728023759987523513079)
        ·
          refine ⟨11006592035639981285269619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7337728023759987523513079 11006592035639981285269619)
          ·
            refine ⟨16509888053459971927904429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11006592035639981285269619 16509888053459971927904429)
            ·
              refine ⟨6191208020047489472964161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16509888053459971927904429 6191208020047489472964161)
              ·
                refine ⟨4643406015035617104723121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6191208020047489472964161 4643406015035617104723121)
                ·
                  refine ⟨3482554511276712828542341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4643406015035617104723121 3482554511276712828542341)
                  ·
                    refine ⟨652978970864383655351689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3482554511276712828542341 652978970864383655351689)
                    ·
                      rfl

theorem cell23_3815016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_3815016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815016 prefixEnd_3815016 := by exact prefixLift 3815016
  have htrace : WordTrace (prefixWord ++ tailWord_3815016) baseStart_3815016 baseEnd_3815016 := by
    simpa [prefixWord, tailWord_3815016, baseEnd_3815016] using wordTrace_append hprefix tailTrace_3815016
  have hstable : (prefixWord ++ tailWord_3815016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815016).length < 2 ^ (prefixWord ++ tailWord_3815016).sum := by decide
  have hdescent : baseEnd_3815016 < baseStart_3815016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815025 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 1, 9]
def baseStart_3815025 : Nat := 118140960795 + 3815025 * 2 ^ 59
def prefixEnd_3815025 : Nat := 4983230072969 + 3 ^ 40 * 3815025 * 2
def baseEnd_3815025 : Nat := 652980511306347143614175

theorem tailTrace_3815025 : CollatzResearch.WordTrace tailWord_3815025 prefixEnd_3815025 652980511306347143614175 := by
  unfold tailWord_3815025
  simp only [CollatzResearch.WordTrace]
  refine ⟨139145393003823454242214529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92763595335882302828143019 139145393003823454242214529)
  ·
    refine ⟨104359044752867590681660897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139145393003823454242214529 104359044752867590681660897)
    ·
      refine ⟨78269283564650693011245673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104359044752867590681660897 78269283564650693011245673)
      ·
        refine ⟨58701962673488019758434255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78269283564650693011245673 58701962673488019758434255)
        ·
          refine ⟨88052944010232029637651383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58701962673488019758434255 88052944010232029637651383)
          ·
            refine ⟨132079416015348044456477075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88052944010232029637651383 132079416015348044456477075)
            ·
              refine ⟨198119124023022066684715613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132079416015348044456477075 198119124023022066684715613)
              ·
                refine ⟨74294671508633275006768355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198119124023022066684715613 74294671508633275006768355)
                ·
                  refine ⟨111442007262949912510152533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74294671508633275006768355 111442007262949912510152533)
                  ·
                    refine ⟨652980511306347143614175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 111442007262949912510152533 652980511306347143614175)
                    ·
                      rfl

theorem cell23_3815025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_3815025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815025 prefixEnd_3815025 := by exact prefixLift 3815025
  have htrace : WordTrace (prefixWord ++ tailWord_3815025) baseStart_3815025 baseEnd_3815025 := by
    simpa [prefixWord, tailWord_3815025, baseEnd_3815025] using wordTrace_append hprefix tailTrace_3815025
  have hstable : (prefixWord ++ tailWord_3815025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815025).length < 2 ^ (prefixWord ++ tailWord_3815025).sum := by decide
  have hdescent : baseEnd_3815025 < baseStart_3815025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815049 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 3, 3, 2]
def baseStart_3815049 : Nat := 118140960795 + 3815049 * 2 ^ 59
def prefixEnd_3815049 : Nat := 4983230072969 + 3 ^ 40 * 3815049 * 2
def baseEnd_3815049 : Nat := 1958953857454749336942415

theorem tailTrace_3815049 : CollatzResearch.WordTrace tailWord_3815049 prefixEnd_3815049 1958953857454749336942415 := by
  unfold tailWord_3815049
  simp only [CollatzResearch.WordTrace]
  refine ⟨139146268355736506341088201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92764178903824337560725467 139146268355736506341088201)
  ·
    refine ⟨104359701266802379755816151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139146268355736506341088201 104359701266802379755816151)
    ·
      refine ⟨156539551900203569633724227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104359701266802379755816151 156539551900203569633724227)
      ·
        refine ⟨234809327850305354450586341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156539551900203569633724227 234809327850305354450586341)
        ·
          refine ⟨44026748971932253959484939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234809327850305354450586341 44026748971932253959484939)
          ·
            refine ⟨66040123457898380939227409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44026748971932253959484939 66040123457898380939227409)
            ·
              refine ⟨49530092593423785704420557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66040123457898380939227409 49530092593423785704420557)
              ·
                refine ⟨18573784722533919639157709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49530092593423785704420557 18573784722533919639157709)
                ·
                  refine ⟨6965169270950219864684141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18573784722533919639157709 6965169270950219864684141)
                  ·
                    refine ⟨2611938476606332449256553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6965169270950219864684141 2611938476606332449256553)
                    ·
                      refine ⟨1958953857454749336942415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2611938476606332449256553 1958953857454749336942415)
                      ·
                        rfl

theorem cell23_3815049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 3, 2].length) (baseStart_3815049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815049 prefixEnd_3815049 := by exact prefixLift 3815049
  have htrace : WordTrace (prefixWord ++ tailWord_3815049) baseStart_3815049 baseEnd_3815049 := by
    simpa [prefixWord, tailWord_3815049, baseEnd_3815049] using wordTrace_append hprefix tailTrace_3815049
  have hstable : (prefixWord ++ tailWord_3815049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815049).length < 2 ^ (prefixWord ++ tailWord_3815049).sum := by decide
  have hdescent : baseEnd_3815049 < baseStart_3815049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815074 : List Nat := [3, 3, 1, 4, 1, 1, 3, 2, 1, 2, 2]
def baseStart_3815074 : Nat := 118140960795 + 3815074 * 2 ^ 59
def prefixEnd_3815074 : Nat := 4983230072969 + 3 ^ 40 * 3815074 * 2
def baseEnd_3815074 : Nat := 1958966694471111739129801

theorem tailTrace_3815074 : CollatzResearch.WordTrace tailWord_3815074 prefixEnd_3815074 1958966694471111739129801 := by
  unfold tailWord_3815074
  simp only [CollatzResearch.WordTrace]
  refine ⟨34786795045161483902687069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92764786787097290407165517 34786795045161483902687069)
  ·
    refine ⟨13045048141935556463507651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34786795045161483902687069 13045048141935556463507651)
    ·
      refine ⟨19567572212903334695261477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13045048141935556463507651 19567572212903334695261477)
      ·
        refine ⟨3668919789919375255361527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19567572212903334695261477 3668919789919375255361527)
        ·
          refine ⟨5503379684879062883042291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3668919789919375255361527 5503379684879062883042291)
          ·
            refine ⟨8255069527318594324563437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5503379684879062883042291 8255069527318594324563437)
            ·
              refine ⟨3095651072744472871711289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8255069527318594324563437 3095651072744472871711289)
              ·
                refine ⟨2321738304558354653783467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3095651072744472871711289 2321738304558354653783467)
                ·
                  refine ⟨3482607456837531980675201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2321738304558354653783467 3482607456837531980675201)
                  ·
                    refine ⟨2611955592628148985506401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3482607456837531980675201 2611955592628148985506401)
                    ·
                      refine ⟨1958966694471111739129801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2611955592628148985506401 1958966694471111739129801)
                      ·
                        rfl

theorem cell23_3815074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_3815074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815074 prefixEnd_3815074 := by exact prefixLift 3815074
  have htrace : WordTrace (prefixWord ++ tailWord_3815074) baseStart_3815074 baseEnd_3815074 := by
    simpa [prefixWord, tailWord_3815074, baseEnd_3815074] using wordTrace_append hprefix tailTrace_3815074
  have hstable : (prefixWord ++ tailWord_3815074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815074).length < 2 ^ (prefixWord ++ tailWord_3815074).sum := by decide
  have hdescent : baseEnd_3815074 < baseStart_3815074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815117 : List Nat := [1, 6, 2, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_3815117 : Nat := 118140960795 + 3815117 * 2 ^ 59
def prefixEnd_3815117 : Nat := 4983230072969 + 3 ^ 40 * 3815117 * 2
def baseEnd_3815117 : Nat := 1958988774139255070892103

theorem tailTrace_3815117 : CollatzResearch.WordTrace tailWord_3815117 prefixEnd_3815117 1958988774139255070892103 := by
  unfold tailWord_3815117
  simp only [CollatzResearch.WordTrace]
  refine ⟨139148748519490153954563605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92765832346326769303042403 139148748519490153954563605)
  ·
    refine ⟨6522597586851100966620169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 139148748519490153954563605 6522597586851100966620169)
    ·
      refine ⟨4891948190138325724965127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6522597586851100966620169 4891948190138325724965127)
      ·
        refine ⟨7337922285207488587447691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4891948190138325724965127 7337922285207488587447691)
        ·
          refine ⟨11006883427811232881171537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7337922285207488587447691 11006883427811232881171537)
          ·
            refine ⟨8255162570858424660878653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11006883427811232881171537 8255162570858424660878653)
            ·
              refine ⟨3095685964071909247829495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8255162570858424660878653 3095685964071909247829495)
              ·
                refine ⟨4643528946107863871744243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3095685964071909247829495 4643528946107863871744243)
                ·
                  refine ⟨6965293419161795807616365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4643528946107863871744243 6965293419161795807616365)
                  ·
                    refine ⟨2611985032185673427856137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6965293419161795807616365 2611985032185673427856137)
                    ·
                      refine ⟨1958988774139255070892103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2611985032185673427856137 1958988774139255070892103)
                      ·
                        rfl

theorem cell23_3815117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_3815117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815117 prefixEnd_3815117 := by exact prefixLift 3815117
  have htrace : WordTrace (prefixWord ++ tailWord_3815117) baseStart_3815117 baseEnd_3815117 := by
    simpa [prefixWord, tailWord_3815117, baseEnd_3815117] using wordTrace_append hprefix tailTrace_3815117
  have hstable : (prefixWord ++ tailWord_3815117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815117).length < 2 ^ (prefixWord ++ tailWord_3815117).sum := by decide
  have hdescent : baseEnd_3815117 < baseStart_3815117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815136 : List Nat := [2, 1, 1, 3, 1, 2, 6, 2, 5]
def baseStart_3815136 : Nat := 118140960795 + 3815136 * 2 ^ 59
def prefixEnd_3815136 : Nat := 4983230072969 + 3 ^ 40 * 3815136 * 2
def baseEnd_3815136 : Nat := 217666503363521166283835

theorem tailTrace_3815136 : CollatzResearch.WordTrace tailWord_3815136 prefixEnd_3815136 217666503363521166283835 := by
  unfold tailWord_3815136
  simp only [CollatzResearch.WordTrace]
  refine ⟨69574720753210660099752631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92766294337614213466336841 69574720753210660099752631)
  ·
    refine ⟨104362081129815990149628947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69574720753210660099752631 104362081129815990149628947)
    ·
      refine ⟨156543121694723985224443421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104362081129815990149628947 156543121694723985224443421)
      ·
        refine ⟨58703670635521494459166283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156543121694723985224443421 58703670635521494459166283)
        ·
          refine ⟨88055505953282241688749425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58703670635521494459166283 88055505953282241688749425)
          ·
            refine ⟨66041629464961681266562069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88055505953282241688749425 66041629464961681266562069)
            ·
              refine ⟨3095701381170078809370097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66041629464961681266562069 3095701381170078809370097)
              ·
                refine ⟨2321776035877559107027573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3095701381170078809370097 2321776035877559107027573)
                ·
                  refine ⟨217666503363521166283835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2321776035877559107027573 217666503363521166283835)
                  ·
                    rfl

theorem cell23_3815136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 5].length) (baseStart_3815136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815136 prefixEnd_3815136 := by exact prefixLift 3815136
  have htrace : WordTrace (prefixWord ++ tailWord_3815136) baseStart_3815136 baseEnd_3815136 := by
    simpa [prefixWord, tailWord_3815136, baseEnd_3815136] using wordTrace_append hprefix tailTrace_3815136
  have hstable : (prefixWord ++ tailWord_3815136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815136).length < 2 ^ (prefixWord ++ tailWord_3815136).sum := by decide
  have hdescent : baseEnd_3815136 < baseStart_3815136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815166 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_3815166 : Nat := 118140960795 + 3815166 * 2 ^ 59
def prefixEnd_3815166 : Nat := 4983230072969 + 3 ^ 40 * 3815166 * 2
def baseEnd_3815166 : Nat := 653004644897108459726459

theorem tailTrace_3815166 : CollatzResearch.WordTrace tailWord_3815166 prefixEnd_3815166 653004644897108459726459 := by
  unfold tailWord_3815166
  simp only [CollatzResearch.WordTrace]
  refine ⟨17393816962039079415387169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92767023797541756882064901 17393816962039079415387169)
  ·
    refine ⟨13045362721529309561540377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17393816962039079415387169 13045362721529309561540377)
    ·
      refine ⟨9784022041146982171155283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13045362721529309561540377 9784022041146982171155283)
      ·
        refine ⟨14676033061720473256732925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9784022041146982171155283 14676033061720473256732925)
        ·
          refine ⟨5503512398145177471274847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14676033061720473256732925 5503512398145177471274847)
          ·
            refine ⟨8255268597217766206912271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5503512398145177471274847 8255268597217766206912271)
            ·
              refine ⟨12382902895826649310368407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8255268597217766206912271 12382902895826649310368407)
              ·
                refine ⟨18574354343739973965552611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12382902895826649310368407 18574354343739973965552611)
                ·
                  refine ⟨27861531515609960948328917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18574354343739973965552611 27861531515609960948328917)
                  ·
                    refine ⟨653004644897108459726459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27861531515609960948328917 653004644897108459726459)
                    ·
                      rfl

theorem cell23_3815166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_3815166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815166 prefixEnd_3815166 := by exact prefixLift 3815166
  have htrace : WordTrace (prefixWord ++ tailWord_3815166) baseStart_3815166 baseEnd_3815166 := by
    simpa [prefixWord, tailWord_3815166, baseEnd_3815166] using wordTrace_append hprefix tailTrace_3815166
  have hstable : (prefixWord ++ tailWord_3815166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815166).length < 2 ^ (prefixWord ++ tailWord_3815166).sum := by decide
  have hdescent : baseEnd_3815166 < baseStart_3815166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815196 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 3, 4]
def baseStart_3815196 : Nat := 118140960795 + 3815196 * 2 ^ 59
def prefixEnd_3815196 : Nat := 4983230072969 + 3 ^ 40 * 3815196 * 2
def baseEnd_3815196 : Nat := 653009779703653420601413

theorem tailTrace_3815196 : CollatzResearch.WordTrace tailWord_3815196 prefixEnd_3815196 653009779703653420601413 := by
  unfold tailWord_3815196
  simp only [CollatzResearch.WordTrace]
  refine ⟨69575814943101975223344721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92767753257469300297792961 69575814943101975223344721)
  ·
    refine ⟨52181861207326481417508541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69575814943101975223344721 52181861207326481417508541)
    ·
      refine ⟨19568197952747430531565703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52181861207326481417508541 19568197952747430531565703)
      ·
        refine ⟨29352296929121145797348555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19568197952747430531565703 29352296929121145797348555)
        ·
          refine ⟨44028445393681718696022833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29352296929121145797348555 44028445393681718696022833)
          ·
            refine ⟨33021334045261289022017125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44028445393681718696022833 33021334045261289022017125)
            ·
              refine ⟨6191500133486491691628211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33021334045261289022017125 6191500133486491691628211)
              ·
                refine ⟨9287250200229737537442317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6191500133486491691628211 9287250200229737537442317)
                ·
                  refine ⟨3482718825086151576540869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9287250200229737537442317 3482718825086151576540869)
                  ·
                    refine ⟨653009779703653420601413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3482718825086151576540869 653009779703653420601413)
                    ·
                      rfl

theorem cell23_3815196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_3815196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815196 prefixEnd_3815196 := by exact prefixLift 3815196
  have htrace : WordTrace (prefixWord ++ tailWord_3815196) baseStart_3815196 baseEnd_3815196 := by
    simpa [prefixWord, tailWord_3815196, baseEnd_3815196] using wordTrace_append hprefix tailTrace_3815196
  have hstable : (prefixWord ++ tailWord_3815196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815196).length < 2 ^ (prefixWord ++ tailWord_3815196).sum := by decide
  have hdescent : baseEnd_3815196 < baseStart_3815196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815230 : List Nat := [4, 2, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_3815230 : Nat := 118140960795 + 3815230 * 2 ^ 59
def prefixEnd_3815230 : Nat := 4983230072969 + 3 ^ 40 * 3815230 * 2
def baseEnd_3815230 : Nat := 653015599151071042926361

theorem tailTrace_3815230 : CollatzResearch.WordTrace tailWord_3815230 prefixEnd_3815230 653015599151071042926361 := by
  unfold tailWord_3815230
  simp only [CollatzResearch.WordTrace]
  refine ⟨17394108746010096781678393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92768579978720516168951429 17394108746010096781678393)
  ·
    refine ⟨13045581559507572586258795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17394108746010096781678393 13045581559507572586258795)
    ·
      refine ⟨19568372339261358879388193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13045581559507572586258795 19568372339261358879388193)
      ·
        refine ⟨14676279254446019159541145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19568372339261358879388193 14676279254446019159541145)
        ·
          refine ⟨11007209440834514369655859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14676279254446019159541145 11007209440834514369655859)
          ·
            refine ⟨16510814161251771554483789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11007209440834514369655859 16510814161251771554483789)
            ·
              refine ⟨6191555310469414332931421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16510814161251771554483789 6191555310469414332931421)
              ·
                refine ⟨2321833241426030374849283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6191555310469414332931421 2321833241426030374849283)
                ·
                  refine ⟨3482749862139045562273925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2321833241426030374849283 3482749862139045562273925)
                  ·
                    refine ⟨653015599151071042926361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3482749862139045562273925 653015599151071042926361)
                    ·
                      rfl

theorem cell23_3815230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_3815230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815230 prefixEnd_3815230 := by exact prefixLift 3815230
  have htrace : WordTrace (prefixWord ++ tailWord_3815230) baseStart_3815230 baseEnd_3815230 := by
    simpa [prefixWord, tailWord_3815230, baseEnd_3815230] using wordTrace_append hprefix tailTrace_3815230
  have hstable : (prefixWord ++ tailWord_3815230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815230).length < 2 ^ (prefixWord ++ tailWord_3815230).sum := by decide
  have hdescent : baseEnd_3815230 < baseStart_3815230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815253 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 3, 1, 3]
def baseStart_3815253 : Nat := 118140960795 + 3815253 * 2 ^ 59
def prefixEnd_3815253 : Nat := 4983230072969 + 3 ^ 40 * 3815253 * 2
def baseEnd_3815253 : Nat := 1959058607508266538791477

theorem tailTrace_3815253 : CollatzResearch.WordTrace tailWord_3815253 prefixEnd_3815253 1959058607508266538791477 := by
  unfold tailWord_3815253
  simp only [CollatzResearch.WordTrace]
  refine ⟨139153708846997449181514413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92769139231331632787676275 139153708846997449181514413)
  ·
    refine ⟨52182640817624043443067905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139153708846997449181514413 52182640817624043443067905)
    ·
      refine ⟨39136980613218032582300929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52182640817624043443067905 39136980613218032582300929)
      ·
        refine ⟨29352735459913524436725697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39136980613218032582300929 29352735459913524436725697)
        ·
          refine ⟨22014551594935143327544273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29352735459913524436725697 22014551594935143327544273)
          ·
            refine ⟨16510913696201357495658205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22014551594935143327544273 16510913696201357495658205)
            ·
              refine ⟨6191592636075509060871827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16510913696201357495658205 6191592636075509060871827)
              ·
                refine ⟨9287388954113263591307741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6191592636075509060871827 9287388954113263591307741)
                ·
                  refine ⟨3482770857792473846740403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9287388954113263591307741 3482770857792473846740403)
                  ·
                    refine ⟨5224156286688710770110605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3482770857792473846740403 5224156286688710770110605)
                    ·
                      refine ⟨1959058607508266538791477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5224156286688710770110605 1959058607508266538791477)
                      ·
                        rfl

theorem cell23_3815253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_3815253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815253 prefixEnd_3815253 := by exact prefixLift 3815253
  have htrace : WordTrace (prefixWord ++ tailWord_3815253) baseStart_3815253 baseEnd_3815253 := by
    simpa [prefixWord, tailWord_3815253, baseEnd_3815253] using wordTrace_append hprefix tailTrace_3815253
  have hstable : (prefixWord ++ tailWord_3815253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815253).length < 2 ^ (prefixWord ++ tailWord_3815253).sum := by decide
  have hdescent : baseEnd_3815253 < baseStart_3815253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815260 : List Nat := [2, 2, 4, 2, 2, 2, 2, 1, 6]
def baseStart_3815260 : Nat := 118140960795 + 3815260 * 2 ^ 59
def prefixEnd_3815260 : Nat := 4983230072969 + 3 ^ 40 * 3815260 * 2
def baseEnd_3815260 : Nat := 217673577985872001267105

theorem tailTrace_3815260 : CollatzResearch.WordTrace tailWord_3815260 prefixEnd_3815260 217673577985872001267105 := by
  unfold tailWord_3815260
  simp only [CollatzResearch.WordTrace]
  refine ⟨69576982078986044688509617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92769309438648059584679489 69576982078986044688509617)
  ·
    refine ⟨52182736559239533516382213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69576982078986044688509617 52182736559239533516382213)
    ·
      refine ⟨9784263104857412534321665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52182736559239533516382213 9784263104857412534321665)
      ·
        refine ⟨7338197328643059400741249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9784263104857412534321665 7338197328643059400741249)
        ·
          refine ⟨5503647996482294550555937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7338197328643059400741249 5503647996482294550555937)
          ·
            refine ⟨4127735997361720912916953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5503647996482294550555937 4127735997361720912916953)
            ·
              refine ⟨3095801998021290684687715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4127735997361720912916953 3095801998021290684687715)
              ·
                refine ⟨4643702997031936027031573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3095801998021290684687715 4643702997031936027031573)
                ·
                  refine ⟨217673577985872001267105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4643702997031936027031573 217673577985872001267105)
                  ·
                    rfl

theorem cell23_3815260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 6].length) (baseStart_3815260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815260 prefixEnd_3815260 := by exact prefixLift 3815260
  have htrace : WordTrace (prefixWord ++ tailWord_3815260) baseStart_3815260 baseEnd_3815260 := by
    simpa [prefixWord, tailWord_3815260, baseEnd_3815260] using wordTrace_append hprefix tailTrace_3815260
  have hstable : (prefixWord ++ tailWord_3815260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815260).length < 2 ^ (prefixWord ++ tailWord_3815260).sum := by decide
  have hdescent : baseEnd_3815260 < baseStart_3815260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815269 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 1, 6]
def baseStart_3815269 : Nat := 118140960795 + 3815269 * 2 ^ 59
def prefixEnd_3815269 : Nat := 4983230072969 + 3 ^ 40 * 3815269 * 2
def baseEnd_3815269 : Nat := 653022274399579492063801

theorem tailTrace_3815269 : CollatzResearch.WordTrace tailWord_3815269 prefixEnd_3815269 653022274399579492063801 := by
  unfold tailWord_3815269
  simp only [CollatzResearch.WordTrace]
  refine ⟨139154292414939483914096861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92769528276626322609397907 139154292414939483914096861)
  ·
    refine ⟨52182859655602306467786323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139154292414939483914096861 52182859655602306467786323)
    ·
      refine ⟨78274289483403459701679485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52182859655602306467786323 78274289483403459701679485)
      ·
        refine ⟨29352858556276297388129807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78274289483403459701679485 29352858556276297388129807)
        ·
          refine ⟨44029287834414446082194711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29352858556276297388129807 44029287834414446082194711)
          ·
            refine ⟨66043931751621669123292067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44029287834414446082194711 66043931751621669123292067)
            ·
              refine ⟨99065897627432503684938101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66043931751621669123292067 99065897627432503684938101)
              ·
                refine ⟨9287427902571797220462947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99065897627432503684938101 9287427902571797220462947)
                ·
                  refine ⟨13931141853857695830694421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9287427902571797220462947 13931141853857695830694421)
                  ·
                    refine ⟨653022274399579492063801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13931141853857695830694421 653022274399579492063801)
                    ·
                      rfl

theorem cell23_3815269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_3815269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815269 prefixEnd_3815269 := by exact prefixLift 3815269
  have htrace : WordTrace (prefixWord ++ tailWord_3815269) baseStart_3815269 baseEnd_3815269 := by
    simpa [prefixWord, tailWord_3815269, baseEnd_3815269] using wordTrace_append hprefix tailTrace_3815269
  have hstable : (prefixWord ++ tailWord_3815269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815269).length < 2 ^ (prefixWord ++ tailWord_3815269).sum := by decide
  have hdescent : baseEnd_3815269 < baseStart_3815269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815276 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 4]
def baseStart_3815276 : Nat := 118140960795 + 3815276 * 2 ^ 59
def prefixEnd_3815276 : Nat := 4983230072969 + 3 ^ 40 * 3815276 * 2
def baseEnd_3815276 : Nat := 1959070417563319948803871

theorem tailTrace_3815276 : CollatzResearch.WordTrace tailWord_3815276 prefixEnd_3815276 1959070417563319948803871 := by
  unfold tailWord_3815276
  simp only [CollatzResearch.WordTrace]
  refine ⟨69577273862957062054800841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92769698483942749406401121 69577273862957062054800841)
  ·
    refine ⟨52182955397217796541100631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69577273862957062054800841 52182955397217796541100631)
    ·
      refine ⟨78274433095826694811650947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52182955397217796541100631 78274433095826694811650947)
      ·
        refine ⟨117411649643740042217476421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78274433095826694811650947 117411649643740042217476421)
        ·
          refine ⟨22014684308201257915776829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117411649643740042217476421 22014684308201257915776829)
          ·
            refine ⟨8255506615575471718416311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22014684308201257915776829 8255506615575471718416311)
            ·
              refine ⟨12383259923363207577624467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8255506615575471718416311 12383259923363207577624467)
              ·
                refine ⟨18574889885044811366436701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12383259923363207577624467 18574889885044811366436701)
                ·
                  refine ⟨6965583706891804262413763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18574889885044811366436701 6965583706891804262413763)
                  ·
                    refine ⟨10448375560337706393620645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6965583706891804262413763 10448375560337706393620645)
                    ·
                      refine ⟨1959070417563319948803871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10448375560337706393620645 1959070417563319948803871)
                      ·
                        rfl

theorem cell23_3815276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_3815276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815276 prefixEnd_3815276 := by exact prefixLift 3815276
  have htrace : WordTrace (prefixWord ++ tailWord_3815276) baseStart_3815276 baseEnd_3815276 := by
    simpa [prefixWord, tailWord_3815276, baseEnd_3815276] using wordTrace_append hprefix tailTrace_3815276
  have hstable : (prefixWord ++ tailWord_3815276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815276).length < 2 ^ (prefixWord ++ tailWord_3815276).sum := by decide
  have hdescent : baseEnd_3815276 < baseStart_3815276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815304 : List Nat := [2, 1, 3, 3, 3, 2, 2, 2, 1, 1, 3]
def baseStart_3815304 : Nat := 118140960795 + 3815304 * 2 ^ 59
def prefixEnd_3815304 : Nat := 4983230072969 + 3 ^ 40 * 3815304 * 2
def baseEnd_3815304 : Nat := 1959084795021645839253743

theorem tailTrace_3815304 : CollatzResearch.WordTrace tailWord_3815304 prefixEnd_3815304 1959084795021645839253743 := by
  unfold tailWord_3815304
  simp only [CollatzResearch.WordTrace]
  refine ⟨69577784484906342445810483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92770379313208456594413977 69577784484906342445810483)
  ·
    refine ⟨104366676727359513668715725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69577784484906342445810483 104366676727359513668715725)
    ·
      refine ⟨39137503772759817625768397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104366676727359513668715725 39137503772759817625768397)
      ·
        refine ⟨14676563914784931609663149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39137503772759817625768397 14676563914784931609663149)
        ·
          refine ⟨5503711468044349353623681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14676563914784931609663149 5503711468044349353623681)
          ·
            refine ⟨4127783601033262015217761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5503711468044349353623681 4127783601033262015217761)
            ·
              refine ⟨3095837700774946511413321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4127783601033262015217761 3095837700774946511413321)
              ·
                refine ⟨2321878275581209883559991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3095837700774946511413321 2321878275581209883559991)
                ·
                  refine ⟨3482817413371814825339987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2321878275581209883559991 3482817413371814825339987)
                  ·
                    refine ⟨5224226120057722238009981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3482817413371814825339987 5224226120057722238009981)
                    ·
                      refine ⟨1959084795021645839253743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5224226120057722238009981 1959084795021645839253743)
                      ·
                        rfl

theorem cell23_3815304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_3815304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815304 prefixEnd_3815304 := by exact prefixLift 3815304
  have htrace : WordTrace (prefixWord ++ tailWord_3815304) baseStart_3815304 baseEnd_3815304 := by
    simpa [prefixWord, tailWord_3815304, baseEnd_3815304] using wordTrace_append hprefix tailTrace_3815304
  have hstable : (prefixWord ++ tailWord_3815304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815304).length < 2 ^ (prefixWord ++ tailWord_3815304).sum := by decide
  have hdescent : baseEnd_3815304 < baseStart_3815304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815316 : List Nat := [2, 4, 2, 1, 1, 2, 3, 8]
def baseStart_3815316 : Nat := 118140960795 + 3815316 * 2 ^ 59
def prefixEnd_3815316 : Nat := 4983230072969 + 3 ^ 40 * 3815316 * 2
def baseEnd_3815316 : Nat := 72558924325537029344581

theorem tailTrace_3815316 : CollatzResearch.WordTrace tailWord_3815316 prefixEnd_3815316 72558924325537029344581 := by
  unfold tailWord_3815316
  simp only [CollatzResearch.WordTrace]
  refine ⟨69578003322884605470528901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92770671097179473960705201 69578003322884605470528901)
  ·
    refine ⟨13045875623040863525724169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69578003322884605470528901 13045875623040863525724169)
    ·
      refine ⟨9784406717280647644293127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13045875623040863525724169 9784406717280647644293127)
      ·
        refine ⟨14676610075920971466439691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9784406717280647644293127 14676610075920971466439691)
        ·
          refine ⟨22014915113881457199659537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14676610075920971466439691 22014915113881457199659537)
          ·
            refine ⟨16511186335411092899744653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22014915113881457199659537 16511186335411092899744653)
            ·
              refine ⟨6191694875779159837404245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16511186335411092899744653 6191694875779159837404245)
              ·
                refine ⟨72558924325537029344581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6191694875779159837404245 72558924325537029344581)
                ·
                  rfl

theorem cell23_3815316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 8].length) (baseStart_3815316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815316 prefixEnd_3815316 := by exact prefixLift 3815316
  have htrace : WordTrace (prefixWord ++ tailWord_3815316) baseStart_3815316 baseEnd_3815316 := by
    simpa [prefixWord, tailWord_3815316, baseEnd_3815316] using wordTrace_append hprefix tailTrace_3815316
  have hstable : (prefixWord ++ tailWord_3815316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815316).length < 2 ^ (prefixWord ++ tailWord_3815316).sum := by decide
  have hdescent : baseEnd_3815316 < baseStart_3815316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815359 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 4, 6]
def baseStart_3815359 : Nat := 118140960795 + 3815359 * 2 ^ 59
def prefixEnd_3815359 : Nat := 4983230072969 + 3 ^ 40 * 3815359 * 2
def baseEnd_3815359 : Nat := 653037678819214374688663

theorem tailTrace_3815359 : CollatzResearch.WordTrace tailWord_3815359 prefixEnd_3815359 653037678819214374688663 := by
  unfold tailWord_3815359
  simp only [CollatzResearch.WordTrace]
  refine ⟨139157574984613429284873131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92771716656408952856582087 139157574984613429284873131)
  ·
    refine ⟨208736362476920143927309697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139157574984613429284873131 208736362476920143927309697)
    ·
      refine ⟨156552271857690107945482273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208736362476920143927309697 156552271857690107945482273)
      ·
        refine ⟨117414203893267580959111705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156552271857690107945482273 117414203893267580959111705)
        ·
          refine ⟨88060652919950685719333779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117414203893267580959111705 88060652919950685719333779)
          ·
            refine ⟨132090979379926028579000669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88060652919950685719333779 132090979379926028579000669)
            ·
              refine ⟨49534117267472260717125251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132090979379926028579000669 49534117267472260717125251)
              ·
                refine ⟨74301175901208391075687877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49534117267472260717125251 74301175901208391075687877)
                ·
                  refine ⟨13931470481476573326691477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74301175901208391075687877 13931470481476573326691477)
                  ·
                    refine ⟨653037678819214374688663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13931470481476573326691477 653037678819214374688663)
                    ·
                      rfl

theorem cell23_3815359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 6].length) (baseStart_3815359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815359 prefixEnd_3815359 := by exact prefixLift 3815359
  have htrace : WordTrace (prefixWord ++ tailWord_3815359) baseStart_3815359 baseEnd_3815359 := by
    simpa [prefixWord, tailWord_3815359, baseEnd_3815359] using wordTrace_append hprefix tailTrace_3815359
  have hstable : (prefixWord ++ tailWord_3815359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815359).length < 2 ^ (prefixWord ++ tailWord_3815359).sum := by decide
  have hdescent : baseEnd_3815359 < baseStart_3815359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815369 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 1, 3, 5]
def baseStart_3815369 : Nat := 118140960795 + 3815369 * 2 ^ 59
def prefixEnd_3815369 : Nat := 4983230072969 + 3 ^ 40 * 3815369 * 2
def baseEnd_3815369 : Nat := 1959118171264188084940943

theorem tailTrace_3815369 : CollatzResearch.WordTrace tailWord_3815369 prefixEnd_3815369 1959118171264188084940943 := by
  unfold tailWord_3815369
  simp only [CollatzResearch.WordTrace]
  refine ⟨139157939714577200992737161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92771959809718133995158107 139157939714577200992737161)
  ·
    refine ⟨104368454785932900744552871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139157939714577200992737161 104368454785932900744552871)
    ·
      refine ⟨156552682178899351116829307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104368454785932900744552871 156552682178899351116829307)
      ·
        refine ⟨234829023268349026675243961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156552682178899351116829307 234829023268349026675243961)
        ·
          refine ⟨176121767451261770006432971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234829023268349026675243961 176121767451261770006432971)
          ·
            refine ⟨264182651176892655009649457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176121767451261770006432971 264182651176892655009649457)
            ·
              refine ⟨198136988382669491257237093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264182651176892655009649457 198136988382669491257237093)
              ·
                refine ⟨37150685321750529610731955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198136988382669491257237093 37150685321750529610731955)
                ·
                  refine ⟨55726027982625794416097933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37150685321750529610731955 55726027982625794416097933)
                  ·
                    refine ⟨20897260493484672906036725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55726027982625794416097933 20897260493484672906036725)
                    ·
                      refine ⟨1959118171264188084940943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20897260493484672906036725 1959118171264188084940943)
                      ·
                        rfl

theorem cell23_3815369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_3815369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815369 prefixEnd_3815369 := by exact prefixLift 3815369
  have htrace : WordTrace (prefixWord ++ tailWord_3815369) baseStart_3815369 baseEnd_3815369 := by
    simpa [prefixWord, tailWord_3815369, baseEnd_3815369] using wordTrace_append hprefix tailTrace_3815369
  have hstable : (prefixWord ++ tailWord_3815369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815369).length < 2 ^ (prefixWord ++ tailWord_3815369).sum := by decide
  have hdescent : baseEnd_3815369 < baseStart_3815369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815416 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 4, 3, 3]
def baseStart_3815416 : Nat := 118140960795 + 3815416 * 2 ^ 59
def prefixEnd_3815416 : Nat := 4983230072969 + 3 ^ 40 * 3815416 * 2
def baseEnd_3815416 : Nat := 1959142304854949401053227

theorem tailTrace_3815416 : CollatzResearch.WordTrace tailWord_3815416 prefixEnd_3815416 1959142304854949401053227 := by
  unfold tailWord_3815416
  simp only [CollatzResearch.WordTrace]
  refine ⟨69579826972703464009849051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92773102630271285346465401 69579826972703464009849051)
  ·
    refine ⟨104369740459055196014773577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69579826972703464009849051 104369740459055196014773577)
    ·
      refine ⟨78277305344291397011080183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104369740459055196014773577 78277305344291397011080183)
      ·
        refine ⟨117415958016437095516620275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78277305344291397011080183 117415958016437095516620275)
        ·
          refine ⟨176123937024655643274930413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117415958016437095516620275 176123937024655643274930413)
          ·
            refine ⟨66046476384245866228098905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176123937024655643274930413 66046476384245866228098905)
            ·
              refine ⟨49534857288184399671074179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66046476384245866228098905 49534857288184399671074179)
              ·
                refine ⟨74302285932276599506611269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49534857288184399671074179 74302285932276599506611269)
                ·
                  refine ⟨13931678612301862407489613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74302285932276599506611269 13931678612301862407489613)
                  ·
                    refine ⟨5224379479613198402808605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13931678612301862407489613 5224379479613198402808605)
                    ·
                      refine ⟨1959142304854949401053227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5224379479613198402808605 1959142304854949401053227)
                      ·
                        rfl

theorem cell23_3815416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_3815416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815416 prefixEnd_3815416 := by exact prefixLift 3815416
  have htrace : WordTrace (prefixWord ++ tailWord_3815416) baseStart_3815416 baseEnd_3815416 := by
    simpa [prefixWord, tailWord_3815416, baseEnd_3815416] using wordTrace_append hprefix tailTrace_3815416
  have hstable : (prefixWord ++ tailWord_3815416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815416).length < 2 ^ (prefixWord ++ tailWord_3815416).sum := by decide
  have hdescent : baseEnd_3815416 < baseStart_3815416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815436 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 4, 5]
def baseStart_3815436 : Nat := 118140960795 + 3815436 * 2 ^ 59
def prefixEnd_3815436 : Nat := 4983230072969 + 3 ^ 40 * 3815436 * 2
def baseEnd_3815436 : Nat := 653050858156013107601045

theorem tailTrace_3815436 : CollatzResearch.WordTrace tailWord_3815436 prefixEnd_3815436 653050858156013107601045 := by
  unfold tailWord_3815436
  simp only [CollatzResearch.WordTrace]
  refine ⟨69580191702667235717713081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92773588936889647623617441 69580191702667235717713081)
  ·
    refine ⟨52185143777000426788284811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69580191702667235717713081 52185143777000426788284811)
    ·
      refine ⟨78277715665500640182427217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52185143777000426788284811 78277715665500640182427217)
      ·
        refine ⟨58708286749125480136820413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78277715665500640182427217 58708286749125480136820413)
        ·
          refine ⟨22015607530922055051307655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58708286749125480136820413 22015607530922055051307655)
          ·
            refine ⟨33023411296383082576961483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22015607530922055051307655 33023411296383082576961483)
            ·
              refine ⟨49535116944574623865442225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33023411296383082576961483 49535116944574623865442225)
              ·
                refine ⟨37151337708430967899081669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49535116944574623865442225 37151337708430967899081669)
                ·
                  refine ⟨6965875820330806481077813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37151337708430967899081669 6965875820330806481077813)
                  ·
                    refine ⟨653050858156013107601045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6965875820330806481077813 653050858156013107601045)
                    ·
                      rfl

theorem cell23_3815436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_3815436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815436 prefixEnd_3815436 := by exact prefixLift 3815436
  have htrace : WordTrace (prefixWord ++ tailWord_3815436) baseStart_3815436 baseEnd_3815436 := by
    simpa [prefixWord, tailWord_3815436, baseEnd_3815436] using wordTrace_append hprefix tailTrace_3815436
  have hstable : (prefixWord ++ tailWord_3815436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815436).length < 2 ^ (prefixWord ++ tailWord_3815436).sum := by decide
  have hdescent : baseEnd_3815436 < baseStart_3815436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815453 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 2, 5]
def baseStart_3815453 : Nat := 118140960795 + 3815453 * 2 ^ 59
def prefixEnd_3815453 : Nat := 4983230072969 + 3 ^ 40 * 3815453 * 2
def baseEnd_3815453 : Nat := 653053767879721918763519

theorem tailTrace_3815453 : CollatzResearch.WordTrace tailWord_3815453 prefixEnd_3815453 653053767879721918763519 := by
  unfold tailWord_3815453
  simp only [CollatzResearch.WordTrace]
  refine ⟨139161003446272883338795013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92774002297515255559196675 139161003446272883338795013)
  ·
    refine ⟨26092688146176165626024065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139161003446272883338795013 26092688146176165626024065)
    ·
      refine ⟨19569516109632124219518049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26092688146176165626024065 19569516109632124219518049)
      ·
        refine ⟨14677137082224093164638537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19569516109632124219518049 14677137082224093164638537)
        ·
          refine ⟨11007852811668069873478903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14677137082224093164638537 11007852811668069873478903)
          ·
            refine ⟨16511779217502104810218355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11007852811668069873478903 16511779217502104810218355)
            ·
              refine ⟨24767668826253157215327533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16511779217502104810218355 24767668826253157215327533)
              ·
                refine ⟨9287875809844933955747825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24767668826253157215327533 9287875809844933955747825)
                ·
                  refine ⟨6965906857383700466810869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9287875809844933955747825 6965906857383700466810869)
                  ·
                    refine ⟨653053767879721918763519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6965906857383700466810869 653053767879721918763519)
                    ·
                      rfl

theorem cell23_3815453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_3815453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815453 prefixEnd_3815453 := by exact prefixLift 3815453
  have htrace : WordTrace (prefixWord ++ tailWord_3815453) baseStart_3815453 baseEnd_3815453 := by
    simpa [prefixWord, tailWord_3815453, baseEnd_3815453] using wordTrace_append hprefix tailTrace_3815453
  have hstable : (prefixWord ++ tailWord_3815453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815453).length < 2 ^ (prefixWord ++ tailWord_3815453).sum := by decide
  have hdescent : baseEnd_3815453 < baseStart_3815453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815473 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 2, 1, 4]
def baseStart_3815473 : Nat := 118140960795 + 3815473 * 2 ^ 59
def prefixEnd_3815473 : Nat := 4983230072969 + 3 ^ 40 * 3815473 * 2
def baseEnd_3815473 : Nat := 1959171573252255678040465

theorem tailTrace_3815473 : CollatzResearch.WordTrace tailWord_3815473 prefixEnd_3815473 1959171573252255678040465 := by
  unfold tailWord_3815473
  simp only [CollatzResearch.WordTrace]
  refine ⟨139161732906200426754523073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92774488604133617836348715 139161732906200426754523073)
  ·
    refine ⟨104371299679650320065892305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139161732906200426754523073 104371299679650320065892305)
    ·
      refine ⟨78278474759737740049419229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104371299679650320065892305 78278474759737740049419229)
      ·
        refine ⟨29354428034901652518532211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78278474759737740049419229 29354428034901652518532211)
        ·
          refine ⟨44031642052352478777798317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29354428034901652518532211 44031642052352478777798317)
          ·
            refine ⟨16511865769632179541674369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44031642052352478777798317 16511865769632179541674369)
            ·
              refine ⟨12383899327224134656255777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16511865769632179541674369 12383899327224134656255777)
              ·
                refine ⟨9287924495418100992191833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12383899327224134656255777 9287924495418100992191833)
                ·
                  refine ⟨6965943371563575744143875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9287924495418100992191833 6965943371563575744143875)
                  ·
                    refine ⟨10448915057345363616215813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6965943371563575744143875 10448915057345363616215813)
                    ·
                      refine ⟨1959171573252255678040465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10448915057345363616215813 1959171573252255678040465)
                      ·
                        rfl

theorem cell23_3815473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_3815473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815473 prefixEnd_3815473 := by exact prefixLift 3815473
  have htrace : WordTrace (prefixWord ++ tailWord_3815473) baseStart_3815473 baseEnd_3815473 := by
    simpa [prefixWord, tailWord_3815473, baseEnd_3815473] using wordTrace_append hprefix tailTrace_3815473
  have hstable : (prefixWord ++ tailWord_3815473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815473).length < 2 ^ (prefixWord ++ tailWord_3815473).sum := by decide
  have hdescent : baseEnd_3815473 < baseStart_3815473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815560 : List Nat := [2, 1, 3, 4, 1, 1, 1, 4, 1, 5]
def baseStart_3815560 : Nat := 118140960795 + 3815560 * 2 ^ 59
def prefixEnd_3815560 : Nat := 4983230072969 + 3 ^ 40 * 3815560 * 2
def baseEnd_3815560 : Nat := 653072082023065612550855

theorem tailTrace_3815560 : CollatzResearch.WordTrace tailWord_3815560 prefixEnd_3815560 653072082023065612550855 := by
  unfold tailWord_3815560
  simp only [CollatzResearch.WordTrace]
  refine ⟨69582453028442620306470067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92776604037923493741960089 69582453028442620306470067)
  ·
    refine ⟨104373679542663930459705101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69582453028442620306470067 104373679542663930459705101)
    ·
      refine ⟨39140129828498973922389413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104373679542663930459705101 39140129828498973922389413)
      ·
        refine ⟨7338774342843557610448015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39140129828498973922389413 7338774342843557610448015)
        ·
          refine ⟨11008161514265336415672023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7338774342843557610448015 11008161514265336415672023)
          ·
            refine ⟨16512242271398004623508035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11008161514265336415672023 16512242271398004623508035)
            ·
              refine ⟨24768363407097006935262053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16512242271398004623508035 24768363407097006935262053)
              ·
                refine ⟨4644068138830688800361635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24768363407097006935262053 4644068138830688800361635)
                ·
                  refine ⟨6966102208246033200542453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4644068138830688800361635 6966102208246033200542453)
                  ·
                    refine ⟨653072082023065612550855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6966102208246033200542453 653072082023065612550855)
                    ·
                      rfl

theorem cell23_3815560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_3815560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815560 prefixEnd_3815560 := by exact prefixLift 3815560
  have htrace : WordTrace (prefixWord ++ tailWord_3815560) baseStart_3815560 baseEnd_3815560 := by
    simpa [prefixWord, tailWord_3815560, baseEnd_3815560] using wordTrace_append hprefix tailTrace_3815560
  have hstable : (prefixWord ++ tailWord_3815560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815560).length < 2 ^ (prefixWord ++ tailWord_3815560).sum := by decide
  have hdescent : baseEnd_3815560 < baseStart_3815560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815573 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 6, 4]
def baseStart_3815573 : Nat := 118140960795 + 3815573 * 2 ^ 59
def prefixEnd_3815573 : Nat := 4983230072969 + 3 ^ 40 * 3815573 * 2
def baseEnd_3815573 : Nat := 653074307105901762263335

theorem tailTrace_3815573 : CollatzResearch.WordTrace tailWord_3815573 prefixEnd_3815573 653074307105901762263335 := by
  unfold tailWord_3815573
  simp only [CollatzResearch.WordTrace]
  refine ⟨139165380205838143833163373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92776920137225429222108915 139165380205838143833163373)
  ·
    refine ⟨52187017577189303937436265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139165380205838143833163373 52187017577189303937436265)
    ·
      refine ⟨39140263182891977953077199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52187017577189303937436265 39140263182891977953077199)
      ·
        refine ⟨58710394774337966929615799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39140263182891977953077199 58710394774337966929615799)
        ·
          refine ⟨88065592161506950394423699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58710394774337966929615799 88065592161506950394423699)
          ·
            refine ⟨132098388242260425591635549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88065592161506950394423699 132098388242260425591635549)
            ·
              refine ⟨49536895590847659596863331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132098388242260425591635549 49536895590847659596863331)
              ·
                refine ⟨74305343386271489395294997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49536895590847659596863331 74305343386271489395294997)
                ·
                  refine ⟨3483062971231476065404453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74305343386271489395294997 3483062971231476065404453)
                  ·
                    refine ⟨653074307105901762263335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3483062971231476065404453 653074307105901762263335)
                    ·
                      rfl

theorem cell23_3815573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_3815573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815573 prefixEnd_3815573 := by exact prefixLift 3815573
  have htrace : WordTrace (prefixWord ++ tailWord_3815573) baseStart_3815573 baseEnd_3815573 := by
    simpa [prefixWord, tailWord_3815573, baseEnd_3815573] using wordTrace_append hprefix tailTrace_3815573
  have hstable : (prefixWord ++ tailWord_3815573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815573).length < 2 ^ (prefixWord ++ tailWord_3815573).sum := by decide
  have hdescent : baseEnd_3815573 < baseStart_3815573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815580 : List Nat := [2, 2, 3, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_3815580 : Nat := 118140960795 + 3815580 * 2 ^ 59
def prefixEnd_3815580 : Nat := 4983230072969 + 3 ^ 40 * 3815580 * 2
def baseEnd_3815580 : Nat := 1959226515682286759402473

theorem tailTrace_3815580 : CollatzResearch.WordTrace tailWord_3815580 prefixEnd_3815580 1959226515682286759402473 := by
  unfold tailWord_3815580
  simp only [CollatzResearch.WordTrace]
  refine ⟨69582817758406392014334097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92777090344541856019112129 69582817758406392014334097)
  ·
    refine ⟨52187113318804794010750573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69582817758406392014334097 52187113318804794010750573)
    ·
      refine ⟨19570167494551797754031465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52187113318804794010750573 19570167494551797754031465)
      ·
        refine ⟨14677625620913848315523599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19570167494551797754031465 14677625620913848315523599)
        ·
          refine ⟨22016438431370772473285399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14677625620913848315523599 22016438431370772473285399)
          ·
            refine ⟨33024657647056158709928099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22016438431370772473285399 33024657647056158709928099)
            ·
              refine ⟨49536986470584238064892149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33024657647056158709928099 49536986470584238064892149)
              ·
                refine ⟨4644092481617272318583639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49536986470584238064892149 4644092481617272318583639)
                ·
                  refine ⟨6966138722425908477875459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4644092481617272318583639 6966138722425908477875459)
                  ·
                    refine ⟨10449208083638862716813189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6966138722425908477875459 10449208083638862716813189)
                    ·
                      refine ⟨1959226515682286759402473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10449208083638862716813189 1959226515682286759402473)
                      ·
                        rfl

theorem cell23_3815580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_3815580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815580 prefixEnd_3815580 := by exact prefixLift 3815580
  have htrace : WordTrace (prefixWord ++ tailWord_3815580) baseStart_3815580 baseEnd_3815580 := by
    simpa [prefixWord, tailWord_3815580, baseEnd_3815580] using wordTrace_append hprefix tailTrace_3815580
  have hstable : (prefixWord ++ tailWord_3815580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815580).length < 2 ^ (prefixWord ++ tailWord_3815580).sum := by decide
  have hdescent : baseEnd_3815580 < baseStart_3815580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815591 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_3815591 : Nat := 118140960795 + 3815591 * 2 ^ 59
def prefixEnd_3815591 : Nat := 4983230072969 + 3 ^ 40 * 3815591 * 2
def baseEnd_3815591 : Nat := 1959232163969486216364923

theorem tailTrace_3815591 : CollatzResearch.WordTrace tailWord_3815591 prefixEnd_3815591 1959232163969486216364923 := by
  unfold tailWord_3815591
  simp only [CollatzResearch.WordTrace]
  refine ⟨139166036719772932907318627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92777357813181955271545751 139166036719772932907318627)
  ·
    refine ⟨208749055079659399360977941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139166036719772932907318627 208749055079659399360977941)
    ·
      refine ⟨9785111956859034345045841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 208749055079659399360977941 9785111956859034345045841)
      ·
        refine ⟨7338833967644275758784381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9785111956859034345045841 7338833967644275758784381)
        ·
          refine ⟨2752062737866603409544143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7338833967644275758784381 2752062737866603409544143)
          ·
            refine ⟨4128094106799905114316215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2752062737866603409544143 4128094106799905114316215)
            ·
              refine ⟨6192141160199857671474323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4128094106799905114316215 6192141160199857671474323)
              ·
                refine ⟨9288211740299786507211485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6192141160199857671474323 9288211740299786507211485)
                ·
                  refine ⟨3483079402612419940204307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9288211740299786507211485 3483079402612419940204307)
                  ·
                    refine ⟨5224619103918629910306461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3483079402612419940204307 5224619103918629910306461)
                    ·
                      refine ⟨1959232163969486216364923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5224619103918629910306461 1959232163969486216364923)
                      ·
                        rfl

theorem cell23_3815591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_3815591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815591 prefixEnd_3815591 := by exact prefixLift 3815591
  have htrace : WordTrace (prefixWord ++ tailWord_3815591) baseStart_3815591 baseEnd_3815591 := by
    simpa [prefixWord, tailWord_3815591, baseEnd_3815591] using wordTrace_append hprefix tailTrace_3815591
  have hstable : (prefixWord ++ tailWord_3815591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815591).length < 2 ^ (prefixWord ++ tailWord_3815591).sum := by decide
  have hdescent : baseEnd_3815591 < baseStart_3815591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815607 : List Nat := [1, 1, 3, 1, 4, 2, 4, 1, 2, 4]
def baseStart_3815607 : Nat := 118140960795 + 3815607 * 2 ^ 59
def prefixEnd_3815607 : Nat := 4983230072969 + 3 ^ 40 * 3815607 * 2
def baseEnd_3815607 : Nat := 653080126553319384588283

theorem tailTrace_3815607 : CollatzResearch.WordTrace tailWord_3815607 prefixEnd_3815607 653080126553319384588283 := by
  unfold tailWord_3815607
  simp only [CollatzResearch.WordTrace]
  refine ⟨139166620287714967639901075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92777746858476645093267383 139166620287714967639901075)
  ·
    refine ⟨208749930431572451459851613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139166620287714967639901075 208749930431572451459851613)
    ·
      refine ⟨78281223911839669297444355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208749930431572451459851613 78281223911839669297444355)
      ·
        refine ⟨117421835867759503946166533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78281223911839669297444355 117421835867759503946166533)
        ·
          refine ⟨22016594225204906989906225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117421835867759503946166533 22016594225204906989906225)
          ·
            refine ⟨16512445668903680242429669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22016594225204906989906225 16512445668903680242429669)
            ·
              refine ⟨3096083562919440045455563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16512445668903680242429669 3096083562919440045455563)
              ·
                refine ⟨4644125344379160068183345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3096083562919440045455563 4644125344379160068183345)
                ·
                  refine ⟨3483094008284370051137509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4644125344379160068183345 3483094008284370051137509)
                  ·
                    refine ⟨653080126553319384588283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3483094008284370051137509 653080126553319384588283)
                    ·
                      rfl

theorem cell23_3815607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_3815607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815607 prefixEnd_3815607 := by exact prefixLift 3815607
  have htrace : WordTrace (prefixWord ++ tailWord_3815607) baseStart_3815607 baseEnd_3815607 := by
    simpa [prefixWord, tailWord_3815607, baseEnd_3815607] using wordTrace_append hprefix tailTrace_3815607
  have hstable : (prefixWord ++ tailWord_3815607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815607).length < 2 ^ (prefixWord ++ tailWord_3815607).sum := by decide
  have hdescent : baseEnd_3815607 < baseStart_3815607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815614 : List Nat := [4, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_3815614 : Nat := 118140960795 + 3815614 * 2 ^ 59
def prefixEnd_3815614 : Nat := 4983230072969 + 3 ^ 40 * 3815614 * 2
def baseEnd_3815614 : Nat := 1959243974024539626377317

theorem tailTrace_3815614 : CollatzResearch.WordTrace tailWord_3815614 prefixEnd_3815614 1959243974024539626377317 := by
  unfold tailWord_3815614
  simp only [CollatzResearch.WordTrace]
  refine ⟨17395859449836200979425737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92777917065793071890270597 17395859449836200979425737)
  ·
    refine ⟨13046894587377150734569303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17395859449836200979425737 13046894587377150734569303)
    ·
      refine ⟨19570341881065726101853955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13046894587377150734569303 19570341881065726101853955)
      ·
        refine ⟨29355512821598589152780933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19570341881065726101853955 29355512821598589152780933)
        ·
          refine ⟨5504158654049735466146425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29355512821598589152780933 5504158654049735466146425)
          ·
            refine ⟨4128118990537301599609819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5504158654049735466146425 4128118990537301599609819)
            ·
              refine ⟨6192178485805952399414729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4128118990537301599609819 6192178485805952399414729)
              ·
                refine ⟨4644133864354464299561047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6192178485805952399414729 4644133864354464299561047)
                ·
                  refine ⟨6966200796531696449341571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4644133864354464299561047 6966200796531696449341571)
                  ·
                    refine ⟨10449301194797544674012357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6966200796531696449341571 10449301194797544674012357)
                    ·
                      refine ⟨1959243974024539626377317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10449301194797544674012357 1959243974024539626377317)
                      ·
                        rfl

theorem cell23_3815614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_3815614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815614 prefixEnd_3815614 := by exact prefixLift 3815614
  have htrace : WordTrace (prefixWord ++ tailWord_3815614) baseStart_3815614 baseEnd_3815614 := by
    simpa [prefixWord, tailWord_3815614, baseEnd_3815614] using wordTrace_append hprefix tailTrace_3815614
  have hstable : (prefixWord ++ tailWord_3815614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815614).length < 2 ^ (prefixWord ++ tailWord_3815614).sum := by decide
  have hdescent : baseEnd_3815614 < baseStart_3815614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815630 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3]
def baseStart_3815630 : Nat := 118140960795 + 3815630 * 2 ^ 59
def prefixEnd_3815630 : Nat := 4983230072969 + 3 ^ 40 * 3815630 * 2
def baseEnd_3815630 : Nat := 1959252189715011563777243

theorem tailTrace_3815630 : CollatzResearch.WordTrace tailWord_3815630 prefixEnd_3815630 1959252189715011563777243 := by
  unfold tailWord_3815630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17395932395828955320998543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92778306111087761711992229 17395932395828955320998543)
  ·
    refine ⟨26093898593743432981497815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17395932395828955320998543 26093898593743432981497815)
    ·
      refine ⟨39140847890615149472246723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26093898593743432981497815 39140847890615149472246723)
      ·
        refine ⟨58711271835922724208370085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39140847890615149472246723 58711271835922724208370085)
        ·
          refine ⟨11008363469235510789069391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58711271835922724208370085 11008363469235510789069391)
          ·
            refine ⟨16512545203853266183604087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11008363469235510789069391 16512545203853266183604087)
            ·
              refine ⟨24768817805779899275406131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16512545203853266183604087 24768817805779899275406131)
              ·
                refine ⟨37153226708669848913109197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24768817805779899275406131 37153226708669848913109197)
                ·
                  refine ⟨13932460015751193342415949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37153226708669848913109197 13932460015751193342415949)
                  ·
                    refine ⟨5224672505906697503405981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13932460015751193342415949 5224672505906697503405981)
                    ·
                      refine ⟨1959252189715011563777243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5224672505906697503405981 1959252189715011563777243)
                      ·
                        rfl

theorem cell23_3815630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_3815630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815630 prefixEnd_3815630 := by exact prefixLift 3815630
  have htrace : WordTrace (prefixWord ++ tailWord_3815630) baseStart_3815630 baseEnd_3815630 := by
    simpa [prefixWord, tailWord_3815630, baseEnd_3815630] using wordTrace_append hprefix tailTrace_3815630
  have hstable : (prefixWord ++ tailWord_3815630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815630).length < 2 ^ (prefixWord ++ tailWord_3815630).sum := by decide
  have hdescent : baseEnd_3815630 < baseStart_3815630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815634 : List Nat := [3, 2, 2, 2, 1, 3, 3, 1, 1, 2, 3]
def baseStart_3815634 : Nat := 118140960795 + 3815634 * 2 ^ 59
def prefixEnd_3815634 : Nat := 4983230072969 + 3 ^ 40 * 3815634 * 2
def baseEnd_3815634 : Nat := 1959254243637629548127225

theorem tailTrace_3815634 : CollatzResearch.WordTrace tailWord_3815634 prefixEnd_3815634 1959254243637629548127225 := by
  unfold tailWord_3815634
  simp only [CollatzResearch.WordTrace]
  refine ⟨34791901264654287812783489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92778403372411434167422637 34791901264654287812783489)
  ·
    refine ⟨26093925948490715859587617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34791901264654287812783489 26093925948490715859587617)
    ·
      refine ⟨19570444461368036894690713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26093925948490715859587617 19570444461368036894690713)
      ·
        refine ⟨14677833346026027671018035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19570444461368036894690713 14677833346026027671018035)
        ·
          refine ⟨22016750019039041506527053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14677833346026027671018035 22016750019039041506527053)
          ·
            refine ⟨8256281257139640564947645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22016750019039041506527053 8256281257139640564947645)
            ·
              refine ⟨3096105471427365211855367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8256281257139640564947645 3096105471427365211855367)
              ·
                refine ⟨4644158207141047817783051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3096105471427365211855367 4644158207141047817783051)
                ·
                  refine ⟨6966237310711571726674577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4644158207141047817783051 6966237310711571726674577)
                  ·
                    refine ⟨5224677983033678795005933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6966237310711571726674577 5224677983033678795005933)
                    ·
                      refine ⟨1959254243637629548127225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5224677983033678795005933 1959254243637629548127225)
                      ·
                        rfl

theorem cell23_3815634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_3815634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815634 prefixEnd_3815634 := by exact prefixLift 3815634
  have htrace : WordTrace (prefixWord ++ tailWord_3815634) baseStart_3815634 baseEnd_3815634 := by
    simpa [prefixWord, tailWord_3815634, baseEnd_3815634] using wordTrace_append hprefix tailTrace_3815634
  have hstable : (prefixWord ++ tailWord_3815634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815634).length < 2 ^ (prefixWord ++ tailWord_3815634).sum := by decide
  have hdescent : baseEnd_3815634 < baseStart_3815634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815663 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 1, 8]
def baseStart_3815663 : Nat := 118140960795 + 3815663 * 2 ^ 59
def prefixEnd_3815663 : Nat := 4983230072969 + 3 ^ 40 * 3815663 * 2
def baseEnd_3815663 : Nat := 653089711525536644888197

theorem tailTrace_3815663 : CollatzResearch.WordTrace tailWord_3815663 prefixEnd_3815663 653089711525536644888197 := by
  unfold tailWord_3815663
  simp only [CollatzResearch.WordTrace]
  refine ⟨139168662775512089203939643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92779108517008059469293095 139168662775512089203939643)
  ·
    refine ⟨208752994163268133805909465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139168662775512089203939643 208752994163268133805909465)
    ·
      refine ⟨156564745622451100354432099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208752994163268133805909465 156564745622451100354432099)
      ·
        refine ⟨234847118433676650531648149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156564745622451100354432099 234847118433676650531648149)
        ·
          refine ⟨11008458676578592993671007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 234847118433676650531648149 11008458676578592993671007)
          ·
            refine ⟨16512688014867889490506511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11008458676578592993671007 16512688014867889490506511)
            ·
              refine ⟨24769032022301834235759767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16512688014867889490506511 24769032022301834235759767)
              ·
                refine ⟨37153548033452751353639651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24769032022301834235759767 37153548033452751353639651)
                ·
                  refine ⟨55730322050179127030459477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37153548033452751353639651 55730322050179127030459477)
                  ·
                    refine ⟨653089711525536644888197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55730322050179127030459477 653089711525536644888197)
                    ·
                      rfl

theorem cell23_3815663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 8].length) (baseStart_3815663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815663 prefixEnd_3815663 := by exact prefixLift 3815663
  have htrace : WordTrace (prefixWord ++ tailWord_3815663) baseStart_3815663 baseEnd_3815663 := by
    simpa [prefixWord, tailWord_3815663, baseEnd_3815663] using wordTrace_append hprefix tailTrace_3815663
  have hstable : (prefixWord ++ tailWord_3815663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815663).length < 2 ^ (prefixWord ++ tailWord_3815663).sum := by decide
  have hdescent : baseEnd_3815663 < baseStart_3815663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815673 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 2, 1, 5]
def baseStart_3815673 : Nat := 118140960795 + 3815673 * 2 ^ 59
def prefixEnd_3815673 : Nat := 4983230072969 + 3 ^ 40 * 3815673 * 2
def baseEnd_3815673 : Nat := 1959274269383154895539545

theorem tailTrace_3815673 : CollatzResearch.WordTrace tailWord_3815673 prefixEnd_3815673 1959274269383154895539545 := by
  unfold tailWord_3815673
  simp only [CollatzResearch.WordTrace]
  refine ⟨139169027505475860911803673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92779351670317240607869115 139169027505475860911803673)
  ·
    refine ⟨104376770629106895683852755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139169027505475860911803673 104376770629106895683852755)
    ·
      refine ⟨156565155943660343525779133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104376770629106895683852755 156565155943660343525779133)
      ·
        refine ⟨58711933478872628822167175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156565155943660343525779133 58711933478872628822167175)
        ·
          refine ⟨88067900218308943233250763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58711933478872628822167175 88067900218308943233250763)
          ·
            refine ⟨132101850327463414849876145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88067900218308943233250763 132101850327463414849876145)
            ·
              refine ⟨99076387745597561137407109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132101850327463414849876145 99076387745597561137407109)
              ·
                refine ⟨18576822702299542713263833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99076387745597561137407109 18576822702299542713263833)
                ·
                  refine ⟨13932617026724657034947875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18576822702299542713263833 13932617026724657034947875)
                  ·
                    refine ⟨20898925540086985552421813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13932617026724657034947875 20898925540086985552421813)
                    ·
                      refine ⟨1959274269383154895539545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20898925540086985552421813 1959274269383154895539545)
                      ·
                        rfl

theorem cell23_3815673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_3815673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815673 prefixEnd_3815673 := by exact prefixLift 3815673
  have htrace : WordTrace (prefixWord ++ tailWord_3815673) baseStart_3815673 baseEnd_3815673 := by
    simpa [prefixWord, tailWord_3815673, baseEnd_3815673] using wordTrace_append hprefix tailTrace_3815673
  have hstable : (prefixWord ++ tailWord_3815673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815673).length < 2 ^ (prefixWord ++ tailWord_3815673).sum := by decide
  have hdescent : baseEnd_3815673 < baseStart_3815673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815683 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 4]
def baseStart_3815683 : Nat := 118140960795 + 3815683 * 2 ^ 59
def prefixEnd_3815683 : Nat := 4983230072969 + 3 ^ 40 * 3815683 * 2
def baseEnd_3815683 : Nat := 1959279404189699856414499

theorem tailTrace_3815683 : CollatzResearch.WordTrace tailWord_3815683 prefixEnd_3815683 1959279404189699856414499 := by
  unfold tailWord_3815683
  simp only [CollatzResearch.WordTrace]
  refine ⟨139169392235439632619667703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92779594823626421746445135 139169392235439632619667703)
  ·
    refine ⟨208754088353159448929501555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139169392235439632619667703 208754088353159448929501555)
    ·
      refine ⟨313131132529739173394252333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208754088353159448929501555 313131132529739173394252333)
      ·
        refine ⟨117424174698652190022844625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313131132529739173394252333 117424174698652190022844625)
        ·
          refine ⟨88068131023989142517133469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117424174698652190022844625 88068131023989142517133469)
          ·
            refine ⟨33025549133995928443925051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88068131023989142517133469 33025549133995928443925051)
            ·
              refine ⟨49538323700993892665887577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33025549133995928443925051 49538323700993892665887577)
              ·
                refine ⟨37153742775745419499415683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49538323700993892665887577 37153742775745419499415683)
                ·
                  refine ⟨55730614163618129249123525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37153742775745419499415683 55730614163618129249123525)
                  ·
                    refine ⟨10449490155678399234210661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55730614163618129249123525 10449490155678399234210661)
                    ·
                      refine ⟨1959279404189699856414499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10449490155678399234210661 1959279404189699856414499)
                      ·
                        rfl

theorem cell23_3815683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_3815683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815683 prefixEnd_3815683 := by exact prefixLift 3815683
  have htrace : WordTrace (prefixWord ++ tailWord_3815683) baseStart_3815683 baseEnd_3815683 := by
    simpa [prefixWord, tailWord_3815683, baseEnd_3815683] using wordTrace_append hprefix tailTrace_3815683
  have hstable : (prefixWord ++ tailWord_3815683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815683).length < 2 ^ (prefixWord ++ tailWord_3815683).sum := by decide
  have hdescent : baseEnd_3815683 < baseStart_3815683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815740 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 2, 5]
def baseStart_3815740 : Nat := 118140960795 + 3815740 * 2 ^ 59
def prefixEnd_3815740 : Nat := 4983230072969 + 3 ^ 40 * 3815740 * 2
def baseEnd_3815740 : Nat := 653102890862335377800579

theorem tailTrace_3815740 : CollatzResearch.WordTrace tailWord_3815740 prefixEnd_3815740 653102890862335377800579 := by
  unfold tailWord_3815740
  simp only [CollatzResearch.WordTrace]
  refine ⟨69585735598116565677246337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92780980797488754236328449 69585735598116565677246337)
  ·
    refine ⟨52189301698587424257934753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69585735598116565677246337 52189301698587424257934753)
    ·
      refine ⟨39141976273940568193451065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52189301698587424257934753 39141976273940568193451065)
      ·
        refine ⟨29356482205455426145088299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39141976273940568193451065 29356482205455426145088299)
        ·
          refine ⟨44034723308183139217632449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29356482205455426145088299 44034723308183139217632449)
          ·
            refine ⟨33026042481137354413224337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44034723308183139217632449 33026042481137354413224337)
            ·
              refine ⟨24769531860853015809918253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33026042481137354413224337 24769531860853015809918253)
              ·
                refine ⟨9288574447819880928719345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24769531860853015809918253 9288574447819880928719345)
                ·
                  refine ⟨6966430835864910696539509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9288574447819880928719345 6966430835864910696539509)
                  ·
                    refine ⟨653102890862335377800579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6966430835864910696539509 653102890862335377800579)
                    ·
                      rfl

theorem cell23_3815740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_3815740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815740 prefixEnd_3815740 := by exact prefixLift 3815740
  have htrace : WordTrace (prefixWord ++ tailWord_3815740) baseStart_3815740 baseEnd_3815740 := by
    simpa [prefixWord, tailWord_3815740, baseEnd_3815740] using wordTrace_append hprefix tailTrace_3815740
  have hstable : (prefixWord ++ tailWord_3815740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815740).length < 2 ^ (prefixWord ++ tailWord_3815740).sum := by decide
  have hdescent : baseEnd_3815740 < baseStart_3815740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815760 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 4]
def baseStart_3815760 : Nat := 118140960795 + 3815760 * 2 ^ 59
def prefixEnd_3815760 : Nat := 4983230072969 + 3 ^ 40 * 3815760 * 2
def baseEnd_3815760 : Nat := 1959318942200096055151645

theorem tailTrace_3815760 : CollatzResearch.WordTrace tailWord_3815760 prefixEnd_3815760 1959318942200096055151645 := by
  unfold tailWord_3815760
  simp only [CollatzResearch.WordTrace]
  refine ⟨69586100328080337385110367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92781467104107116513480489 69586100328080337385110367)
  ·
    refine ⟨104379150492120506077665551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69586100328080337385110367 104379150492120506077665551)
    ·
      refine ⟨156568725738180759116498327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104379150492120506077665551 156568725738180759116498327)
      ·
        refine ⟨234853088607271138674747491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156568725738180759116498327 234853088607271138674747491)
        ·
          refine ⟨352279632910906708012121237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234853088607271138674747491 352279632910906708012121237)
          ·
            refine ⟨16513107792698751938068183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 352279632910906708012121237 16513107792698751938068183)
            ·
              refine ⟨24769661689048127907102275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16513107792698751938068183 24769661689048127907102275)
              ·
                refine ⟨37154492533572191860653413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24769661689048127907102275 37154492533572191860653413)
                ·
                  refine ⟨6966467350044785973872515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37154492533572191860653413 6966467350044785973872515)
                  ·
                    refine ⟨10449701025067178960808773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6966467350044785973872515 10449701025067178960808773)
                    ·
                      refine ⟨1959318942200096055151645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10449701025067178960808773 1959318942200096055151645)
                      ·
                        rfl

theorem cell23_3815760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 4].length) (baseStart_3815760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815760 prefixEnd_3815760 := by exact prefixLift 3815760
  have htrace : WordTrace (prefixWord ++ tailWord_3815760) baseStart_3815760 baseEnd_3815760 := by
    simpa [prefixWord, tailWord_3815760, baseEnd_3815760] using wordTrace_append hprefix tailTrace_3815760
  have hstable : (prefixWord ++ tailWord_3815760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815760).length < 2 ^ (prefixWord ++ tailWord_3815760).sum := by decide
  have hdescent : baseEnd_3815760 < baseStart_3815760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815763 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 5]
def baseStart_3815763 : Nat := 118140960795 + 3815763 * 2 ^ 59
def prefixEnd_3815763 : Nat := 4983230072969 + 3 ^ 40 * 3815763 * 2
def baseEnd_3815763 : Nat := 1959320482642059543414131

theorem tailTrace_3815763 : CollatzResearch.WordTrace tailWord_3815763 prefixEnd_3815763 1959320482642059543414131 := by
  unfold tailWord_3815763
  simp only [CollatzResearch.WordTrace]
  refine ⟨139172310075149806282579943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92781540050099870855053295 139172310075149806282579943)
  ·
    refine ⟨208758465112724709423869915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139172310075149806282579943 208758465112724709423869915)
    ·
      refine ⟨313137697669087064135804873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208758465112724709423869915 313137697669087064135804873)
      ·
        refine ⟨234853273251815298101853655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313137697669087064135804873 234853273251815298101853655)
        ·
          refine ⟨352279909877722947152780483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234853273251815298101853655 352279909877722947152780483)
          ·
            refine ⟨528419864816584420729170725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352279909877722947152780483 528419864816584420729170725)
            ·
              refine ⟨99078724653109578886719511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 528419864816584420729170725 99078724653109578886719511)
              ·
                refine ⟨148618086979664368330079267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99078724653109578886719511 148618086979664368330079267)
                ·
                  refine ⟨222927130469496552495118901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148618086979664368330079267 222927130469496552495118901)
                  ·
                    refine ⟨20899418481515301796417397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 222927130469496552495118901 20899418481515301796417397)
                    ·
                      refine ⟨1959320482642059543414131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20899418481515301796417397 1959320482642059543414131)
                      ·
                        rfl

theorem cell23_3815763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_3815763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815763 prefixEnd_3815763 := by exact prefixLift 3815763
  have htrace : WordTrace (prefixWord ++ tailWord_3815763) baseStart_3815763 baseEnd_3815763 := by
    simpa [prefixWord, tailWord_3815763, baseEnd_3815763] using wordTrace_append hprefix tailTrace_3815763
  have hstable : (prefixWord ++ tailWord_3815763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815763).length < 2 ^ (prefixWord ++ tailWord_3815763).sum := by decide
  have hdescent : baseEnd_3815763 < baseStart_3815763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815772 : List Nat := [2, 2, 4, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_3815772 : Nat := 118140960795 + 3815772 * 2 ^ 59
def prefixEnd_3815772 : Nat := 4983230072969 + 3 ^ 40 * 3815772 * 2
def baseEnd_3815772 : Nat := 1959325103967950008201591

theorem tailTrace_3815772 : CollatzResearch.WordTrace tailWord_3815772 prefixEnd_3815772 1959325103967950008201591 := by
  unfold tailWord_3815772
  simp only [CollatzResearch.WordTrace]
  refine ⟨69586319166058600409828785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92781758888078133879771713 69586319166058600409828785)
  ·
    refine ⟨52189739374543950307371589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69586319166058600409828785 52189739374543950307371589)
    ·
      refine ⟨9785576132726990682632173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52189739374543950307371589 9785576132726990682632173)
      ·
        refine ⟨3669591049772621505987065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9785576132726990682632173 3669591049772621505987065)
        ·
          refine ⟨2752193287329466129490299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3669591049772621505987065 2752193287329466129490299)
          ·
            refine ⟨4128289930994199194235449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2752193287329466129490299 4128289930994199194235449)
            ·
              refine ⟨3096217448245649395676587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4128289930994199194235449 3096217448245649395676587)
              ·
                refine ⟨4644326172368474093514881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3096217448245649395676587 4644326172368474093514881)
                ·
                  refine ⟨3483244629276355570136161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4644326172368474093514881 3483244629276355570136161)
                  ·
                    refine ⟨2612433471957266677602121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3483244629276355570136161 2612433471957266677602121)
                    ·
                      refine ⟨1959325103967950008201591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2612433471957266677602121 1959325103967950008201591)
                      ·
                        rfl

theorem cell23_3815772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_3815772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815772 prefixEnd_3815772 := by exact prefixLift 3815772
  have htrace : WordTrace (prefixWord ++ tailWord_3815772) baseStart_3815772 baseEnd_3815772 := by
    simpa [prefixWord, tailWord_3815772, baseEnd_3815772] using wordTrace_append hprefix tailTrace_3815772
  have hstable : (prefixWord ++ tailWord_3815772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815772).length < 2 ^ (prefixWord ++ tailWord_3815772).sum := by decide
  have hdescent : baseEnd_3815772 < baseStart_3815772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815817 : List Nat := [1, 2, 1, 1, 6, 2, 2, 2, 6]
def baseStart_3815817 : Nat := 118140960795 + 3815817 * 2 ^ 59
def prefixEnd_3815817 : Nat := 4983230072969 + 3 ^ 40 * 3815817 * 2
def baseEnd_3815817 : Nat := 217705356733044703570987

theorem tailTrace_3815817 : CollatzResearch.WordTrace tailWord_3815817 prefixEnd_3815817 217705356733044703570987 := by
  unfold tailWord_3815817
  simp only [CollatzResearch.WordTrace]
  refine ⟨139174279616954173505045705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92782853077969449003363803 139174279616954173505045705)
  ·
    refine ⟨104380709712715630128784279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139174279616954173505045705 104380709712715630128784279)
    ·
      refine ⟨156571064569073445193176419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104380709712715630128784279 156571064569073445193176419)
      ·
        refine ⟨234856596853610167789764629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156571064569073445193176419 234856596853610167789764629)
        ·
          refine ⟨11008902977512976615145217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 234856596853610167789764629 11008902977512976615145217)
          ·
            refine ⟨8256677233134732461358913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11008902977512976615145217 8256677233134732461358913)
            ·
              refine ⟨6192507924851049346019185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8256677233134732461358913 6192507924851049346019185)
              ·
                refine ⟨4644380943638287009514389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6192507924851049346019185 4644380943638287009514389)
                ·
                  refine ⟨217705356733044703570987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4644380943638287009514389 217705356733044703570987)
                  ·
                    rfl

theorem cell23_3815817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 6].length) (baseStart_3815817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815817 prefixEnd_3815817 := by exact prefixLift 3815817
  have htrace : WordTrace (prefixWord ++ tailWord_3815817) baseStart_3815817 baseEnd_3815817 := by
    simpa [prefixWord, tailWord_3815817, baseEnd_3815817] using wordTrace_append hprefix tailTrace_3815817
  have hstable : (prefixWord ++ tailWord_3815817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815817).length < 2 ^ (prefixWord ++ tailWord_3815817).sum := by decide
  have hdescent : baseEnd_3815817 < baseStart_3815817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815847 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 3, 5]
def baseStart_3815847 : Nat := 118140960795 + 3815847 * 2 ^ 59
def prefixEnd_3815847 : Nat := 4983230072969 + 3 ^ 40 * 3815847 * 2
def baseEnd_3815847 : Nat := 653121205005679071587915

theorem tailTrace_3815847 : CollatzResearch.WordTrace tailWord_3815847 prefixEnd_3815847 653121205005679071587915 := by
  unfold tailWord_3815847
  simp only [CollatzResearch.WordTrace]
  refine ⟨139175373806845488628637795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92783582537896992419091863 139175373806845488628637795)
  ·
    refine ⟨208763060710268232942956693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139175373806845488628637795 208763060710268232942956693)
    ·
      refine ⟨9785768470793823419201095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 208763060710268232942956693 9785768470793823419201095)
      ·
        refine ⟨14678652706190735128801643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9785768470793823419201095 14678652706190735128801643)
        ·
          refine ⟨22017979059286102693202465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14678652706190735128801643 22017979059286102693202465)
          ·
            refine ⟨16513484294464577019901849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22017979059286102693202465 16513484294464577019901849)
            ·
              refine ⟨12385113220848432764926387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16513484294464577019901849 12385113220848432764926387)
              ·
                refine ⟨18577669831272649147389581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12385113220848432764926387 18577669831272649147389581)
                ·
                  refine ⟨6966626186727243430271093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18577669831272649147389581 6966626186727243430271093)
                  ·
                    refine ⟨653121205005679071587915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6966626186727243430271093 653121205005679071587915)
                    ·
                      rfl

theorem cell23_3815847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_3815847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815847 prefixEnd_3815847 := by exact prefixLift 3815847
  have htrace : WordTrace (prefixWord ++ tailWord_3815847) baseStart_3815847 baseEnd_3815847 := by
    simpa [prefixWord, tailWord_3815847, baseEnd_3815847] using wordTrace_append hprefix tailTrace_3815847
  have hstable : (prefixWord ++ tailWord_3815847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815847).length < 2 ^ (prefixWord ++ tailWord_3815847).sum := by decide
  have hdescent : baseEnd_3815847 < baseStart_3815847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815901 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_3815901 : Nat := 118140960795 + 3815901 * 2 ^ 59
def prefixEnd_3815901 : Nat := 4983230072969 + 3 ^ 40 * 3815901 * 2
def baseEnd_3815901 : Nat := 1959391342972380003488497

theorem tailTrace_3815901 : CollatzResearch.WordTrace tailWord_3815901 prefixEnd_3815901 1959391342972380003488497 := by
  unfold tailWord_3815901
  simp only [CollatzResearch.WordTrace]
  refine ⟨139177343348649855851103557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92784895565766570567402371 139177343348649855851103557)
  ·
    refine ⟨26095751877871847972081917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139177343348649855851103557 26095751877871847972081917)
    ·
      refine ⟨9785906954201942989530719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26095751877871847972081917 9785906954201942989530719)
      ·
        refine ⟨14678860431302914484296079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9785906954201942989530719 14678860431302914484296079)
        ·
          refine ⟨22018290646954371726444119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14678860431302914484296079 22018290646954371726444119)
          ·
            refine ⟨33027435970431557589666179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22018290646954371726444119 33027435970431557589666179)
            ·
              refine ⟨49541153955647336384499269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33027435970431557589666179 49541153955647336384499269)
              ·
                refine ⟨9288966366683875572093613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49541153955647336384499269 9288966366683875572093613)
                ·
                  refine ⟨3483362387506453339535105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9288966366683875572093613 3483362387506453339535105)
                  ·
                    refine ⟨2612521790629840004651329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3483362387506453339535105 2612521790629840004651329)
                    ·
                      refine ⟨1959391342972380003488497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2612521790629840004651329 1959391342972380003488497)
                      ·
                        rfl

theorem cell23_3815901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_3815901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815901 prefixEnd_3815901 := by exact prefixLift 3815901
  have htrace : WordTrace (prefixWord ++ tailWord_3815901) baseStart_3815901 baseEnd_3815901 := by
    simpa [prefixWord, tailWord_3815901, baseEnd_3815901] using wordTrace_append hprefix tailTrace_3815901
  have hstable : (prefixWord ++ tailWord_3815901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815901).length < 2 ^ (prefixWord ++ tailWord_3815901).sum := by decide
  have hdescent : baseEnd_3815901 < baseStart_3815901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815904 : List Nat := [2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 3]
def baseStart_3815904 : Nat := 118140960795 + 3815904 * 2 ^ 59
def prefixEnd_3815904 : Nat := 4983230072969 + 3 ^ 40 * 3815904 * 2
def baseEnd_3815904 : Nat := 1959392883414343491750983

theorem tailTrace_3815904 : CollatzResearch.WordTrace tailWord_3815904 prefixEnd_3815904 1959392883414343491750983 := by
  unfold tailWord_3815904
  simp only [CollatzResearch.WordTrace]
  refine ⟨69588726383819493681731383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92784968511759324908975177 69588726383819493681731383)
  ·
    refine ⟨104383089575729240522597075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69588726383819493681731383 104383089575729240522597075)
    ·
      refine ⟨156574634363593860783895613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104383089575729240522597075 156574634363593860783895613)
      ·
        refine ⟨58715487886347697793960855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156574634363593860783895613 58715487886347697793960855)
        ·
          refine ⟨88073231829521546690941283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58715487886347697793960855 88073231829521546690941283)
          ·
            refine ⟨132109847744282320036411925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88073231829521546690941283 132109847744282320036411925)
            ·
              refine ⟨6192649113013233751706809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132109847744282320036411925 6192649113013233751706809)
              ·
                refine ⟨4644486834759925313780107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6192649113013233751706809 4644486834759925313780107)
                ·
                  refine ⟨6966730252139887970670161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4644486834759925313780107 6966730252139887970670161)
                  ·
                    refine ⟨5225047689104915978002621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6966730252139887970670161 5225047689104915978002621)
                    ·
                      refine ⟨1959392883414343491750983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5225047689104915978002621 1959392883414343491750983)
                      ·
                        rfl

theorem cell23_3815904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_3815904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815904 prefixEnd_3815904 := by exact prefixLift 3815904
  have htrace : WordTrace (prefixWord ++ tailWord_3815904) baseStart_3815904 baseEnd_3815904 := by
    simpa [prefixWord, tailWord_3815904, baseEnd_3815904] using wordTrace_append hprefix tailTrace_3815904
  have hstable : (prefixWord ++ tailWord_3815904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815904).length < 2 ^ (prefixWord ++ tailWord_3815904).sum := by decide
  have hdescent : baseEnd_3815904 < baseStart_3815904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815907 : List Nat := [1, 1, 1, 6, 3, 1, 1, 9]
def baseStart_3815907 : Nat := 118140960795 + 3815907 * 2 ^ 59
def prefixEnd_3815907 : Nat := 4983230072969 + 3 ^ 40 * 3815907 * 2
def baseEnd_3815907 : Nat := 72570163846529888148647

theorem tailTrace_3815907 : CollatzResearch.WordTrace tailWord_3815907 prefixEnd_3815907 72570163846529888148647 := by
  unfold tailWord_3815907
  simp only [CollatzResearch.WordTrace]
  refine ⟨139177562186628118875821975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92785041457752079250547983 139177562186628118875821975)
  ·
    refine ⟨208766343279942178313732963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139177562186628118875821975 208766343279942178313732963)
    ·
      refine ⟨313149514919913267470599445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208766343279942178313732963 313149514919913267470599445)
      ·
        refine ⟨14678883511870934412684349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 313149514919913267470599445 14678883511870934412684349)
        ·
          refine ⟨5504581316951600404756631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14678883511870934412684349 5504581316951600404756631)
          ·
            refine ⟨8256871975427400607134947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5504581316951600404756631 8256871975427400607134947)
            ·
              refine ⟨12385307963141100910702421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8256871975427400607134947 12385307963141100910702421)
              ·
                refine ⟨72570163846529888148647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12385307963141100910702421 72570163846529888148647)
                ·
                  rfl

theorem cell23_3815907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 9].length) (baseStart_3815907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815907 prefixEnd_3815907 := by exact prefixLift 3815907
  have htrace : WordTrace (prefixWord ++ tailWord_3815907) baseStart_3815907 baseEnd_3815907 := by
    simpa [prefixWord, tailWord_3815907, baseEnd_3815907] using wordTrace_append hprefix tailTrace_3815907
  have hstable : (prefixWord ++ tailWord_3815907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815907).length < 2 ^ (prefixWord ++ tailWord_3815907).sum := by decide
  have hdescent : baseEnd_3815907 < baseStart_3815907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815927 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 1, 9, 2]
def baseStart_3815927 : Nat := 118140960795 + 3815927 * 2 ^ 59
def prefixEnd_3815927 : Nat := 4983230072969 + 3 ^ 40 * 3815927 * 2
def baseEnd_3815927 : Nat := 1959404693469396901763377

theorem tailTrace_3815927 : CollatzResearch.WordTrace tailWord_3815927 prefixEnd_3815927 1959404693469396901763377 := by
  unfold tailWord_3815927
  simp only [CollatzResearch.WordTrace]
  refine ⟨139178291646555662291550035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92785527764370441527700023 139178291646555662291550035)
  ·
    refine ⟨208767437469833493437325053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139178291646555662291550035 208767437469833493437325053)
    ·
      refine ⟨78287789051187560038996895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208767437469833493437325053 78287789051187560038996895)
      ·
        refine ⟨117431683576781340058495343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78287789051187560038996895 117431683576781340058495343)
        ·
          refine ⟨176147525365172010087743015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117431683576781340058495343 176147525365172010087743015)
          ·
            refine ⟨264221288047758015131614523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176147525365172010087743015 264221288047758015131614523)
            ·
              refine ⟨396331932071637022697421785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264221288047758015131614523 396331932071637022697421785)
              ·
                refine ⟨297248949053727767023066339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396331932071637022697421785 297248949053727767023066339)
                ·
                  refine ⟨445873423580591650534599509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297248949053727767023066339 445873423580591650534599509)
                  ·
                    refine ⟨2612539591292529202351169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 445873423580591650534599509 2612539591292529202351169)
                    ·
                      refine ⟨1959404693469396901763377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2612539591292529202351169 1959404693469396901763377)
                      ·
                        rfl

theorem cell23_3815927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 9, 2].length) (baseStart_3815927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815927 prefixEnd_3815927 := by exact prefixLift 3815927
  have htrace : WordTrace (prefixWord ++ tailWord_3815927) baseStart_3815927 baseEnd_3815927 := by
    simpa [prefixWord, tailWord_3815927, baseEnd_3815927] using wordTrace_append hprefix tailTrace_3815927
  have hstable : (prefixWord ++ tailWord_3815927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815927).length < 2 ^ (prefixWord ++ tailWord_3815927).sum := by decide
  have hdescent : baseEnd_3815927 < baseStart_3815927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815944 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 3, 3, 2]
def baseStart_3815944 : Nat := 118140960795 + 3815944 * 2 ^ 59
def prefixEnd_3815944 : Nat := 4983230072969 + 3 ^ 40 * 3815944 * 2
def baseEnd_3815944 : Nat := 1959413422640523335250799

theorem tailTrace_3815944 : CollatzResearch.WordTrace tailWord_3815944 prefixEnd_3815944 1959413422640523335250799 := by
  unfold tailWord_3815944
  simp only [CollatzResearch.WordTrace]
  refine ⟨69589455843747037097459443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92785941124996049463279257 69589455843747037097459443)
  ·
    refine ⟨104384183765620555646189165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69589455843747037097459443 104384183765620555646189165)
    ·
      refine ⟨39144068912107708367320937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104384183765620555646189165 39144068912107708367320937)
      ·
        refine ⟨29358051684080781275490703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39144068912107708367320937 29358051684080781275490703)
        ·
          refine ⟨44037077526121171913236055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29358051684080781275490703 44037077526121171913236055)
          ·
            refine ⟨66055616289181757869854083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44037077526121171913236055 66055616289181757869854083)
            ·
              refine ⟨99083424433772636804781125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66055616289181757869854083 99083424433772636804781125)
              ·
                refine ⟨18578142081332369400896461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99083424433772636804781125 18578142081332369400896461)
                ·
                  refine ⟨6966803280499638525336173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18578142081332369400896461 6966803280499638525336173)
                  ·
                    refine ⟨2612551230187364447001065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6966803280499638525336173 2612551230187364447001065)
                    ·
                      refine ⟨1959413422640523335250799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2612551230187364447001065 1959413422640523335250799)
                      ·
                        rfl

theorem cell23_3815944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_3815944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815944 prefixEnd_3815944 := by exact prefixLift 3815944
  have htrace : WordTrace (prefixWord ++ tailWord_3815944) baseStart_3815944 baseEnd_3815944 := by
    simpa [prefixWord, tailWord_3815944, baseEnd_3815944] using wordTrace_append hprefix tailTrace_3815944
  have hstable : (prefixWord ++ tailWord_3815944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815944).length < 2 ^ (prefixWord ++ tailWord_3815944).sum := by decide
  have hdescent : baseEnd_3815944 < baseStart_3815944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815987 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 4]
def baseStart_3815987 : Nat := 118140960795 + 3815987 * 2 ^ 59
def prefixEnd_3815987 : Nat := 4983230072969 + 3 ^ 40 * 3815987 * 2
def baseEnd_3815987 : Nat := 1959435502308666667013101

theorem tailTrace_3815987 : CollatzResearch.WordTrace tailWord_3815987 prefixEnd_3815987 1959435502308666667013101 := by
  unfold tailWord_3815987
  simp only [CollatzResearch.WordTrace]
  refine ⟨139180480026338292538734215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92786986684225528359156143 139180480026338292538734215)
  ·
    refine ⟨208770720039507438808101323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139180480026338292538734215 208770720039507438808101323)
    ·
      refine ⟨313156080059261158212151985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208770720039507438808101323 313156080059261158212151985)
      ·
        refine ⟨234867060044445868659113989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313156080059261158212151985 234867060044445868659113989)
        ·
          refine ⟨44037573758333600373583873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234867060044445868659113989 44037573758333600373583873)
          ·
            refine ⟨33028180318750200280187905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44037573758333600373583873 33028180318750200280187905)
            ·
              refine ⟨24771135239062650210140929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33028180318750200280187905 24771135239062650210140929)
              ·
                refine ⟨18578351429296987657605697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24771135239062650210140929 18578351429296987657605697)
                ·
                  refine ⟨13933763571972740743204273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18578351429296987657605697 13933763571972740743204273)
                  ·
                    refine ⟨10450322678979555557403205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13933763571972740743204273 10450322678979555557403205)
                    ·
                      refine ⟨1959435502308666667013101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10450322678979555557403205 1959435502308666667013101)
                      ·
                        rfl

theorem cell23_3815987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_3815987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3815987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3815987 prefixEnd_3815987 := by exact prefixLift 3815987
  have htrace : WordTrace (prefixWord ++ tailWord_3815987) baseStart_3815987 baseEnd_3815987 := by
    simpa [prefixWord, tailWord_3815987, baseEnd_3815987] using wordTrace_append hprefix tailTrace_3815987
  have hstable : (prefixWord ++ tailWord_3815987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815987).length < 2 ^ (prefixWord ++ tailWord_3815987).sum := by decide
  have hdescent : baseEnd_3815987 < baseStart_3815987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816087 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 10]
def baseStart_3816087 : Nat := 118140960795 + 3816087 * 2 ^ 59
def prefixEnd_3816087 : Nat := 4983230072969 + 3 ^ 40 * 3816087 * 2
def baseEnd_3816087 : Nat := 217720761152679586195849

theorem tailTrace_3816087 : CollatzResearch.WordTrace tailWord_3816087 prefixEnd_3816087 217720761152679586195849 := by
  unfold tailWord_3816087
  simp only [CollatzResearch.WordTrace]
  refine ⟨139184127325976009617374515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92789418217317339744916343 139184127325976009617374515)
  ·
    refine ⟨208776190988964014426061773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139184127325976009617374515 208776190988964014426061773)
    ·
      refine ⟨78291071620861505409773165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208776190988964014426061773 78291071620861505409773165)
      ·
        refine ⟨29359151857823064528664937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78291071620861505409773165 29359151857823064528664937)
        ·
          refine ⟨22019363893367298396498703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29359151857823064528664937 22019363893367298396498703)
          ·
            refine ⟨33029045840050947594748055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22019363893367298396498703 33029045840050947594748055)
            ·
              refine ⟨49543568760076421392122083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33029045840050947594748055 49543568760076421392122083)
              ·
                refine ⟨74315353140114632088183125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49543568760076421392122083 74315353140114632088183125)
                ·
                  refine ⟨217720761152679586195849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 74315353140114632088183125 217720761152679586195849)
                  ·
                    rfl

theorem cell23_3816087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 10].length) (baseStart_3816087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816087 prefixEnd_3816087 := by exact prefixLift 3816087
  have htrace : WordTrace (prefixWord ++ tailWord_3816087) baseStart_3816087 baseEnd_3816087 := by
    simpa [prefixWord, tailWord_3816087, baseEnd_3816087] using wordTrace_append hprefix tailTrace_3816087
  have hstable : (prefixWord ++ tailWord_3816087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816087).length < 2 ^ (prefixWord ++ tailWord_3816087).sum := by decide
  have hdescent : baseEnd_3816087 < baseStart_3816087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816165 : List Nat := [1, 3, 1, 4, 1, 3, 1, 4, 1, 1, 3]
def baseStart_3816165 : Nat := 118140960795 + 3816165 * 2 ^ 59
def prefixEnd_3816165 : Nat := 4983230072969 + 3 ^ 40 * 3816165 * 2
def baseEnd_3816165 : Nat := 1959526901865166970587283

theorem tailTrace_3816165 : CollatzResearch.WordTrace tailWord_3816165 prefixEnd_3816165 1959526901865166970587283 := by
  unfold tailWord_3816165
  simp only [CollatzResearch.WordTrace]
  refine ⟨139186972219693428938713949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92791314813128952625809299 139186972219693428938713949)
  ·
    refine ⟨52195114582385035852017731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139186972219693428938713949 52195114582385035852017731)
    ·
      refine ⟨78292671873577553778026597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52195114582385035852017731 78292671873577553778026597)
      ·
        refine ⟨14679875976295791333379987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78292671873577553778026597 14679875976295791333379987)
        ·
          refine ⟨22019813964443687000069981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14679875976295791333379987 22019813964443687000069981)
          ·
            refine ⟨8257430236666382625026243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22019813964443687000069981 8257430236666382625026243)
            ·
              refine ⟨12386145354999573937539365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8257430236666382625026243 12386145354999573937539365)
              ·
                refine ⟨2322402254062420113288631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12386145354999573937539365 2322402254062420113288631)
                ·
                  refine ⟨3483603381093630169932947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2322402254062420113288631 3483603381093630169932947)
                  ·
                    refine ⟨5225405071640445254899421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3483603381093630169932947 5225405071640445254899421)
                    ·
                      refine ⟨1959526901865166970587283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5225405071640445254899421 1959526901865166970587283)
                      ·
                        rfl

theorem cell23_3816165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_3816165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816165 prefixEnd_3816165 := by exact prefixLift 3816165
  have htrace : WordTrace (prefixWord ++ tailWord_3816165) baseStart_3816165 baseEnd_3816165 := by
    simpa [prefixWord, tailWord_3816165, baseEnd_3816165] using wordTrace_append hprefix tailTrace_3816165
  have hstable : (prefixWord ++ tailWord_3816165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816165).length < 2 ^ (prefixWord ++ tailWord_3816165).sum := by decide
  have hdescent : baseEnd_3816165 < baseStart_3816165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816188 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 5, 2, 2]
def baseStart_3816188 : Nat := 118140960795 + 3816188 * 2 ^ 59
def prefixEnd_3816188 : Nat := 4983230072969 + 3 ^ 40 * 3816188 * 2
def baseEnd_3816188 : Nat := 1959538711920220380599677

theorem tailTrace_3816188 : CollatzResearch.WordTrace tailWord_3816188 prefixEnd_3816188 1959538711920220380599677 := by
  unfold tailWord_3816188
  simp only [CollatzResearch.WordTrace]
  refine ⟨69593905549305051933400609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92791874065740069244534145 69593905549305051933400609)
  ·
    refine ⟨52195429161978788950050457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69593905549305051933400609 52195429161978788950050457)
    ·
      refine ⟨39146571871484091712537843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52195429161978788950050457 39146571871484091712537843)
      ·
        refine ⟨58719857807226137568806765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39146571871484091712537843 58719857807226137568806765)
        ·
          refine ⟨22019946677709801588302537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58719857807226137568806765 22019946677709801588302537)
          ·
            refine ⟨16514960008282351191226903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22019946677709801588302537 16514960008282351191226903)
            ·
              refine ⟨24772440012423526786840355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16514960008282351191226903 24772440012423526786840355)
              ·
                refine ⟨37158660018635290180260533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24772440012423526786840355 37158660018635290180260533)
                ·
                  refine ⟨3483624376747058454399425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37158660018635290180260533 3483624376747058454399425)
                  ·
                    refine ⟨2612718282560293840799569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3483624376747058454399425 2612718282560293840799569)
                    ·
                      refine ⟨1959538711920220380599677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2612718282560293840799569 1959538711920220380599677)
                      ·
                        rfl

theorem cell23_3816188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_3816188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816188 prefixEnd_3816188 := by exact prefixLift 3816188
  have htrace : WordTrace (prefixWord ++ tailWord_3816188) baseStart_3816188 baseEnd_3816188 := by
    simpa [prefixWord, tailWord_3816188, baseEnd_3816188] using wordTrace_append hprefix tailTrace_3816188
  have hstable : (prefixWord ++ tailWord_3816188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816188).length < 2 ^ (prefixWord ++ tailWord_3816188).sum := by decide
  have hdescent : baseEnd_3816188 < baseStart_3816188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816191 : List Nat := [1, 1, 2, 2, 1, 3, 1, 6, 1, 2, 3]
def baseStart_3816191 : Nat := 118140960795 + 3816191 * 2 ^ 59
def prefixEnd_3816191 : Nat := 4983230072969 + 3 ^ 40 * 3816191 * 2
def baseEnd_3816191 : Nat := 1959540252362183868862163

theorem tailTrace_3816191 : CollatzResearch.WordTrace tailWord_3816191 prefixEnd_3816191 1959540252362183868862163 := by
  unfold tailWord_3816191
  simp only [CollatzResearch.WordTrace]
  refine ⟨139187920517599235379160427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92791947011732823586106951 139187920517599235379160427)
  ·
    refine ⟨208781880776398853068740641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139187920517599235379160427 208781880776398853068740641)
    ·
      refine ⟨156586410582299139801555481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208781880776398853068740641 156586410582299139801555481)
      ·
        refine ⟨117439807936724354851166611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156586410582299139801555481 117439807936724354851166611)
        ·
          refine ⟨176159711905086532276749917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117439807936724354851166611 176159711905086532276749917)
          ·
            refine ⟨66059891964407449603781219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176159711905086532276749917 66059891964407449603781219)
            ·
              refine ⟨99089837946611174405671829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66059891964407449603781219 99089837946611174405671829)
              ·
                refine ⟨4644836153747398800265867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99089837946611174405671829 4644836153747398800265867)
                ·
                  refine ⟨6967254230621098200398801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4644836153747398800265867 6967254230621098200398801)
                  ·
                    refine ⟨5225440672965823650299101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6967254230621098200398801 5225440672965823650299101)
                    ·
                      refine ⟨1959540252362183868862163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5225440672965823650299101 1959540252362183868862163)
                      ·
                        rfl

theorem cell23_3816191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_3816191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816191 prefixEnd_3816191 := by exact prefixLift 3816191
  have htrace : WordTrace (prefixWord ++ tailWord_3816191) baseStart_3816191 baseEnd_3816191 := by
    simpa [prefixWord, tailWord_3816191, baseEnd_3816191] using wordTrace_append hprefix tailTrace_3816191
  have hstable : (prefixWord ++ tailWord_3816191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816191).length < 2 ^ (prefixWord ++ tailWord_3816191).sum := by decide
  have hdescent : baseEnd_3816191 < baseStart_3816191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816215 : List Nat := [1, 1, 3, 4, 3, 2, 1, 2, 2, 4]
def baseStart_3816215 : Nat := 118140960795 + 3816215 * 2 ^ 59
def prefixEnd_3816215 : Nat := 4983230072969 + 3 ^ 40 * 3816215 * 2
def baseEnd_3816215 : Nat := 653184191965963924987351

theorem tailTrace_3816215 : CollatzResearch.WordTrace tailWord_3816215 prefixEnd_3816215 653184191965963924987351 := by
  unfold tailWord_3816215
  simp only [CollatzResearch.WordTrace]
  refine ⟨139188795869512287478034099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92792530579674858318689399 139188795869512287478034099)
  ·
    refine ⟨208783193804268431217051149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139188795869512287478034099 208783193804268431217051149)
    ·
      refine ⟨78293697676600661706394181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208783193804268431217051149 78293697676600661706394181)
      ·
        refine ⟨14680068314362624069948909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78293697676600661706394181 14680068314362624069948909)
        ·
          refine ⟨5505025617885984026230841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14680068314362624069948909 5505025617885984026230841)
          ·
            refine ⟨4128769213414488019673131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5505025617885984026230841 4128769213414488019673131)
            ·
              refine ⟨6193153820121732029509697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4128769213414488019673131 6193153820121732029509697)
              ·
                refine ⟨4644865365091299022132273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6193153820121732029509697 4644865365091299022132273)
                ·
                  refine ⟨3483649023818474266599205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4644865365091299022132273 3483649023818474266599205)
                  ·
                    refine ⟨653184191965963924987351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3483649023818474266599205 653184191965963924987351)
                    ·
                      rfl

theorem cell23_3816215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_3816215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816215 prefixEnd_3816215 := by exact prefixLift 3816215
  have htrace : WordTrace (prefixWord ++ tailWord_3816215) baseStart_3816215 baseEnd_3816215 := by
    simpa [prefixWord, tailWord_3816215, baseEnd_3816215] using wordTrace_append hprefix tailTrace_3816215
  have hstable : (prefixWord ++ tailWord_3816215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816215).length < 2 ^ (prefixWord ++ tailWord_3816215).sum := by decide
  have hdescent : baseEnd_3816215 < baseStart_3816215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816331 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 2, 5]
def baseStart_3816331 : Nat := 118140960795 + 3816331 * 2 ^ 59
def prefixEnd_3816331 : Nat := 4983230072969 + 3 ^ 40 * 3816331 * 2
def baseEnd_3816331 : Nat := 653204046551271107037173

theorem tailTrace_3816331 : CollatzResearch.WordTrace tailWord_3816331 prefixEnd_3816331 653204046551271107037173 := by
  unfold tailWord_3816331
  simp only [CollatzResearch.WordTrace]
  refine ⟨139193026737092039289256847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92795351158061359526171231 139193026737092039289256847)
  ·
    refine ⟨208789540105638058933885271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139193026737092039289256847 208789540105638058933885271)
    ·
      refine ⟨313184310158457088400827907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208789540105638058933885271 313184310158457088400827907)
      ·
        refine ⟨469776465237685632601241861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313184310158457088400827907 469776465237685632601241861)
        ·
          refine ⟨88083087232066056112732849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 469776465237685632601241861 88083087232066056112732849)
          ·
            refine ⟨66062315424049542084549637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88083087232066056112732849 66062315424049542084549637)
            ·
              refine ⟨12386684142009289140853057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66062315424049542084549637 12386684142009289140853057)
              ·
                refine ⟨9290013106506966855639793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12386684142009289140853057 9290013106506966855639793)
                ·
                  refine ⟨6967509829880225141729845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9290013106506966855639793 6967509829880225141729845)
                  ·
                    refine ⟨653204046551271107037173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6967509829880225141729845 653204046551271107037173)
                    ·
                      rfl

theorem cell23_3816331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 5].length) (baseStart_3816331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816331 prefixEnd_3816331 := by exact prefixLift 3816331
  have htrace : WordTrace (prefixWord ++ tailWord_3816331) baseStart_3816331 baseEnd_3816331 := by
    simpa [prefixWord, tailWord_3816331, baseEnd_3816331] using wordTrace_append hprefix tailTrace_3816331
  have hstable : (prefixWord ++ tailWord_3816331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816331).length < 2 ^ (prefixWord ++ tailWord_3816331).sum := by decide
  have hdescent : baseEnd_3816331 < baseStart_3816331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816341 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_3816341 : Nat := 118140960795 + 3816341 * 2 ^ 59
def prefixEnd_3816341 : Nat := 4983230072969 + 3 ^ 40 * 3816341 * 2
def baseEnd_3816341 : Nat := 1959617274460358281986473

theorem tailTrace_3816341 : CollatzResearch.WordTrace tailWord_3816341 prefixEnd_3816341 1959617274460358281986473 := by
  unfold tailWord_3816341
  simp only [CollatzResearch.WordTrace]
  refine ⟨139193391467055810997120877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92795594311370540664747251 139193391467055810997120877)
  ·
    refine ⟨52197521800145929123920329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139193391467055810997120877 52197521800145929123920329)
    ·
      refine ⟨39148141350109446842940247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52197521800145929123920329 39148141350109446842940247)
      ·
        refine ⟨58722212025164170264410371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39148141350109446842940247 58722212025164170264410371)
        ·
          refine ⟨88083318037746255396615557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58722212025164170264410371 88083318037746255396615557)
          ·
            refine ⟨16515622132077422886865417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88083318037746255396615557 16515622132077422886865417)
            ·
              refine ⟨12386716599058067165149063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16515622132077422886865417 12386716599058067165149063)
              ·
                refine ⟨18580074898587100747723595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12386716599058067165149063 18580074898587100747723595)
                ·
                  refine ⟨27870112347880651121585393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18580074898587100747723595 27870112347880651121585393)
                  ·
                    refine ⟨20902584260910488341189045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27870112347880651121585393 20902584260910488341189045)
                    ·
                      refine ⟨1959617274460358281986473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20902584260910488341189045 1959617274460358281986473)
                      ·
                        rfl

theorem cell23_3816341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_3816341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816341 prefixEnd_3816341 := by exact prefixLift 3816341
  have htrace : WordTrace (prefixWord ++ tailWord_3816341) baseStart_3816341 baseEnd_3816341 := by
    simpa [prefixWord, tailWord_3816341, baseEnd_3816341] using wordTrace_append hprefix tailTrace_3816341
  have hstable : (prefixWord ++ tailWord_3816341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816341).length < 2 ^ (prefixWord ++ tailWord_3816341).sum := by decide
  have hdescent : baseEnd_3816341 < baseStart_3816341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816342 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3816342 : Nat := 118140960795 + 3816342 * 2 ^ 59
def prefixEnd_3816342 : Nat := 4983230072969 + 3 ^ 40 * 3816342 * 2
def baseEnd_3816342 : Nat := 1959617787941012778073969

theorem tailTrace_3816342 : CollatzResearch.WordTrace tailWord_3816342 prefixEnd_3816342 1959617787941012778073969 := by
  unfold tailWord_3816342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8699589246253261760494205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92795618626701458778604853 8699589246253261760494205)
  ·
    refine ⟨3262345967344973160185327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8699589246253261760494205 3262345967344973160185327)
    ·
      refine ⟨4893518951017459740277991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3262345967344973160185327 4893518951017459740277991)
      ·
        refine ⟨7340278426526189610416987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4893518951017459740277991 7340278426526189610416987)
        ·
          refine ⟨11010417639789284415625481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7340278426526189610416987 11010417639789284415625481)
          ·
            refine ⟨8257813229841963311719111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11010417639789284415625481 8257813229841963311719111)
            ·
              refine ⟨12386719844762944967578667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8257813229841963311719111 12386719844762944967578667)
              ·
                refine ⟨18580079767144417451368001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12386719844762944967578667 18580079767144417451368001)
                ·
                  refine ⟨13935059825358313088526001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18580079767144417451368001 13935059825358313088526001)
                  ·
                    refine ⟨10451294869018734816394501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13935059825358313088526001 10451294869018734816394501)
                    ·
                      refine ⟨1959617787941012778073969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10451294869018734816394501 1959617787941012778073969)
                      ·
                        rfl

theorem cell23_3816342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3816342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816342 prefixEnd_3816342 := by exact prefixLift 3816342
  have htrace : WordTrace (prefixWord ++ tailWord_3816342) baseStart_3816342 baseEnd_3816342 := by
    simpa [prefixWord, tailWord_3816342, baseEnd_3816342] using wordTrace_append hprefix tailTrace_3816342
  have hstable : (prefixWord ++ tailWord_3816342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816342).length < 2 ^ (prefixWord ++ tailWord_3816342).sum := by decide
  have hdescent : baseEnd_3816342 < baseStart_3816342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816365 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_3816365 : Nat := 118140960795 + 3816365 * 2 ^ 59
def prefixEnd_3816365 : Nat := 4983230072969 + 3 ^ 40 * 3816365 * 2
def baseEnd_3816365 : Nat := 653209865998688729362121

theorem tailTrace_3816365 : CollatzResearch.WordTrace tailWord_3816365 prefixEnd_3816365 653209865998688729362121 := by
  unfold tailWord_3816365
  simp only [CollatzResearch.WordTrace]
  refine ⟨139194266818968863095994549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92796177879312575397329699 139194266818968863095994549)
  ·
    refine ⟨13049462514278330915249489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139194266818968863095994549 13049462514278330915249489)
    ·
      refine ⟨9787096885708748186437117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13049462514278330915249489 9787096885708748186437117)
      ·
        refine ⟨3670161332140780569913919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9787096885708748186437117 3670161332140780569913919)
        ·
          refine ⟨5505241998211170854870879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3670161332140780569913919 5505241998211170854870879)
          ·
            refine ⟨8257862997316756282306319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5505241998211170854870879 8257862997316756282306319)
            ·
              refine ⟨12386794495975134423459479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8257862997316756282306319 12386794495975134423459479)
              ·
                refine ⟨18580191743962701635189219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12386794495975134423459479 18580191743962701635189219)
                ·
                  refine ⟨27870287615944052452783829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18580191743962701635189219 27870287615944052452783829)
                  ·
                    refine ⟨653209865998688729362121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27870287615944052452783829 653209865998688729362121)
                    ·
                      rfl

theorem cell23_3816365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_3816365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816365 prefixEnd_3816365 := by exact prefixLift 3816365
  have htrace : WordTrace (prefixWord ++ tailWord_3816365) baseStart_3816365 baseEnd_3816365 := by
    simpa [prefixWord, tailWord_3816365, baseEnd_3816365] using wordTrace_append hprefix tailTrace_3816365
  have hstable : (prefixWord ++ tailWord_3816365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816365).length < 2 ^ (prefixWord ++ tailWord_3816365).sum := by decide
  have hdescent : baseEnd_3816365 < baseStart_3816365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816395 : List Nat := [1, 1, 1, 1, 3, 5, 2, 4, 1, 4]
def baseStart_3816395 : Nat := 118140960795 + 3816395 * 2 ^ 59
def prefixEnd_3816395 : Nat := 4983230072969 + 3 ^ 40 * 3816395 * 2
def baseEnd_3816395 : Nat := 653215000805233690237075

theorem tailTrace_3816395 : CollatzResearch.WordTrace tailWord_3816395 prefixEnd_3816395 653215000805233690237075 := by
  unfold tailWord_3816395
  simp only [CollatzResearch.WordTrace]
  refine ⟨139195361008860178219586639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92796907339240118813057759 139195361008860178219586639)
  ·
    refine ⟨208793041513290267329379959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139195361008860178219586639 208793041513290267329379959)
    ·
      refine ⟨313189562269935400994069939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208793041513290267329379959 313189562269935400994069939)
      ·
        refine ⟨469784343404903101491104909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313189562269935400994069939 469784343404903101491104909)
        ·
          refine ⟨176169128776838663059164341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469784343404903101491104909 176169128776838663059164341)
          ·
            refine ⟨16515855822828624661796657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176169128776838663059164341 16515855822828624661796657)
            ·
              refine ⟨12386891867121468496347493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16515855822828624661796657 12386891867121468496347493)
              ·
                refine ⟨2322542225085275343065155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12386891867121468496347493 2322542225085275343065155)
                ·
                  refine ⟨3483813337627913014597733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2322542225085275343065155 3483813337627913014597733)
                  ·
                    refine ⟨653215000805233690237075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3483813337627913014597733 653215000805233690237075)
                    ·
                      rfl

theorem cell23_3816395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 1, 4].length) (baseStart_3816395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816395 prefixEnd_3816395 := by exact prefixLift 3816395
  have htrace : WordTrace (prefixWord ++ tailWord_3816395) baseStart_3816395 baseEnd_3816395 := by
    simpa [prefixWord, tailWord_3816395, baseEnd_3816395] using wordTrace_append hprefix tailTrace_3816395
  have hstable : (prefixWord ++ tailWord_3816395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816395).length < 2 ^ (prefixWord ++ tailWord_3816395).sum := by decide
  have hdescent : baseEnd_3816395 < baseStart_3816395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816436 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3816436 : Nat := 118140960795 + 3816436 * 2 ^ 59
def prefixEnd_3816436 : Nat := 4983230072969 + 3 ^ 40 * 3816436 * 2
def baseEnd_3816436 : Nat := 1959666055122535410298537

theorem tailTrace_3816436 : CollatzResearch.WordTrace tailWord_3816436 prefixEnd_3816436 1959666055122535410298537 := by
  unfold tailWord_3816436
  simp only [CollatzResearch.WordTrace]
  refine ⟨69598428200855821110914581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92797904267807761481219441 69598428200855821110914581)
  ·
    refine ⟨3262426321915116614574121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69598428200855821110914581 3262426321915116614574121)
    ·
      refine ⟨2446819741436337460930591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3262426321915116614574121 2446819741436337460930591)
      ·
        refine ⟨3670229612154506191395887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2446819741436337460930591 3670229612154506191395887)
        ·
          refine ⟨5505344418231759287093831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3670229612154506191395887 5505344418231759287093831)
          ·
            refine ⟨8258016627347638930640747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5505344418231759287093831 8258016627347638930640747)
            ·
              refine ⟨12387024941021458395961121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8258016627347638930640747 12387024941021458395961121)
              ·
                refine ⟨9290268705766093796970841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12387024941021458395961121 9290268705766093796970841)
                ·
                  refine ⟨6967701529324570347728131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9290268705766093796970841 6967701529324570347728131)
                  ·
                    refine ⟨10451552293986855521592197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6967701529324570347728131 10451552293986855521592197)
                    ·
                      refine ⟨1959666055122535410298537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10451552293986855521592197 1959666055122535410298537)
                      ·
                        rfl

theorem cell23_3816436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3816436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816436 prefixEnd_3816436 := by exact prefixLift 3816436
  have htrace : WordTrace (prefixWord ++ tailWord_3816436) baseStart_3816436 baseEnd_3816436 := by
    simpa [prefixWord, tailWord_3816436, baseEnd_3816436] using wordTrace_append hprefix tailTrace_3816436
  have hstable : (prefixWord ++ tailWord_3816436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816436).length < 2 ^ (prefixWord ++ tailWord_3816436).sum := by decide
  have hdescent : baseEnd_3816436 < baseStart_3816436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816446 : List Nat := [4, 2, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_3816446 : Nat := 118140960795 + 3816446 * 2 ^ 59
def prefixEnd_3816446 : Nat := 4983230072969 + 3 ^ 40 * 3816446 * 2
def baseEnd_3816446 : Nat := 653223729976360123724497

theorem tailTrace_3816446 : CollatzResearch.WordTrace tailWord_3816446 prefixEnd_3816446 653223729976360123724497 := by
  unfold tailWord_3816446
  simp only [CollatzResearch.WordTrace]
  refine ⟨17399652641459426741211649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92798147421116942619795461 17399652641459426741211649)
  ·
    refine ⟨13049739481094570055908737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17399652641459426741211649 13049739481094570055908737)
    ·
      refine ⟨9787304610820927541931553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13049739481094570055908737 9787304610820927541931553)
      ·
        refine ⟨7340478458115695656448665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9787304610820927541931553 7340478458115695656448665)
        ·
          refine ⟨5505358843586771742336499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7340478458115695656448665 5505358843586771742336499)
          ·
            refine ⟨8258038265380157613504749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5505358843586771742336499 8258038265380157613504749)
            ·
              refine ⟨3096764349517559105064281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8258038265380157613504749 3096764349517559105064281)
              ·
                refine ⟨2322573262138169328798211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3096764349517559105064281 2322573262138169328798211)
                ·
                  refine ⟨3483859893207253993197317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2322573262138169328798211 3483859893207253993197317)
                  ·
                    refine ⟨653223729976360123724497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3483859893207253993197317 653223729976360123724497)
                    ·
                      rfl

theorem cell23_3816446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_3816446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816446 prefixEnd_3816446 := by exact prefixLift 3816446
  have htrace : WordTrace (prefixWord ++ tailWord_3816446) baseStart_3816446 baseEnd_3816446 := by
    simpa [prefixWord, tailWord_3816446, baseEnd_3816446] using wordTrace_append hprefix tailTrace_3816446
  have hstable : (prefixWord ++ tailWord_3816446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816446).length < 2 ^ (prefixWord ++ tailWord_3816446).sum := by decide
  have hdescent : baseEnd_3816446 < baseStart_3816446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816502 : List Nat := [5, 1, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_3816502 : Nat := 118140960795 + 3816502 * 2 ^ 59
def prefixEnd_3816502 : Nat := 4983230072969 + 3 ^ 40 * 3816502 * 2
def baseEnd_3816502 : Nat := 653233314948577384024411

theorem tailTrace_3816502 : CollatzResearch.WordTrace tailWord_3816502 prefixEnd_3816502 653233314948577384024411 := by
  unfold tailWord_3816502
  simp only [CollatzResearch.WordTrace]
  refine ⟨8699953976217033468358235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92799509079648356995821173 8699953976217033468358235)
  ·
    refine ⟨13049930964325550202537353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8699953976217033468358235 13049930964325550202537353)
    ·
      refine ⟨9787448223244162651903015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13049930964325550202537353 9787448223244162651903015)
      ·
        refine ⟨14681172334866243977854523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9787448223244162651903015 14681172334866243977854523)
        ·
          refine ⟨22021758502299365966781785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14681172334866243977854523 22021758502299365966781785)
          ·
            refine ⟨16516318876724524475086339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22021758502299365966781785 16516318876724524475086339)
            ·
              refine ⟨24774478315086786712629509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16516318876724524475086339 24774478315086786712629509)
              ·
                refine ⟨4645214684078772508618033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24774478315086786712629509 4645214684078772508618033)
                ·
                  refine ⟨3483911013059079381463525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4645214684078772508618033 3483911013059079381463525)
                  ·
                    refine ⟨653233314948577384024411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3483911013059079381463525 653233314948577384024411)
                    ·
                      rfl

theorem cell23_3816502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_3816502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816502 prefixEnd_3816502 := by exact prefixLift 3816502
  have htrace : WordTrace (prefixWord ++ tailWord_3816502) baseStart_3816502 baseEnd_3816502 := by
    simpa [prefixWord, tailWord_3816502, baseEnd_3816502] using wordTrace_append hprefix tailTrace_3816502
  have hstable : (prefixWord ++ tailWord_3816502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816502).length < 2 ^ (prefixWord ++ tailWord_3816502).sum := by decide
  have hdescent : baseEnd_3816502 < baseStart_3816502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816531 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 8]
def baseStart_3816531 : Nat := 118140960795 + 3816531 * 2 ^ 59
def prefixEnd_3816531 : Nat := 4983230072969 + 3 ^ 40 * 3816531 * 2
def baseEnd_3816531 : Nat := 1959714835784712538610599

theorem tailTrace_3816531 : CollatzResearch.WordTrace tailWord_3816531 prefixEnd_3816531 1959714835784712538610599 := by
  unfold tailWord_3816531
  simp only [CollatzResearch.WordTrace]
  refine ⟨139200321336367473446537447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92800214224244982297691631 139200321336367473446537447)
  ·
    refine ⟨208800482004551210169806171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139200321336367473446537447 208800482004551210169806171)
    ·
      refine ⟨313200723006826815254709257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208800482004551210169806171 313200723006826815254709257)
      ·
        refine ⟨234900542255120111441031943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313200723006826815254709257 234900542255120111441031943)
        ·
          refine ⟨352350813382680167161547915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234900542255120111441031943 352350813382680167161547915)
          ·
            refine ⟨528526220074020250742321873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352350813382680167161547915 528526220074020250742321873)
            ·
              refine ⟨396394665055515188056741405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528526220074020250742321873 396394665055515188056741405)
              ·
                refine ⟨148647999395818195521278027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 396394665055515188056741405 148647999395818195521278027)
                ·
                  refine ⟨222971999093727293281917041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148647999395818195521278027 222971999093727293281917041)
                  ·
                    refine ⟨167228999320295469961437781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 222971999093727293281917041 167228999320295469961437781)
                    ·
                      refine ⟨1959714835784712538610599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 167228999320295469961437781 1959714835784712538610599)
                      ·
                        rfl

theorem cell23_3816531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_3816531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816531 prefixEnd_3816531 := by exact prefixLift 3816531
  have htrace : WordTrace (prefixWord ++ tailWord_3816531) baseStart_3816531 baseEnd_3816531 := by
    simpa [prefixWord, tailWord_3816531, baseEnd_3816531] using wordTrace_append hprefix tailTrace_3816531
  have hstable : (prefixWord ++ tailWord_3816531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816531).length < 2 ^ (prefixWord ++ tailWord_3816531).sum := by decide
  have hdescent : baseEnd_3816531 < baseStart_3816531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816546 : List Nat := [3, 3, 2, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_3816546 : Nat := 118140960795 + 3816546 * 2 ^ 59
def prefixEnd_3816546 : Nat := 4983230072969 + 3 ^ 40 * 3816546 * 2
def baseEnd_3816546 : Nat := 1959722537994529979923031

theorem tailTrace_3816546 : CollatzResearch.WordTrace tailWord_3816546 prefixEnd_3816546 1959722537994529979923031 := by
  unfold tailWord_3816546
  simp only [CollatzResearch.WordTrace]
  refine ⟨34800217107828282752083373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92800578954208754005555661 34800217107828282752083373)
  ·
    refine ⟨13050081415435606032031265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34800217107828282752083373 13050081415435606032031265)
    ·
      refine ⟨9787561061576704524023449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13050081415435606032031265 9787561061576704524023449)
      ·
        refine ⟨7340670796182528393017587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9787561061576704524023449 7340670796182528393017587)
        ·
          refine ⟨11011006194273792589526381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7340670796182528393017587 11011006194273792589526381)
          ·
            refine ⟨4129127322852672221072393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11011006194273792589526381 4129127322852672221072393)
            ·
              refine ⟨3096845492139504165804295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4129127322852672221072393 3096845492139504165804295)
              ·
                refine ⟨4645268238209256248706443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3096845492139504165804295 4645268238209256248706443)
                ·
                  refine ⟨6967902357313884373059665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4645268238209256248706443 6967902357313884373059665)
                  ·
                    refine ⟨5225926767985413279794749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6967902357313884373059665 5225926767985413279794749)
                    ·
                      refine ⟨1959722537994529979923031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5225926767985413279794749 1959722537994529979923031)
                      ·
                        rfl

theorem cell23_3816546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_3816546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816546 prefixEnd_3816546 := by exact prefixLift 3816546
  have htrace : WordTrace (prefixWord ++ tailWord_3816546) baseStart_3816546 baseEnd_3816546 := by
    simpa [prefixWord, tailWord_3816546, baseEnd_3816546] using wordTrace_append hprefix tailTrace_3816546
  have hstable : (prefixWord ++ tailWord_3816546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816546).length < 2 ^ (prefixWord ++ tailWord_3816546).sum := by decide
  have hdescent : baseEnd_3816546 < baseStart_3816546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816568 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 1, 6, 3]
def baseStart_3816568 : Nat := 118140960795 + 3816568 * 2 ^ 59
def prefixEnd_3816568 : Nat := 4983230072969 + 3 ^ 40 * 3816568 * 2
def baseEnd_3816568 : Nat := 1959733834568928893847929

theorem tailTrace_3816568 : CollatzResearch.WordTrace tailWord_3816568 prefixEnd_3816568 1959733834568928893847929 := by
  unfold tailWord_3816568
  simp only [CollatzResearch.WordTrace]
  refine ⟨69600835418616714382817179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92801113891488952510422905 69600835418616714382817179)
  ·
    refine ⟨104401253127925071574225769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69600835418616714382817179 104401253127925071574225769)
    ·
      refine ⟨78300939845943803680669327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104401253127925071574225769 78300939845943803680669327)
      ·
        refine ⟨117451409768915705521003991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78300939845943803680669327 117451409768915705521003991)
        ·
          refine ⟨176177114653373558281505987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117451409768915705521003991 176177114653373558281505987)
          ·
            refine ⟨264265671980060337422258981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176177114653373558281505987 264265671980060337422258981)
            ·
              refine ⟨49549813496261313266673559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264265671980060337422258981 49549813496261313266673559)
              ·
                refine ⟨74324720244391969900010339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49549813496261313266673559 74324720244391969900010339)
                ·
                  refine ⟨111487080366587954850015509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74324720244391969900010339 111487080366587954850015509)
                  ·
                    refine ⟨5225956892183810383594477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111487080366587954850015509 5225956892183810383594477)
                    ·
                      refine ⟨1959733834568928893847929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5225956892183810383594477 1959733834568928893847929)
                      ·
                        rfl

theorem cell23_3816568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_3816568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816568 prefixEnd_3816568 := by exact prefixLift 3816568
  have htrace : WordTrace (prefixWord ++ tailWord_3816568) baseStart_3816568 baseEnd_3816568 := by
    simpa [prefixWord, tailWord_3816568, baseEnd_3816568] using wordTrace_append hprefix tailTrace_3816568
  have hstable : (prefixWord ++ tailWord_3816568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816568).length < 2 ^ (prefixWord ++ tailWord_3816568).sum := by decide
  have hdescent : baseEnd_3816568 < baseStart_3816568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816648 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 2, 8]
def baseStart_3816648 : Nat := 118140960795 + 3816648 * 2 ^ 59
def prefixEnd_3816648 : Nat := 4983230072969 + 3 ^ 40 * 3816648 * 2
def baseEnd_3816648 : Nat := 653258304340429526949187

theorem tailTrace_3816648 : CollatzResearch.WordTrace tailWord_3816648 prefixEnd_3816648 653258304340429526949187 := by
  unfold tailWord_3816648
  simp only [CollatzResearch.WordTrace]
  refine ⟨69602294338471801214273299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92803059117962401619031065 69602294338471801214273299)
  ·
    refine ⟨104403441507707701821409949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69602294338471801214273299 104403441507707701821409949)
    ·
      refine ⟨39151290565390388183028731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104403441507707701821409949 39151290565390388183028731)
      ·
        refine ⟨58726935848085582274543097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39151290565390388183028731 58726935848085582274543097)
        ·
          refine ⟨44045201886064186705907323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58726935848085582274543097 44045201886064186705907323)
          ·
            refine ⟨66067802829096280058860985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44045201886064186705907323 66067802829096280058860985)
            ·
              refine ⟨49550852121822210044145739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66067802829096280058860985 49550852121822210044145739)
              ·
                refine ⟨74326278182733315066218609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49550852121822210044145739 74326278182733315066218609)
                ·
                  refine ⟨55744708637049986299663957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74326278182733315066218609 55744708637049986299663957)
                  ·
                    refine ⟨653258304340429526949187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55744708637049986299663957 653258304340429526949187)
                    ·
                      rfl

theorem cell23_3816648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_3816648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816648 prefixEnd_3816648 := by exact prefixLift 3816648
  have htrace : WordTrace (prefixWord ++ tailWord_3816648) baseStart_3816648 baseEnd_3816648 := by
    simpa [prefixWord, tailWord_3816648, baseEnd_3816648] using wordTrace_append hprefix tailTrace_3816648
  have hstable : (prefixWord ++ tailWord_3816648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816648).length < 2 ^ (prefixWord ++ tailWord_3816648).sum := by decide
  have hdescent : baseEnd_3816648 < baseStart_3816648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816655 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 3, 6, 2]
def baseStart_3816655 : Nat := 118140960795 + 3816655 * 2 ^ 59
def prefixEnd_3816655 : Nat := 4983230072969 + 3 ^ 40 * 3816655 * 2
def baseEnd_3816655 : Nat := 1959778507385870053460029

theorem tailTrace_3816655 : CollatzResearch.WordTrace tailWord_3816655 prefixEnd_3816655 1959778507385870053460029 := by
  unfold tailWord_3816655
  simp only [CollatzResearch.WordTrace]
  refine ⟨139204843987918242624051419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92803229325278828416034279 139204843987918242624051419)
  ·
    refine ⟨208807265981877363936077129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139204843987918242624051419 208807265981877363936077129)
    ·
      refine ⟨156605449486408022952057847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208807265981877363936077129 156605449486408022952057847)
      ·
        refine ⟨234908174229612034428086771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156605449486408022952057847 234908174229612034428086771)
        ·
          refine ⟨352362261344418051642130157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234908174229612034428086771 352362261344418051642130157)
          ·
            refine ⟨132135848004156769365798809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352362261344418051642130157 132135848004156769365798809)
            ·
              refine ⟨99101886003117577024349107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132135848004156769365798809 99101886003117577024349107)
              ·
                refine ⟨148652829004676365536523661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99101886003117577024349107 148652829004676365536523661)
                ·
                  refine ⟨55744810876753637076196373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148652829004676365536523661 55744810876753637076196373)
                  ·
                    refine ⟨2613038009847826737946705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55744810876753637076196373 2613038009847826737946705)
                    ·
                      refine ⟨1959778507385870053460029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2613038009847826737946705 1959778507385870053460029)
                      ·
                        rfl

theorem cell23_3816655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 6, 2].length) (baseStart_3816655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816655 prefixEnd_3816655 := by exact prefixLift 3816655
  have htrace : WordTrace (prefixWord ++ tailWord_3816655) baseStart_3816655 baseEnd_3816655 := by
    simpa [prefixWord, tailWord_3816655, baseEnd_3816655] using wordTrace_append hprefix tailTrace_3816655
  have hstable : (prefixWord ++ tailWord_3816655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816655).length < 2 ^ (prefixWord ++ tailWord_3816655).sum := by decide
  have hdescent : baseEnd_3816655 < baseStart_3816655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816706 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_3816706 : Nat := 118140960795 + 3816706 * 2 ^ 59
def prefixEnd_3816706 : Nat := 4983230072969 + 3 ^ 40 * 3816706 * 2
def baseEnd_3816706 : Nat := 1959804694899249353922295

theorem tailTrace_3816706 : CollatzResearch.WordTrace tailWord_3816706 prefixEnd_3816706 1959804694899249353922295 := by
  unfold tailWord_3816706
  simp only [CollatzResearch.WordTrace]
  refine ⟨34801676027683369583539493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92804469407155652222771981 34801676027683369583539493)
  ·
    refine ⟨6525314255190631796913655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34801676027683369583539493 6525314255190631796913655)
    ·
      refine ⟨9787971382785947695370483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6525314255190631796913655 9787971382785947695370483)
      ·
        refine ⟨14681957074178921543055725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9787971382785947695370483 14681957074178921543055725)
        ·
          refine ⟨5505733902817095578645897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14681957074178921543055725 5505733902817095578645897)
          ·
            refine ⟨4129300427112821683984423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5505733902817095578645897 4129300427112821683984423)
            ·
              refine ⟨6193950640669232525976635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4129300427112821683984423 6193950640669232525976635)
              ·
                refine ⟨9290925961003848788964953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6193950640669232525976635 9290925961003848788964953)
                ·
                  refine ⟨6968194470752886591723715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9290925961003848788964953 6968194470752886591723715)
                  ·
                    refine ⟨10452291706129329887585573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6968194470752886591723715 10452291706129329887585573)
                    ·
                      refine ⟨1959804694899249353922295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10452291706129329887585573 1959804694899249353922295)
                      ·
                        rfl

theorem cell23_3816706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_3816706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816706 prefixEnd_3816706 := by exact prefixLift 3816706
  have htrace : WordTrace (prefixWord ++ tailWord_3816706) baseStart_3816706 baseEnd_3816706 := by
    simpa [prefixWord, tailWord_3816706, baseEnd_3816706] using wordTrace_append hprefix tailTrace_3816706
  have hstable : (prefixWord ++ tailWord_3816706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816706).length < 2 ^ (prefixWord ++ tailWord_3816706).sum := by decide
  have hdescent : baseEnd_3816706 < baseStart_3816706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816739 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 3, 1, 3]
def baseStart_3816739 : Nat := 118140960795 + 3816739 * 2 ^ 59
def prefixEnd_3816739 : Nat := 4983230072969 + 3 ^ 40 * 3816739 * 2
def baseEnd_3816739 : Nat := 1959821639760847724809643

theorem tailTrace_3816739 : CollatzResearch.WordTrace tailWord_3816739 prefixEnd_3816739 1959821639760847724809643 := by
  unfold tailWord_3816739
  simp only [CollatzResearch.WordTrace]
  refine ⟨139207907719613924970109271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92805271813075949980072847 139207907719613924970109271)
  ·
    refine ⟨208811861579420887455163907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139207907719613924970109271 208811861579420887455163907)
    ·
      refine ⟨313217792369131331182745861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208811861579420887455163907 313217792369131331182745861)
      ·
        refine ⟨58728336069212124596764849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313217792369131331182745861 58728336069212124596764849)
        ·
          refine ⟨44046252051909093447573637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58728336069212124596764849 44046252051909093447573637)
          ·
            refine ⟨8258672259732955021420057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44046252051909093447573637 8258672259732955021420057)
            ·
              refine ⟨6194004194799716266065043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8258672259732955021420057 6194004194799716266065043)
              ·
                refine ⟨9291006292199574399097565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6194004194799716266065043 9291006292199574399097565)
                ·
                  refine ⟨3484127359574840399661587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9291006292199574399097565 3484127359574840399661587)
                  ·
                    refine ⟨5226191039362260599492381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3484127359574840399661587 5226191039362260599492381)
                    ·
                      refine ⟨1959821639760847724809643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5226191039362260599492381 1959821639760847724809643)
                      ·
                        rfl

theorem cell23_3816739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_3816739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816739 prefixEnd_3816739 := by exact prefixLift 3816739
  have htrace : WordTrace (prefixWord ++ tailWord_3816739) baseStart_3816739 baseEnd_3816739 := by
    simpa [prefixWord, tailWord_3816739, baseEnd_3816739] using wordTrace_append hprefix tailTrace_3816739
  have hstable : (prefixWord ++ tailWord_3816739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816739).length < 2 ^ (prefixWord ++ tailWord_3816739).sum := by decide
  have hdescent : baseEnd_3816739 < baseStart_3816739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816762 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2]
def baseStart_3816762 : Nat := 118140960795 + 3816762 * 2 ^ 59
def prefixEnd_3816762 : Nat := 4983230072969 + 3 ^ 40 * 3816762 * 2
def baseEnd_3816762 : Nat := 1959833449815901134822037

theorem tailTrace_3816762 : CollatzResearch.WordTrace tailWord_3816762 prefixEnd_3816762 1959833449815901134822037 := by
  unfold tailWord_3816762
  simp only [CollatzResearch.WordTrace]
  refine ⟨34802186649632649974549135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92805831065687066598797693 34802186649632649974549135)
  ·
    refine ⟨52203279974448974961823703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34802186649632649974549135 52203279974448974961823703)
    ·
      refine ⟨78304919961673462442735555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52203279974448974961823703 78304919961673462442735555)
      ·
        refine ⟨117457379942510193664103333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78304919961673462442735555 117457379942510193664103333)
        ·
          refine ⟨22023258739220661312019375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117457379942510193664103333 22023258739220661312019375)
          ·
            refine ⟨33034888108830991968029063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22023258739220661312019375 33034888108830991968029063)
            ·
              refine ⟨49552332163246487952043595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33034888108830991968029063 49552332163246487952043595)
              ·
                refine ⟨74328498244869731928065393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49552332163246487952043595 74328498244869731928065393)
                ·
                  refine ⟨55746373683652298946049045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74328498244869731928065393 55746373683652298946049045)
                  ·
                    refine ⟨2613111266421201513096049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55746373683652298946049045 2613111266421201513096049)
                    ·
                      refine ⟨1959833449815901134822037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2613111266421201513096049 1959833449815901134822037)
                      ·
                        rfl

theorem cell23_3816762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2].length) (baseStart_3816762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816762 prefixEnd_3816762 := by exact prefixLift 3816762
  have htrace : WordTrace (prefixWord ++ tailWord_3816762) baseStart_3816762 baseEnd_3816762 := by
    simpa [prefixWord, tailWord_3816762, baseEnd_3816762] using wordTrace_append hprefix tailTrace_3816762
  have hstable : (prefixWord ++ tailWord_3816762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816762).length < 2 ^ (prefixWord ++ tailWord_3816762).sum := by decide
  have hdescent : baseEnd_3816762 < baseStart_3816762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816782 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5]
def baseStart_3816782 : Nat := 118140960795 + 3816782 * 2 ^ 59
def prefixEnd_3816782 : Nat := 4983230072969 + 3 ^ 40 * 3816782 * 2
def baseEnd_3816782 : Nat := 1959843719428991056571945

theorem tailTrace_3816782 : CollatzResearch.WordTrace tailWord_3816782 prefixEnd_3816782 1959843719428991056571945 := by
  unfold tailWord_3816782
  simp only [CollatzResearch.WordTrace]
  refine ⟨17401184507307267914240575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92806317372305428875949733 17401184507307267914240575)
  ·
    refine ⟨26101776760960901871360863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17401184507307267914240575 26101776760960901871360863)
    ·
      refine ⟨39152665141441352807041295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26101776760960901871360863 39152665141441352807041295)
      ·
        refine ⟨58728997712162029210561943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39152665141441352807041295 58728997712162029210561943)
        ·
          refine ⟨88093496568243043815842915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58728997712162029210561943 88093496568243043815842915)
          ·
            refine ⟨132140244852364565723764373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88093496568243043815842915 132140244852364565723764373)
            ·
              refine ⟨6194073977454589018301455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132140244852364565723764373 6194073977454589018301455)
              ·
                refine ⟨9291110966181883527452183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6194073977454589018301455 9291110966181883527452183)
                ·
                  refine ⟨13936666449272825291178275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9291110966181883527452183 13936666449272825291178275)
                  ·
                    refine ⟨20904999673909237936767413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13936666449272825291178275 20904999673909237936767413)
                    ·
                      refine ⟨1959843719428991056571945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20904999673909237936767413 1959843719428991056571945)
                      ·
                        rfl

theorem cell23_3816782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_3816782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816782 prefixEnd_3816782 := by exact prefixLift 3816782
  have htrace : WordTrace (prefixWord ++ tailWord_3816782) baseStart_3816782 baseEnd_3816782 := by
    simpa [prefixWord, tailWord_3816782, baseEnd_3816782] using wordTrace_append hprefix tailTrace_3816782
  have hstable : (prefixWord ++ tailWord_3816782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816782).length < 2 ^ (prefixWord ++ tailWord_3816782).sum := by decide
  have hdescent : baseEnd_3816782 < baseStart_3816782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816802 : List Nat := [3, 3, 2, 1, 1, 1, 4, 8]
def baseStart_3816802 : Nat := 118140960795 + 3816802 * 2 ^ 59
def prefixEnd_3816802 : Nat := 4983230072969 + 3 ^ 40 * 3816802 * 2
def baseEnd_3816802 : Nat := 72587184779336332530439

theorem tailTrace_3816802 : CollatzResearch.WordTrace tailWord_3816802 prefixEnd_3816802 72587184779336332530439 := by
  unfold tailWord_3816802
  simp only [CollatzResearch.WordTrace]
  refine ⟨34802551379596421682413165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92806803678923791153101773 34802551379596421682413165)
  ·
    refine ⟨13050956767348658130904937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34802551379596421682413165 13050956767348658130904937)
    ·
      refine ⟨9788217575511493598178703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13050956767348658130904937 9788217575511493598178703)
      ·
        refine ⟨14682326363267240397268055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9788217575511493598178703 14682326363267240397268055)
        ·
          refine ⟨22023489544900860595902083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14682326363267240397268055 22023489544900860595902083)
          ·
            refine ⟨33035234317351290893853125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22023489544900860595902083 33035234317351290893853125)
            ·
              refine ⟨6194106434503367042597461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33035234317351290893853125 6194106434503367042597461)
              ·
                refine ⟨72587184779336332530439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6194106434503367042597461 72587184779336332530439)
                ·
                  rfl

theorem cell23_3816802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 8].length) (baseStart_3816802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816802 prefixEnd_3816802 := by exact prefixLift 3816802
  have htrace : WordTrace (prefixWord ++ tailWord_3816802) baseStart_3816802 baseEnd_3816802 := by
    simpa [prefixWord, tailWord_3816802, baseEnd_3816802] using wordTrace_append hprefix tailTrace_3816802
  have hstable : (prefixWord ++ tailWord_3816802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816802).length < 2 ^ (prefixWord ++ tailWord_3816802).sum := by decide
  have hdescent : baseEnd_3816802 < baseStart_3816802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816805 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 2, 2, 6]
def baseStart_3816805 : Nat := 118140960795 + 3816805 * 2 ^ 59
def prefixEnd_3816805 : Nat := 4983230072969 + 3 ^ 40 * 3816805 * 2
def baseEnd_3816805 : Nat := 1959855529484044466584339

theorem tailTrace_3816805 : CollatzResearch.WordTrace tailWord_3816805 prefixEnd_3816805 1959855529484044466584339 := by
  unfold tailWord_3816805
  simp only [CollatzResearch.WordTrace]
  refine ⟨139210314937374818242011869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92806876624916545494674579 139210314937374818242011869)
  ·
    refine ⟨52203868101515556840754451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139210314937374818242011869 52203868101515556840754451)
    ·
      refine ⟨78305802152273335261131677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52203868101515556840754451 78305802152273335261131677)
      ·
        refine ⟨29364675807102500722924379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78305802152273335261131677 29364675807102500722924379)
        ·
          refine ⟨44047013710653751084386569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29364675807102500722924379 44047013710653751084386569)
          ·
            refine ⟨33035260282990313313289927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44047013710653751084386569 33035260282990313313289927)
            ·
              refine ⟨49552890424485469969934891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33035260282990313313289927 49552890424485469969934891)
              ·
                refine ⟨74329335636728204954902337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49552890424485469969934891 74329335636728204954902337)
                ·
                  refine ⟨55747001727546153716176753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74329335636728204954902337 55747001727546153716176753)
                  ·
                    refine ⟨41810251295659615287132565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55747001727546153716176753 41810251295659615287132565)
                    ·
                      refine ⟨1959855529484044466584339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41810251295659615287132565 1959855529484044466584339)
                      ·
                        rfl

theorem cell23_3816805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_3816805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816805 prefixEnd_3816805 := by exact prefixLift 3816805
  have htrace : WordTrace (prefixWord ++ tailWord_3816805) baseStart_3816805 baseEnd_3816805 := by
    simpa [prefixWord, tailWord_3816805, baseEnd_3816805] using wordTrace_append hprefix tailTrace_3816805
  have hstable : (prefixWord ++ tailWord_3816805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816805).length < 2 ^ (prefixWord ++ tailWord_3816805).sum := by decide
  have hdescent : baseEnd_3816805 < baseStart_3816805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816825 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 1, 4, 5]
def baseStart_3816825 : Nat := 118140960795 + 3816825 * 2 ^ 59
def prefixEnd_3816825 : Nat := 4983230072969 + 3 ^ 40 * 3816825 * 2
def baseEnd_3816825 : Nat := 1959865799097134388334247

theorem tailTrace_3816825 : CollatzResearch.WordTrace tailWord_3816825 prefixEnd_3816825 1959865799097134388334247 := by
  unfold tailWord_3816825
  simp only [CollatzResearch.WordTrace]
  refine ⟨139211044397302361657739929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92807362931534907771826619 139211044397302361657739929)
  ·
    refine ⟨104408283297976771243304947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139211044397302361657739929 104408283297976771243304947)
    ·
      refine ⟨156612424946965156864957421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104408283297976771243304947 156612424946965156864957421)
      ·
        refine ⟨58729659355111933824359033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156612424946965156864957421 58729659355111933824359033)
        ·
          refine ⟨44047244516333950368269275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58729659355111933824359033 44047244516333950368269275)
          ·
            refine ⟨66070866774500925552403913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44047244516333950368269275 66070866774500925552403913)
            ·
              refine ⟨49553150080875694164302935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66070866774500925552403913 49553150080875694164302935)
              ·
                refine ⟨74329725121313541246454403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49553150080875694164302935 74329725121313541246454403)
                ·
                  refine ⟨111494587681970311869681605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74329725121313541246454403 111494587681970311869681605)
                  ·
                    refine ⟨20905235190369433475565301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111494587681970311869681605 20905235190369433475565301)
                    ·
                      refine ⟨1959865799097134388334247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20905235190369433475565301 1959865799097134388334247)
                      ·
                        rfl

theorem cell23_3816825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_3816825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816825 prefixEnd_3816825 := by exact prefixLift 3816825
  have htrace : WordTrace (prefixWord ++ tailWord_3816825) baseStart_3816825 baseEnd_3816825 := by
    simpa [prefixWord, tailWord_3816825, baseEnd_3816825] using wordTrace_append hprefix tailTrace_3816825
  have hstable : (prefixWord ++ tailWord_3816825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816825).length < 2 ^ (prefixWord ++ tailWord_3816825).sum := by decide
  have hdescent : baseEnd_3816825 < baseStart_3816825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816830 : List Nat := [4, 2, 3, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_3816830 : Nat := 118140960795 + 3816830 * 2 ^ 59
def prefixEnd_3816830 : Nat := 4983230072969 + 3 ^ 40 * 3816830 * 2
def baseEnd_3816830 : Nat := 1959868366500406868771725

theorem tailTrace_3816830 : CollatzResearch.WordTrace tailWord_3816830 prefixEnd_3816830 1959868366500406868771725 := by
  unfold tailWord_3816830
  simp only [CollatzResearch.WordTrace]
  refine ⟨17401403345285530938958993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92807484508189498341114629 17401403345285530938958993)
  ·
    refine ⟨13051052508964148204219245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17401403345285530938958993 13051052508964148204219245)
    ·
      refine ⟨4894144690861555576582217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13051052508964148204219245 4894144690861555576582217)
      ·
        refine ⟨3670608518146166682436663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4894144690861555576582217 3670608518146166682436663)
        ·
          refine ⟨5505912777219250023654995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3670608518146166682436663 5505912777219250023654995)
          ·
            refine ⟨8258869165828875035482493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5505912777219250023654995 8258869165828875035482493)
            ·
              refine ⟨3097075937185828138305935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8258869165828875035482493 3097075937185828138305935)
              ·
                refine ⟨4645613905778742207458903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3097075937185828138305935 4645613905778742207458903)
                ·
                  refine ⟨6968420858668113311188355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4645613905778742207458903 6968420858668113311188355)
                  ·
                    refine ⟨10452631288002169966782533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6968420858668113311188355 10452631288002169966782533)
                    ·
                      refine ⟨1959868366500406868771725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10452631288002169966782533 1959868366500406868771725)
                      ·
                        rfl

theorem cell23_3816830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_3816830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816830 prefixEnd_3816830 := by exact prefixLift 3816830
  have htrace : WordTrace (prefixWord ++ tailWord_3816830) baseStart_3816830 baseEnd_3816830 := by
    simpa [prefixWord, tailWord_3816830, baseEnd_3816830] using wordTrace_append hprefix tailTrace_3816830
  have hstable : (prefixWord ++ tailWord_3816830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816830).length < 2 ^ (prefixWord ++ tailWord_3816830).sum := by decide
  have hdescent : baseEnd_3816830 < baseStart_3816830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816833 : List Nat := [1, 2, 4, 3, 2, 1, 3, 1, 1, 2, 3]
def baseStart_3816833 : Nat := 118140960795 + 3816833 * 2 ^ 59
def prefixEnd_3816833 : Nat := 4983230072969 + 3 ^ 40 * 3816833 * 2
def baseEnd_3816833 : Nat := 1959869906942370357034211

theorem tailTrace_3816833 : CollatzResearch.WordTrace tailWord_3816833 prefixEnd_3816833 1959869906942370357034211 := by
  unfold tailWord_3816833
  simp only [CollatzResearch.WordTrace]
  refine ⟨139211336181273379024031153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92807557454182252682687435 139211336181273379024031153)
  ·
    refine ⟨104408502135955034268023365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139211336181273379024031153 104408502135955034268023365)
    ·
      refine ⟨19576594150491568925254381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104408502135955034268023365 19576594150491568925254381)
      ·
        refine ⟨7341222806434338346970393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19576594150491568925254381 7341222806434338346970393)
        ·
          refine ⟨5505917104825753760227795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7341222806434338346970393 5505917104825753760227795)
          ·
            refine ⟨8258875657238630640341693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5505917104825753760227795 8258875657238630640341693)
            ·
              refine ⟨3097078371464486490128135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8258875657238630640341693 3097078371464486490128135)
              ·
                refine ⟨4645617557196729735192203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3097078371464486490128135 4645617557196729735192203)
                ·
                  refine ⟨6968426335795094602788305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4645617557196729735192203 6968426335795094602788305)
                  ·
                    refine ⟨5226319751846320952091229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6968426335795094602788305 5226319751846320952091229)
                    ·
                      refine ⟨1959869906942370357034211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5226319751846320952091229 1959869906942370357034211)
                      ·
                        rfl

theorem cell23_3816833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_3816833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816833 prefixEnd_3816833 := by exact prefixLift 3816833
  have htrace : WordTrace (prefixWord ++ tailWord_3816833) baseStart_3816833 baseEnd_3816833 := by
    simpa [prefixWord, tailWord_3816833, baseEnd_3816833] using wordTrace_append hprefix tailTrace_3816833
  have hstable : (prefixWord ++ tailWord_3816833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816833).length < 2 ^ (prefixWord ++ tailWord_3816833).sum := by decide
  have hdescent : baseEnd_3816833 < baseStart_3816833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816922 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 1, 7]
def baseStart_3816922 : Nat := 118140960795 + 3816922 * 2 ^ 59
def prefixEnd_3816922 : Nat := 4983230072969 + 3 ^ 40 * 3816922 * 2
def baseEnd_3816922 : Nat := 653305202240206836273767

theorem tailTrace_3816922 : CollatzResearch.WordTrace tailWord_3816922 prefixEnd_3816922 653305202240206836273767 := by
  unfold tailWord_3816922
  simp only [CollatzResearch.WordTrace]
  refine ⟨34803645569487736806005255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92809721518633964816014013 34803645569487736806005255)
  ·
    refine ⟨52205468354231605209007883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34803645569487736806005255 52205468354231605209007883)
    ·
      refine ⟨78308202531347407813511825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52205468354231605209007883 78308202531347407813511825)
      ·
        refine ⟨58731151898510555860133869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78308202531347407813511825 58731151898510555860133869)
        ·
          refine ⟨22024181961941458447550201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58731151898510555860133869 22024181961941458447550201)
          ·
            refine ⟨16518136471456093835662651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22024181961941458447550201 16518136471456093835662651)
            ·
              refine ⟨24777204707184140753493977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16518136471456093835662651 24777204707184140753493977)
              ·
                refine ⟨18582903530388105565120483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24777204707184140753493977 18582903530388105565120483)
                ·
                  refine ⟨27874355295582158347680725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18582903530388105565120483 27874355295582158347680725)
                  ·
                    refine ⟨653305202240206836273767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27874355295582158347680725 653305202240206836273767)
                    ·
                      rfl

theorem cell23_3816922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_3816922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816922 prefixEnd_3816922 := by exact prefixLift 3816922
  have htrace : WordTrace (prefixWord ++ tailWord_3816922) baseStart_3816922 baseEnd_3816922 := by
    simpa [prefixWord, tailWord_3816922, baseEnd_3816922] using wordTrace_append hprefix tailTrace_3816922
  have hstable : (prefixWord ++ tailWord_3816922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816922).length < 2 ^ (prefixWord ++ tailWord_3816922).sum := by decide
  have hdescent : baseEnd_3816922 < baseStart_3816922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816959 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 2, 4, 2]
def baseStart_3816959 : Nat := 118140960795 + 3816959 * 2 ^ 59
def prefixEnd_3816959 : Nat := 4983230072969 + 3 ^ 40 * 3816959 * 2
def baseEnd_3816959 : Nat := 1959934605504836864058631

theorem tailTrace_3816959 : CollatzResearch.WordTrace tailWord_3816959 prefixEnd_3816959 1959934605504836864058631 := by
  unfold tailWord_3816959
  simp only [CollatzResearch.WordTrace]
  refine ⟨139215931778816902543117931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92810621185877935028745287 139215931778816902543117931)
  ·
    refine ⟨208823897668225353814676897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139215931778816902543117931 208823897668225353814676897)
    ·
      refine ⟨156617923251169015361007673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208823897668225353814676897 156617923251169015361007673)
      ·
        refine ⟨117463442438376761520755755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156617923251169015361007673 117463442438376761520755755)
        ·
          refine ⟨176195163657565142281133633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117463442438376761520755755 176195163657565142281133633)
          ·
            refine ⟨132146372743173856710850225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176195163657565142281133633 132146372743173856710850225)
            ·
              refine ⟨99109779557380392533137669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132146372743173856710850225 99109779557380392533137669)
              ·
                refine ⟨18583083667008823599963313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99109779557380392533137669 18583083667008823599963313)
                ·
                  refine ⟨13937312750256617699972485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18583083667008823599963313 13937312750256617699972485)
                  ·
                    refine ⟨2613246140673115818744841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13937312750256617699972485 2613246140673115818744841)
                    ·
                      refine ⟨1959934605504836864058631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2613246140673115818744841 1959934605504836864058631)
                      ·
                        rfl

theorem cell23_3816959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 4, 2].length) (baseStart_3816959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3816959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3816959 prefixEnd_3816959 := by exact prefixLift 3816959
  have htrace : WordTrace (prefixWord ++ tailWord_3816959) baseStart_3816959 baseEnd_3816959 := by
    simpa [prefixWord, tailWord_3816959, baseEnd_3816959] using wordTrace_append hprefix tailTrace_3816959
  have hstable : (prefixWord ++ tailWord_3816959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816959).length < 2 ^ (prefixWord ++ tailWord_3816959).sum := by decide
  have hdescent : baseEnd_3816959 < baseStart_3816959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817059 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 1, 6]
def baseStart_3817059 : Nat := 118140960795 + 3817059 * 2 ^ 59
def prefixEnd_3817059 : Nat := 4983230072969 + 3 ^ 40 * 3817059 * 2
def baseEnd_3817059 : Nat := 653328651190095490936057

theorem tailTrace_3817059 : CollatzResearch.WordTrace tailWord_3817059 prefixEnd_3817059 653328651190095490936057 := by
  unfold tailWord_3817059
  simp only [CollatzResearch.WordTrace]
  refine ⟨139219579078454619621758231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92813052718969746414505487 139219579078454619621758231)
  ·
    refine ⟨208829368617681929432637347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139219579078454619621758231 208829368617681929432637347)
    ·
      refine ⟨313244052926522894148956021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208829368617681929432637347 313244052926522894148956021)
      ·
        refine ⟨29366629961861521326464627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 313244052926522894148956021 29366629961861521326464627)
        ·
          refine ⟨44049944942792281989696941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29366629961861521326464627 44049944942792281989696941)
          ·
            refine ⟨16518729353547105746136353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44049944942792281989696941 16518729353547105746136353)
            ·
              refine ⟨12389047015160329309602265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16518729353547105746136353 12389047015160329309602265)
              ·
                refine ⟨9291785261370246982201699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12389047015160329309602265 9291785261370246982201699)
                ·
                  refine ⟨13937677892055370473302549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9291785261370246982201699 13937677892055370473302549)
                  ·
                    refine ⟨653328651190095490936057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13937677892055370473302549 653328651190095490936057)
                    ·
                      rfl

theorem cell23_3817059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 6].length) (baseStart_3817059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817059 prefixEnd_3817059 := by exact prefixLift 3817059
  have htrace : WordTrace (prefixWord ++ tailWord_3817059) baseStart_3817059 baseEnd_3817059 := by
    simpa [prefixWord, tailWord_3817059, baseEnd_3817059] using wordTrace_append hprefix tailTrace_3817059
  have hstable : (prefixWord ++ tailWord_3817059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817059).length < 2 ^ (prefixWord ++ tailWord_3817059).sum := by decide
  have hdescent : baseEnd_3817059 < baseStart_3817059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817060 : List Nat := [2, 3, 1, 1, 2, 4, 2, 3, 1, 1, 3]
def baseStart_3817060 : Nat := 118140960795 + 3817060 * 2 ^ 59
def prefixEnd_3817060 : Nat := 4983230072969 + 3 ^ 40 * 3817060 * 2
def baseEnd_3817060 : Nat := 1959986467050940968895667

theorem tailTrace_3817060 : CollatzResearch.WordTrace tailWord_3817060 prefixEnd_3817060 1959986467050940968895667 := by
  unfold tailWord_3817060
  simp only [CollatzResearch.WordTrace]
  refine ⟨69609807775725498396272317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92813077034300664528363089 69609807775725498396272317)
  ·
    refine ⟨26103677915897061898602119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69609807775725498396272317 26103677915897061898602119)
    ·
      refine ⟨39155516873845592847903179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26103677915897061898602119 39155516873845592847903179)
      ·
        refine ⟨58733275310768389271854769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39155516873845592847903179 58733275310768389271854769)
        ·
          refine ⟨44049956483076291953891077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58733275310768389271854769 44049956483076291953891077)
          ·
            refine ⟨8259366840576804741354577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44049956483076291953891077 8259366840576804741354577)
            ·
              refine ⟨6194525130432603556015933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8259366840576804741354577 6194525130432603556015933)
              ·
                refine ⟨2322946923912226333505975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6194525130432603556015933 2322946923912226333505975)
                ·
                  refine ⟨3484420385868339500258963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2322946923912226333505975 3484420385868339500258963)
                  ·
                    refine ⟨5226630578802509250388445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3484420385868339500258963 5226630578802509250388445)
                    ·
                      refine ⟨1959986467050940968895667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5226630578802509250388445 1959986467050940968895667)
                      ·
                        rfl

theorem cell23_3817060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_3817060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817060 prefixEnd_3817060 := by exact prefixLift 3817060
  have htrace : WordTrace (prefixWord ++ tailWord_3817060) baseStart_3817060 baseEnd_3817060 := by
    simpa [prefixWord, tailWord_3817060, baseEnd_3817060] using wordTrace_append hprefix tailTrace_3817060
  have hstable : (prefixWord ++ tailWord_3817060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817060).length < 2 ^ (prefixWord ++ tailWord_3817060).sum := by decide
  have hdescent : baseEnd_3817060 < baseStart_3817060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817083 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 3, 2, 2]
def baseStart_3817083 : Nat := 118140960795 + 3817083 * 2 ^ 59
def prefixEnd_3817083 : Nat := 4983230072969 + 3 ^ 40 * 3817083 * 2
def baseEnd_3817083 : Nat := 1959998277105994378908061

theorem tailTrace_3817083 : CollatzResearch.WordTrace tailWord_3817083 prefixEnd_3817083 1959998277105994378908061 := by
  unfold tailWord_3817083
  simp only [CollatzResearch.WordTrace]
  refine ⟨139220454430367671720631903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92813636286911781147087935 139220454430367671720631903)
  ·
    refine ⟨208830681645551507580947855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139220454430367671720631903 208830681645551507580947855)
    ·
      refine ⟨313246022468327261371421783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208830681645551507580947855 313246022468327261371421783)
      ·
        refine ⟨469869033702490892057132675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313246022468327261371421783 469869033702490892057132675)
        ·
          refine ⟨704803550553736338085699013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469869033702490892057132675 704803550553736338085699013)
          ·
            refine ⟨132150665728825563391068565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 704803550553736338085699013 132150665728825563391068565)
            ·
              refine ⟨6194562456038698283956339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132150665728825563391068565 6194562456038698283956339)
              ·
                refine ⟨9291843684058047425934509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6194562456038698283956339 9291843684058047425934509)
                ·
                  refine ⟨3484441381521767784725441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9291843684058047425934509 3484441381521767784725441)
                  ·
                    refine ⟨2613331036141325838544081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3484441381521767784725441 2613331036141325838544081)
                    ·
                      refine ⟨1959998277105994378908061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2613331036141325838544081 1959998277105994378908061)
                      ·
                        rfl

theorem cell23_3817083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 2, 2].length) (baseStart_3817083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817083 prefixEnd_3817083 := by exact prefixLift 3817083
  have htrace : WordTrace (prefixWord ++ tailWord_3817083) baseStart_3817083 baseEnd_3817083 := by
    simpa [prefixWord, tailWord_3817083, baseEnd_3817083] using wordTrace_append hprefix tailTrace_3817083
  have hstable : (prefixWord ++ tailWord_3817083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817083).length < 2 ^ (prefixWord ++ tailWord_3817083).sum := by decide
  have hdescent : baseEnd_3817083 < baseStart_3817083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817093 : List Nat := [1, 3, 1, 1, 4, 1, 5, 1, 2, 4]
def baseStart_3817093 : Nat := 118140960795 + 3817093 * 2 ^ 59
def prefixEnd_3817093 : Nat := 4983230072969 + 3 ^ 40 * 3817093 * 2
def baseEnd_3817093 : Nat := 653334470637513113261005

theorem tailTrace_3817093 : CollatzResearch.WordTrace tailWord_3817093 prefixEnd_3817093 653334470637513113261005 := by
  unfold tailWord_3817093
  simp only [CollatzResearch.WordTrace]
  refine ⟨139220819160331443428495933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92813879440220962285663955 139220819160331443428495933)
  ·
    refine ⟨52207807185124291285685975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139220819160331443428495933 52207807185124291285685975)
    ·
      refine ⟨78311710777686436928528963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52207807185124291285685975 78311710777686436928528963)
      ·
        refine ⟨117467566166529655392793445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78311710777686436928528963 117467566166529655392793445)
        ·
          refine ⟨22025168656224310386148771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117467566166529655392793445 22025168656224310386148771)
          ·
            refine ⟨33037752984336465579223157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22025168656224310386148771 33037752984336465579223157)
            ·
              refine ⟨3097289342281543648052171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33037752984336465579223157 3097289342281543648052171)
              ·
                refine ⟨4645934013422315472078257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3097289342281543648052171 4645934013422315472078257)
                ·
                  refine ⟨3484450510066736604058693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4645934013422315472078257 3484450510066736604058693)
                  ·
                    refine ⟨653334470637513113261005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3484450510066736604058693 653334470637513113261005)
                    ·
                      rfl

theorem cell23_3817093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_3817093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817093 prefixEnd_3817093 := by exact prefixLift 3817093
  have htrace : WordTrace (prefixWord ++ tailWord_3817093) baseStart_3817093 baseEnd_3817093 := by
    simpa [prefixWord, tailWord_3817093, baseEnd_3817093] using wordTrace_append hprefix tailTrace_3817093
  have hstable : (prefixWord ++ tailWord_3817093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817093).length < 2 ^ (prefixWord ++ tailWord_3817093).sum := by decide
  have hdescent : baseEnd_3817093 < baseStart_3817093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817106 : List Nat := [3, 2, 3, 1, 3, 1, 1, 9]
def baseStart_3817106 : Nat := 118140960795 + 3817106 * 2 ^ 59
def prefixEnd_3817106 : Nat := 4983230072969 + 3 ^ 40 * 3817106 * 2
def baseEnd_3817106 : Nat := 72592966191149918108165

theorem tailTrace_3817106 : CollatzResearch.WordTrace tailWord_3817106 prefixEnd_3817106 72592966191149918108165 := by
  unfold tailWord_3817106
  simp only [CollatzResearch.WordTrace]
  refine ⟨34805323327321086662179793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92814195539522897765812781 34805323327321086662179793)
  ·
    refine ⟨26103992495490814996634845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34805323327321086662179793 26103992495490814996634845)
    ·
      refine ⟨9788997185809055623738067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26103992495490814996634845 9788997185809055623738067)
      ·
        refine ⟨14683495778713583435607101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9788997185809055623738067 14683495778713583435607101)
        ·
          refine ⟨5506310917017593788352663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14683495778713583435607101 5506310917017593788352663)
          ·
            refine ⟨8259466375526390682528995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5506310917017593788352663 8259466375526390682528995)
            ·
              refine ⟨12389199563289586023793493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8259466375526390682528995 12389199563289586023793493)
              ·
                refine ⟨72592966191149918108165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12389199563289586023793493 72592966191149918108165)
                ·
                  rfl

theorem cell23_3817106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 9].length) (baseStart_3817106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817106 prefixEnd_3817106 := by exact prefixLift 3817106
  have htrace : WordTrace (prefixWord ++ tailWord_3817106) baseStart_3817106 baseEnd_3817106 := by
    simpa [prefixWord, tailWord_3817106, baseEnd_3817106] using wordTrace_append hprefix tailTrace_3817106
  have hstable : (prefixWord ++ tailWord_3817106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817106).length < 2 ^ (prefixWord ++ tailWord_3817106).sum := by decide
  have hdescent : baseEnd_3817106 < baseStart_3817106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817133 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_3817133 : Nat := 118140960795 + 3817133 * 2 ^ 59
def prefixEnd_3817133 : Nat := 4983230072969 + 3 ^ 40 * 3817133 * 2
def baseEnd_3817133 : Nat := 1960023951138719183282831

theorem tailTrace_3817133 : CollatzResearch.WordTrace tailWord_3817133 prefixEnd_3817133 1960023951138719183282831 := by
  unfold tailWord_3817133
  simp only [CollatzResearch.WordTrace]
  refine ⟨139222278080186530259952053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92814852053457686839968035 139222278080186530259952053)
  ·
    refine ⟨13052088570017487211870505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139222278080186530259952053 13052088570017487211870505)
    ·
      refine ⟨9789066427513115408902879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13052088570017487211870505 9789066427513115408902879)
      ·
        refine ⟨14683599641269673113354319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9789066427513115408902879 14683599641269673113354319)
        ·
          refine ⟨22025399461904509670031479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14683599641269673113354319 22025399461904509670031479)
          ·
            refine ⟨33038099192856764505047219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22025399461904509670031479 33038099192856764505047219)
            ·
              refine ⟨49557148789285146757570829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33038099192856764505047219 49557148789285146757570829)
              ·
                refine ⟨18583930795981930034089061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49557148789285146757570829 18583930795981930034089061)
                ·
                  refine ⟨3484487024246611881391699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18583930795981930034089061 3484487024246611881391699)
                  ·
                    refine ⟨5226730536369917822087549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3484487024246611881391699 5226730536369917822087549)
                    ·
                      refine ⟨1960023951138719183282831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5226730536369917822087549 1960023951138719183282831)
                      ·
                        rfl

theorem cell23_3817133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_3817133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817133 prefixEnd_3817133 := by exact prefixLift 3817133
  have htrace : WordTrace (prefixWord ++ tailWord_3817133) baseStart_3817133 baseEnd_3817133 := by
    simpa [prefixWord, tailWord_3817133, baseEnd_3817133] using wordTrace_append hprefix tailTrace_3817133
  have hstable : (prefixWord ++ tailWord_3817133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817133).length < 2 ^ (prefixWord ++ tailWord_3817133).sum := by decide
  have hdescent : baseEnd_3817133 < baseStart_3817133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817134 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_3817134 : Nat := 118140960795 + 3817134 * 2 ^ 59
def prefixEnd_3817134 : Nat := 4983230072969 + 3 ^ 40 * 3817134 * 2
def baseEnd_3817134 : Nat := 1960024464619373679370327

theorem tailTrace_3817134 : CollatzResearch.WordTrace tailWord_3817134 prefixEnd_3817134 1960024464619373679370327 := by
  unfold tailWord_3817134
  simp only [CollatzResearch.WordTrace]
  refine ⟨17402789319147863428842307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92814876368788604953825637 17402789319147863428842307)
  ·
    refine ⟨26104183978721795143263461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17402789319147863428842307 26104183978721795143263461)
    ·
      refine ⟨4894534496010336589361899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26104183978721795143263461 4894534496010336589361899)
      ·
        refine ⟨7341801744015504884042849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4894534496010336589361899 7341801744015504884042849)
        ·
          refine ⟨5506351308011628663032137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7341801744015504884042849 5506351308011628663032137)
          ·
            refine ⟨4129763481008721497274103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5506351308011628663032137 4129763481008721497274103)
            ·
              refine ⟨6194645221513082245911155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4129763481008721497274103 6194645221513082245911155)
              ·
                refine ⟨9291967832269623368866733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6194645221513082245911155 9291967832269623368866733)
                ·
                  refine ⟨3484487937101108763325025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9291967832269623368866733 3484487937101108763325025)
                  ·
                    refine ⟨2613365952825831572493769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3484487937101108763325025 2613365952825831572493769)
                    ·
                      refine ⟨1960024464619373679370327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2613365952825831572493769 1960024464619373679370327)
                      ·
                        rfl

theorem cell23_3817134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_3817134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817134 prefixEnd_3817134 := by exact prefixLift 3817134
  have htrace : WordTrace (prefixWord ++ tailWord_3817134) baseStart_3817134 baseEnd_3817134 := by
    simpa [prefixWord, tailWord_3817134, baseEnd_3817134] using wordTrace_append hprefix tailTrace_3817134
  have hstable : (prefixWord ++ tailWord_3817134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817134).length < 2 ^ (prefixWord ++ tailWord_3817134).sum := by decide
  have hdescent : baseEnd_3817134 < baseStart_3817134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817139 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 4]
def baseStart_3817139 : Nat := 118140960795 + 3817139 * 2 ^ 59
def prefixEnd_3817139 : Nat := 4983230072969 + 3 ^ 40 * 3817139 * 2
def baseEnd_3817139 : Nat := 1960027032022646159807803

theorem tailTrace_3817139 : CollatzResearch.WordTrace tailWord_3817139 prefixEnd_3817139 1960027032022646159807803 := by
  unfold tailWord_3817139
  simp only [CollatzResearch.WordTrace]
  refine ⟨139222496918164793284670471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92814997945443195523113647 139222496918164793284670471)
  ·
    refine ⟨208833745377247189927005707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139222496918164793284670471 208833745377247189927005707)
    ·
      refine ⟨313250618065870784890508561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208833745377247189927005707 313250618065870784890508561)
      ·
        refine ⟨234937963549403088667881421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313250618065870784890508561 234937963549403088667881421)
        ·
          refine ⟨88101736331026158250455533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234937963549403088667881421 88101736331026158250455533)
          ·
            refine ⟨33038151124134809343920825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88101736331026158250455533 33038151124134809343920825)
            ·
              refine ⟨24778613343101107007940619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33038151124134809343920825 24778613343101107007940619)
              ·
                refine ⟨37167920014651660511910929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24778613343101107007940619 37167920014651660511910929)
                ·
                  refine ⟨27875940010988745383933197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37167920014651660511910929 27875940010988745383933197)
                  ·
                    refine ⟨10453477504120779518974949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27875940010988745383933197 10453477504120779518974949)
                    ·
                      refine ⟨1960027032022646159807803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10453477504120779518974949 1960027032022646159807803)
                      ·
                        rfl

theorem cell23_3817139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_3817139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817139 prefixEnd_3817139 := by exact prefixLift 3817139
  have htrace : WordTrace (prefixWord ++ tailWord_3817139) baseStart_3817139 baseEnd_3817139 := by
    simpa [prefixWord, tailWord_3817139, baseEnd_3817139] using wordTrace_append hprefix tailTrace_3817139
  have hstable : (prefixWord ++ tailWord_3817139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817139).length < 2 ^ (prefixWord ++ tailWord_3817139).sum := by decide
  have hdescent : baseEnd_3817139 < baseStart_3817139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817149 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 1, 8]
def baseStart_3817149 : Nat := 118140960795 + 3817149 * 2 ^ 59
def prefixEnd_3817149 : Nat := 4983230072969 + 3 ^ 40 * 3817149 * 2
def baseEnd_3817149 : Nat := 653344055609730373560919

theorem tailTrace_3817149 : CollatzResearch.WordTrace tailWord_3817149 prefixEnd_3817149 653344055609730373560919 := by
  unfold tailWord_3817149
  simp only [CollatzResearch.WordTrace]
  refine ⟨139222861648128564992534501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92815241098752376661689667 139222861648128564992534501)
  ·
    refine ⟨26104286559024105936100219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139222861648128564992534501 26104286559024105936100219)
    ·
      refine ⟨39156429838536158904150329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26104286559024105936100219 39156429838536158904150329)
      ·
        refine ⟨29367322378902119178112747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39156429838536158904150329 29367322378902119178112747)
        ·
          refine ⟨44050983568353178767169121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29367322378902119178112747 44050983568353178767169121)
          ·
            refine ⟨33038237676264884075376841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44050983568353178767169121 33038237676264884075376841)
            ·
              refine ⟨24778678257198663056532631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33038237676264884075376841 24778678257198663056532631)
              ·
                refine ⟨37168017385797994584798947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24778678257198663056532631 37168017385797994584798947)
                ·
                  refine ⟨55752026078696991877198421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37168017385797994584798947 55752026078696991877198421)
                  ·
                    refine ⟨653344055609730373560919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55752026078696991877198421 653344055609730373560919)
                    ·
                      rfl

theorem cell23_3817149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_3817149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817149 prefixEnd_3817149 := by exact prefixLift 3817149
  have htrace : WordTrace (prefixWord ++ tailWord_3817149) baseStart_3817149 baseEnd_3817149 := by
    simpa [prefixWord, tailWord_3817149, baseEnd_3817149] using wordTrace_append hprefix tailTrace_3817149
  have hstable : (prefixWord ++ tailWord_3817149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817149).length < 2 ^ (prefixWord ++ tailWord_3817149).sum := by decide
  have hdescent : baseEnd_3817149 < baseStart_3817149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817150 : List Nat := [4, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_3817150 : Nat := 118140960795 + 3817150 * 2 ^ 59
def prefixEnd_3817150 : Nat := 4983230072969 + 3 ^ 40 * 3817150 * 2
def baseEnd_3817150 : Nat := 1960032680309845616770253

theorem tailTrace_3817150 : CollatzResearch.WordTrace tailWord_3817150 prefixEnd_3817150 1960032680309845616770253 := by
  unfold tailWord_3817150
  simp only [CollatzResearch.WordTrace]
  refine ⟨17402862265140617770415113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92815265414083294775547269 17402862265140617770415113)
  ·
    refine ⟨13052146698855463327811335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17402862265140617770415113 13052146698855463327811335)
    ·
      refine ⟨19578220048283194991717003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13052146698855463327811335 19578220048283194991717003)
      ·
        refine ⟨29367330072424792487575505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19578220048283194991717003 29367330072424792487575505)
        ·
          refine ⟨22025497554318594365681629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29367330072424792487575505 22025497554318594365681629)
          ·
            refine ⟨8259561582869472887130611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22025497554318594365681629 8259561582869472887130611)
            ·
              refine ⟨12389342374304209330695917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8259561582869472887130611 12389342374304209330695917)
              ·
                refine ⟨4646003390364078499010969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12389342374304209330695917 4646003390364078499010969)
                ·
                  refine ⟨3484502542773058874258227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4646003390364078499010969 3484502542773058874258227)
                  ·
                    refine ⟨5226753814159588311387341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3484502542773058874258227 5226753814159588311387341)
                    ·
                      refine ⟨1960032680309845616770253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5226753814159588311387341 1960032680309845616770253)
                      ·
                        rfl

theorem cell23_3817150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_3817150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817150 prefixEnd_3817150 := by exact prefixLift 3817150
  have htrace : WordTrace (prefixWord ++ tailWord_3817150) baseStart_3817150 baseEnd_3817150 := by
    simpa [prefixWord, tailWord_3817150, baseEnd_3817150] using wordTrace_append hprefix tailTrace_3817150
  have hstable : (prefixWord ++ tailWord_3817150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817150).length < 2 ^ (prefixWord ++ tailWord_3817150).sum := by decide
  have hdescent : baseEnd_3817150 < baseStart_3817150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817159 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_3817159 : Nat := 118140960795 + 3817159 * 2 ^ 59
def prefixEnd_3817159 : Nat := 4983230072969 + 3 ^ 40 * 3817159 * 2
def baseEnd_3817159 : Nat := 1960037301635736081557711

theorem tailTrace_3817159 : CollatzResearch.WordTrace tailWord_3817159 prefixEnd_3817159 1960037301635736081557711 := by
  unfold tailWord_3817159
  simp only [CollatzResearch.WordTrace]
  refine ⟨139223226378092336700398531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92815484252061557800265687 139223226378092336700398531)
  ·
    refine ⟨208834839567138505050597797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139223226378092336700398531 208834839567138505050597797)
    ·
      refine ⟨39156532418838469696987087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208834839567138505050597797 39156532418838469696987087)
      ·
        refine ⟨58734798628257704545480631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39156532418838469696987087 58734798628257704545480631)
        ·
          refine ⟨88102197942386556818220947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58734798628257704545480631 88102197942386556818220947)
          ·
            refine ⟨132153296913579835227331421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88102197942386556818220947 132153296913579835227331421)
            ·
              refine ⟨49557486342592438210249283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132153296913579835227331421 49557486342592438210249283)
              ·
                refine ⟨74336229513888657315373925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49557486342592438210249283 74336229513888657315373925)
                ·
                  refine ⟨13938043033854123246632611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74336229513888657315373925 13938043033854123246632611)
                  ·
                    refine ⟨20907064550781184869948917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13938043033854123246632611 20907064550781184869948917)
                    ·
                      refine ⟨1960037301635736081557711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20907064550781184869948917 1960037301635736081557711)
                      ·
                        rfl

theorem cell23_3817159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_3817159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817159 prefixEnd_3817159 := by exact prefixLift 3817159
  have htrace : WordTrace (prefixWord ++ tailWord_3817159) baseStart_3817159 baseEnd_3817159 := by
    simpa [prefixWord, tailWord_3817159, baseEnd_3817159] using wordTrace_append hprefix tailTrace_3817159
  have hstable : (prefixWord ++ tailWord_3817159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817159).length < 2 ^ (prefixWord ++ tailWord_3817159).sum := by decide
  have hdescent : baseEnd_3817159 < baseStart_3817159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817219 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 7]
def baseStart_3817219 : Nat := 118140960795 + 3817219 * 2 ^ 59
def prefixEnd_3817219 : Nat := 4983230072969 + 3 ^ 40 * 3817219 * 2
def baseEnd_3817219 : Nat := 1960068110475005846807435

theorem tailTrace_3817219 : CollatzResearch.WordTrace tailWord_3817219 prefixEnd_3817219 1960068110475005846807435 := by
  unfold tailWord_3817219
  simp only [CollatzResearch.WordTrace]
  refine ⟨139225414757874966947582711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92816943171916644631721807 139225414757874966947582711)
  ·
    refine ⟨208838122136812450421374067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139225414757874966947582711 208838122136812450421374067)
    ·
      refine ⟨313257183205218675632061101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208838122136812450421374067 313257183205218675632061101)
      ·
        refine ⟨117471443701957003362022913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313257183205218675632061101 117471443701957003362022913)
        ·
          refine ⟨88103582776467752521517185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117471443701957003362022913 88103582776467752521517185)
          ·
            refine ⟨66077687082350814391137889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88103582776467752521517185 66077687082350814391137889)
            ·
              refine ⟨49558265311763110793353417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66077687082350814391137889 49558265311763110793353417)
              ·
                refine ⟨37168698983822333095015063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49558265311763110793353417 37168698983822333095015063)
                ·
                  refine ⟨55753048475733499642522595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37168698983822333095015063 55753048475733499642522595)
                  ·
                    refine ⟨83629572713600249463783893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55753048475733499642522595 83629572713600249463783893)
                    ·
                      refine ⟨1960068110475005846807435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83629572713600249463783893 1960068110475005846807435)
                      ·
                        rfl

theorem cell23_3817219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_3817219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817219 prefixEnd_3817219 := by exact prefixLift 3817219
  have htrace : WordTrace (prefixWord ++ tailWord_3817219) baseStart_3817219 baseEnd_3817219 := by
    simpa [prefixWord, tailWord_3817219, baseEnd_3817219] using wordTrace_append hprefix tailTrace_3817219
  have hstable : (prefixWord ++ tailWord_3817219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817219).length < 2 ^ (prefixWord ++ tailWord_3817219).sum := by decide
  have hdescent : baseEnd_3817219 < baseStart_3817219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817226 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 1, 7]
def baseStart_3817226 : Nat := 118140960795 + 3817226 * 2 ^ 59
def prefixEnd_3817226 : Nat := 4983230072969 + 3 ^ 40 * 3817226 * 2
def baseEnd_3817226 : Nat := 653357234946529106473301

theorem tailTrace_3817226 : CollatzResearch.WordTrace tailWord_3817226 prefixEnd_3817226 653357234946529106473301 := by
  unfold tailWord_3817226
  simp only [CollatzResearch.WordTrace]
  refine ⟨34806417517212401785771883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92817113379233071428725021 34806417517212401785771883)
  ·
    refine ⟨52209626275818602678657825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34806417517212401785771883 52209626275818602678657825)
    ·
      refine ⟨39157219706863952008993369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52209626275818602678657825 39157219706863952008993369)
      ·
        refine ⟨29367914780147964006745027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39157219706863952008993369 29367914780147964006745027)
        ·
          refine ⟨44051872170221946010117541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29367914780147964006745027 44051872170221946010117541)
          ·
            refine ⟨8259726031916614876897039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44051872170221946010117541 8259726031916614876897039)
            ·
              refine ⟨12389589047874922315345559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8259726031916614876897039 12389589047874922315345559)
              ·
                refine ⟨18584383571812383473018339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12389589047874922315345559 18584383571812383473018339)
                ·
                  refine ⟨27876575357718575209527509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18584383571812383473018339 27876575357718575209527509)
                  ·
                    refine ⟨653357234946529106473301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27876575357718575209527509 653357234946529106473301)
                    ·
                      rfl

theorem cell23_3817226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_3817226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817226 prefixEnd_3817226 := by exact prefixLift 3817226
  have htrace : WordTrace (prefixWord ++ tailWord_3817226) baseStart_3817226 baseEnd_3817226 := by
    simpa [prefixWord, tailWord_3817226, baseEnd_3817226] using wordTrace_append hprefix tailTrace_3817226
  have hstable : (prefixWord ++ tailWord_3817226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817226).length < 2 ^ (prefixWord ++ tailWord_3817226).sum := by decide
  have hdescent : baseEnd_3817226 < baseStart_3817226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817259 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 6]
def baseStart_3817259 : Nat := 118140960795 + 3817259 * 2 ^ 59
def prefixEnd_3817259 : Nat := 4983230072969 + 3 ^ 40 * 3817259 * 2
def baseEnd_3817259 : Nat := 1960088649701185690307251

theorem tailTrace_3817259 : CollatzResearch.WordTrace tailWord_3817259 prefixEnd_3817259 1960088649701185690307251 := by
  unfold tailWord_3817259
  simp only [CollatzResearch.WordTrace]
  refine ⟨139226873677730053779038831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92817915785153369186025887 139226873677730053779038831)
  ·
    refine ⟨208840310516595080668558247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139226873677730053779038831 208840310516595080668558247)
    ·
      refine ⟨313260465774892621002837371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208840310516595080668558247 313260465774892621002837371)
      ·
        refine ⟨469890698662338931504256057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313260465774892621002837371 469890698662338931504256057)
        ·
          refine ⟨352418023996754198628192043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469890698662338931504256057 352418023996754198628192043)
          ·
            refine ⟨528627035995131297942288065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352418023996754198628192043 528627035995131297942288065)
            ·
              refine ⟨396470276996348473456716049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528627035995131297942288065 396470276996348473456716049)
              ·
                refine ⟨297352707747261355092537037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396470276996348473456716049 297352707747261355092537037)
                ·
                  refine ⟨111507265405223008159701389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297352707747261355092537037 111507265405223008159701389)
                  ·
                    refine ⟨41815224526958628059888021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111507265405223008159701389 41815224526958628059888021)
                    ·
                      refine ⟨1960088649701185690307251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41815224526958628059888021 1960088649701185690307251)
                      ·
                        rfl

theorem cell23_3817259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 6].length) (baseStart_3817259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817259 prefixEnd_3817259 := by exact prefixLift 3817259
  have htrace : WordTrace (prefixWord ++ tailWord_3817259) baseStart_3817259 baseEnd_3817259 := by
    simpa [prefixWord, tailWord_3817259, baseEnd_3817259] using wordTrace_append hprefix tailTrace_3817259
  have hstable : (prefixWord ++ tailWord_3817259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817259).length < 2 ^ (prefixWord ++ tailWord_3817259).sum := by decide
  have hdescent : baseEnd_3817259 < baseStart_3817259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817300 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_3817300 : Nat := 118140960795 + 3817300 * 2 ^ 59
def prefixEnd_3817300 : Nat := 4983230072969 + 3 ^ 40 * 3817300 * 2
def baseEnd_3817300 : Nat := 1960109702408020029894563

theorem tailTrace_3817300 : CollatzResearch.WordTrace tailWord_3817300 prefixEnd_3817300 1960109702408020029894563 := by
  unfold tailWord_3817300
  simp only [CollatzResearch.WordTrace]
  refine ⟨69614184535290758890640677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92818912713721011854187569 69614184535290758890640677)
  ·
    refine ⟨13052659600367017291995127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69614184535290758890640677 13052659600367017291995127)
    ·
      refine ⟨19578989400550525937992691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13052659600367017291995127 19578989400550525937992691)
      ·
        refine ⟨29368484100825788906989037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19578989400550525937992691 29368484100825788906989037)
        ·
          refine ⟨11013181537809670840120889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29368484100825788906989037 11013181537809670840120889)
          ·
            refine ⟨8259886153357253130090667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11013181537809670840120889 8259886153357253130090667)
            ·
              refine ⟨12389829230035879695136001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8259886153357253130090667 12389829230035879695136001)
              ·
                refine ⟨9292371922526909771352001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12389829230035879695136001 9292371922526909771352001)
                ·
                  refine ⟨6969278941895182328514001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9292371922526909771352001 6969278941895182328514001)
                  ·
                    refine ⟨5226959206421386746385501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6969278941895182328514001 5226959206421386746385501)
                    ·
                      refine ⟨1960109702408020029894563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5226959206421386746385501 1960109702408020029894563)
                      ·
                        rfl

theorem cell23_3817300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_3817300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817300 prefixEnd_3817300 := by exact prefixLift 3817300
  have htrace : WordTrace (prefixWord ++ tailWord_3817300) baseStart_3817300 baseEnd_3817300 := by
    simpa [prefixWord, tailWord_3817300, baseEnd_3817300] using wordTrace_append hprefix tailTrace_3817300
  have hstable : (prefixWord ++ tailWord_3817300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817300).length < 2 ^ (prefixWord ++ tailWord_3817300).sum := by decide
  have hdescent : baseEnd_3817300 < baseStart_3817300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817323 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 6, 3, 2]
def baseStart_3817323 : Nat := 118140960795 + 3817323 * 2 ^ 59
def prefixEnd_3817323 : Nat := 4983230072969 + 3 ^ 40 * 3817323 * 2
def baseEnd_3817323 : Nat := 1960121512463073439906957

theorem tailTrace_3817323 : CollatzResearch.WordTrace tailWord_3817323 prefixEnd_3817323 1960121512463073439906957 := by
  unfold tailWord_3817323
  simp only [CollatzResearch.WordTrace]
  refine ⟨139229207949498192709368623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92819471966332128472912415 139229207949498192709368623)
  ·
    refine ⟨208843811924247289064052935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139229207949498192709368623 208843811924247289064052935)
    ·
      refine ⟨313265717886370933596079403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208843811924247289064052935 313265717886370933596079403)
      ·
        refine ⟨469898576829556400394119105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313265717886370933596079403 469898576829556400394119105)
        ·
          refine ⟨352423932622167300295589329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469898576829556400394119105 352423932622167300295589329)
          ·
            refine ⟨264317949466625475221691997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352423932622167300295589329 264317949466625475221691997)
            ·
              refine ⟨99119231049984553208134499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264317949466625475221691997 99119231049984553208134499)
              ·
                refine ⟨148678846574976829812201749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99119231049984553208134499 148678846574976829812201749)
                ·
                  refine ⟨6969320933202038897446957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148678846574976829812201749 6969320933202038897446957)
                  ·
                    refine ⟨2613495349950764586542609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6969320933202038897446957 2613495349950764586542609)
                    ·
                      refine ⟨1960121512463073439906957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2613495349950764586542609 1960121512463073439906957)
                      ·
                        rfl

theorem cell23_3817323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 3, 2].length) (baseStart_3817323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817323 prefixEnd_3817323 := by exact prefixLift 3817323
  have htrace : WordTrace (prefixWord ++ tailWord_3817323) baseStart_3817323 baseEnd_3817323 := by
    simpa [prefixWord, tailWord_3817323, baseEnd_3817323] using wordTrace_append hprefix tailTrace_3817323
  have hstable : (prefixWord ++ tailWord_3817323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817323).length < 2 ^ (prefixWord ++ tailWord_3817323).sum := by decide
  have hdescent : baseEnd_3817323 < baseStart_3817323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817333 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 3, 5]
def baseStart_3817333 : Nat := 118140960795 + 3817333 * 2 ^ 59
def prefixEnd_3817333 : Nat := 4983230072969 + 3 ^ 40 * 3817333 * 2
def baseEnd_3817333 : Nat := 653375549089872800260637

theorem tailTrace_3817333 : CollatzResearch.WordTrace tailWord_3817333 prefixEnd_3817333 653375549089872800260637 := by
  unfold tailWord_3817333
  simp only [CollatzResearch.WordTrace]
  refine ⟨139229572679461964417232653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92819715119641309611488435 139229572679461964417232653)
  ·
    refine ⟨52211089754798236656462245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139229572679461964417232653 52211089754798236656462245)
    ·
      refine ⟨9789579329024669373086671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52211089754798236656462245 9789579329024669373086671)
      ·
        refine ⟨14684368993537004059630007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9789579329024669373086671 14684368993537004059630007)
        ·
          refine ⟨22026553490305506089445011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14684368993537004059630007 22026553490305506089445011)
          ·
            refine ⟨33039830235458259134167517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22026553490305506089445011 33039830235458259134167517)
            ·
              refine ⟨12389936338296847175312819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33039830235458259134167517 12389936338296847175312819)
              ·
                refine ⟨18584904507445270762969229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12389936338296847175312819 18584904507445270762969229)
                ·
                  refine ⟨6969339190291976536113461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18584904507445270762969229 6969339190291976536113461)
                  ·
                    refine ⟨653375549089872800260637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6969339190291976536113461 653375549089872800260637)
                    ·
                      rfl

theorem cell23_3817333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_3817333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817333 prefixEnd_3817333 := by exact prefixLift 3817333
  have htrace : WordTrace (prefixWord ++ tailWord_3817333) baseStart_3817333 baseEnd_3817333 := by
    simpa [prefixWord, tailWord_3817333, baseEnd_3817333] using wordTrace_append hprefix tailTrace_3817333
  have hstable : (prefixWord ++ tailWord_3817333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817333).length < 2 ^ (prefixWord ++ tailWord_3817333).sum := by decide
  have hdescent : baseEnd_3817333 < baseStart_3817333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817358 : List Nat := [4, 1, 1, 5, 2, 1, 2, 2, 1, 4]
def baseStart_3817358 : Nat := 118140960795 + 3817358 * 2 ^ 59
def prefixEnd_3817358 : Nat := 4983230072969 + 3 ^ 40 * 3817358 * 2
def baseEnd_3817358 : Nat := 653379828095326934323099

theorem tailTrace_3817358 : CollatzResearch.WordTrace tailWord_3817358 prefixEnd_3817358 653379828095326934323099 := by
  unfold tailWord_3817358
  simp only [CollatzResearch.WordTrace]
  refine ⟨17403810563046424210861591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92820323002914262457928485 17403810563046424210861591)
  ·
    refine ⟨26105715844569636316292387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17403810563046424210861591 26105715844569636316292387)
    ·
      refine ⟨39158573766854454474438581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26105715844569636316292387 39158573766854454474438581)
      ·
        refine ⟨3671116290642605106978617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39158573766854454474438581 3671116290642605106978617)
        ·
          refine ⟨2753337217981953830233963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3671116290642605106978617 2753337217981953830233963)
          ·
            refine ⟨4130005826972930745350945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753337217981953830233963 4130005826972930745350945)
            ·
              refine ⟨3097504370229698059013209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4130005826972930745350945 3097504370229698059013209)
              ·
                refine ⟨2323128277672273544259907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3097504370229698059013209 2323128277672273544259907)
                ·
                  refine ⟨3484692416508410316389861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2323128277672273544259907 3484692416508410316389861)
                  ·
                    refine ⟨653379828095326934323099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3484692416508410316389861 653379828095326934323099)
                    ·
                      rfl

theorem cell23_3817358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_3817358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817358 prefixEnd_3817358 := by exact prefixLift 3817358
  have htrace : WordTrace (prefixWord ++ tailWord_3817358) baseStart_3817358 baseEnd_3817358 := by
    simpa [prefixWord, tailWord_3817358, baseEnd_3817358] using wordTrace_append hprefix tailTrace_3817358
  have hstable : (prefixWord ++ tailWord_3817358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817358).length < 2 ^ (prefixWord ++ tailWord_3817358).sum := by decide
  have hdescent : baseEnd_3817358 < baseStart_3817358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817364 : List Nat := [2, 4, 2, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_3817364 : Nat := 118140960795 + 3817364 * 2 ^ 59
def prefixEnd_3817364 : Nat := 4983230072969 + 3 ^ 40 * 3817364 * 2
def baseEnd_3817364 : Nat := 1960142565169907779494269

theorem tailTrace_3817364 : CollatzResearch.WordTrace tailWord_3817364 prefixEnd_3817364 1960142565169907779494269 := by
  unfold tailWord_3817364
  simp only [CollatzResearch.WordTrace]
  refine ⟨69615351671174828355805573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92820468894899771141074097 69615351671174828355805573)
  ·
    refine ⟨13052878438345280316713545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69615351671174828355805573 13052878438345280316713545)
    ·
      refine ⟨9789658828758960237535159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13052878438345280316713545 9789658828758960237535159)
      ·
        refine ⟨14684488243138440356302739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9789658828758960237535159 14684488243138440356302739)
        ·
          refine ⟨22026732364707660534454109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14684488243138440356302739 22026732364707660534454109)
          ·
            refine ⟨8260024636765372700420291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22026732364707660534454109 8260024636765372700420291)
            ·
              refine ⟨12390036955148059050630437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8260024636765372700420291 12390036955148059050630437)
              ·
                refine ⟨2323131929090261071993207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12390036955148059050630437 2323131929090261071993207)
                ·
                  refine ⟨3484697893635391607989811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2323131929090261071993207 3484697893635391607989811)
                  ·
                    refine ⟨5227046840453087411984717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3484697893635391607989811 5227046840453087411984717)
                    ·
                      refine ⟨1960142565169907779494269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5227046840453087411984717 1960142565169907779494269)
                      ·
                        rfl

theorem cell23_3817364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_3817364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817364 prefixEnd_3817364 := by exact prefixLift 3817364
  have htrace : WordTrace (prefixWord ++ tailWord_3817364) baseStart_3817364 baseEnd_3817364 := by
    simpa [prefixWord, tailWord_3817364, baseEnd_3817364] using wordTrace_append hprefix tailTrace_3817364
  have hstable : (prefixWord ++ tailWord_3817364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817364).length < 2 ^ (prefixWord ++ tailWord_3817364).sum := by decide
  have hdescent : baseEnd_3817364 < baseStart_3817364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817380 : List Nat := [2, 3, 1, 2, 1, 3, 2, 3, 2, 4]
def baseStart_3817380 : Nat := 118140960795 + 3817380 * 2 ^ 59
def prefixEnd_3817380 : Nat := 4983230072969 + 3 ^ 40 * 3817380 * 2
def baseEnd_3817380 : Nat := 653383593620126572298065

theorem tailTrace_3817380 : CollatzResearch.WordTrace tailWord_3817380 prefixEnd_3817380 653383593620126572298065 := by
  unfold tailWord_3817380
  simp only [CollatzResearch.WordTrace]
  refine ⟨69615643455145845722096797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92820857940194460962795729 69615643455145845722096797)
  ·
    refine ⟨26105866295679692145786299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69615643455145845722096797 26105866295679692145786299)
    ·
      refine ⟨39158799443519538218679449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26105866295679692145786299 39158799443519538218679449)
      ·
        refine ⟨29369099582639653664009587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39158799443519538218679449 29369099582639653664009587)
        ·
          refine ⟨44053649373959480496014381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29369099582639653664009587 44053649373959480496014381)
          ·
            refine ⟨16520118515234805186005393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44053649373959480496014381 16520118515234805186005393)
            ·
              refine ⟨12390088886426103889504045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16520118515234805186005393 12390088886426103889504045)
              ·
                refine ⟨4646283332409788958564017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12390088886426103889504045 4646283332409788958564017)
                ·
                  refine ⟨3484712499307341718923013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4646283332409788958564017 3484712499307341718923013)
                  ·
                    refine ⟨653383593620126572298065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3484712499307341718923013 653383593620126572298065)
                    ·
                      rfl

theorem cell23_3817380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_3817380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817380 prefixEnd_3817380 := by exact prefixLift 3817380
  have htrace : WordTrace (prefixWord ++ tailWord_3817380) baseStart_3817380 baseEnd_3817380 := by
    simpa [prefixWord, tailWord_3817380, baseEnd_3817380] using wordTrace_append hprefix tailTrace_3817380
  have hstable : (prefixWord ++ tailWord_3817380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817380).length < 2 ^ (prefixWord ++ tailWord_3817380).sum := by decide
  have hdescent : baseEnd_3817380 < baseStart_3817380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817477 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 4, 2, 2]
def baseStart_3817477 : Nat := 118140960795 + 3817477 * 2 ^ 59
def prefixEnd_3817477 : Nat := 4983230072969 + 3 ^ 40 * 3817477 * 2
def baseEnd_3817477 : Nat := 1960200588483865837381249

theorem tailTrace_3817477 : CollatzResearch.WordTrace tailWord_3817477 prefixEnd_3817477 1960200588483865837381249 := by
  unfold tailWord_3817477
  simp only [CollatzResearch.WordTrace]
  refine ⟨139234824790940277010474685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92823216527293518006983123 139234824790940277010474685)
  ·
    refine ⟨52213059296602603878928007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139234824790940277010474685 52213059296602603878928007)
    ·
      refine ⟨78319588944903905818392011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52213059296602603878928007 78319588944903905818392011)
      ·
        refine ⟨117479383417355858727588017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78319588944903905818392011 117479383417355858727588017)
        ·
          refine ⟨88109537563016894045691013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117479383417355858727588017 88109537563016894045691013)
          ·
            refine ⟨16520538293065667633567065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88109537563016894045691013 16520538293065667633567065)
            ·
              refine ⟨12390403719799250725175299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16520538293065667633567065 12390403719799250725175299)
              ·
                refine ⟨18585605579698876087762949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12390403719799250725175299 18585605579698876087762949)
                ·
                  refine ⟨3484801046193539266455553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18585605579698876087762949 3484801046193539266455553)
                  ·
                    refine ⟨2613600784645154449841665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3484801046193539266455553 2613600784645154449841665)
                    ·
                      refine ⟨1960200588483865837381249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2613600784645154449841665 1960200588483865837381249)
                      ·
                        rfl

theorem cell23_3817477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 2, 2].length) (baseStart_3817477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817477 prefixEnd_3817477 := by exact prefixLift 3817477
  have htrace : WordTrace (prefixWord ++ tailWord_3817477) baseStart_3817477 baseEnd_3817477 := by
    simpa [prefixWord, tailWord_3817477, baseEnd_3817477] using wordTrace_append hprefix tailTrace_3817477
  have hstable : (prefixWord ++ tailWord_3817477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817477).length < 2 ^ (prefixWord ++ tailWord_3817477).sum := by decide
  have hdescent : baseEnd_3817477 < baseStart_3817477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817523 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 5]
def baseStart_3817523 : Nat := 118140960795 + 3817523 * 2 ^ 59
def prefixEnd_3817523 : Nat := 4983230072969 + 3 ^ 40 * 3817523 * 2
def baseEnd_3817523 : Nat := 1960224208593972657406037

theorem tailTrace_3817523 : CollatzResearch.WordTrace tailWord_3817523 prefixEnd_3817523 1960224208593972657406037 := by
  unfold tailWord_3817523
  simp only [CollatzResearch.WordTrace]
  refine ⟨139236502548773626866649223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92824335032515751244432815 139236502548773626866649223)
  ·
    refine ⟨208854753823160440299973835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139236502548773626866649223 208854753823160440299973835)
    ·
      refine ⟨313282130734740660449960753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208854753823160440299973835 313282130734740660449960753)
      ·
        refine ⟨234961598051055495337470565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313282130734740660449960753 234961598051055495337470565)
        ·
          refine ⟨44055299634572905375775731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234961598051055495337470565 44055299634572905375775731)
          ·
            refine ⟨66082949451859358063663597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44055299634572905375775731 66082949451859358063663597)
            ·
              refine ⟨24781106044447259273873849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66082949451859358063663597 24781106044447259273873849)
              ·
                refine ⟨18585829533335444455405387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24781106044447259273873849 18585829533335444455405387)
                ·
                  refine ⟨27878744300003166683108081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18585829533335444455405387 27878744300003166683108081)
                  ·
                    refine ⟨20909058225002375012331061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27878744300003166683108081 20909058225002375012331061)
                    ·
                      refine ⟨1960224208593972657406037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20909058225002375012331061 1960224208593972657406037)
                      ·
                        rfl

theorem cell23_3817523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_3817523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817523 prefixEnd_3817523 := by exact prefixLift 3817523
  have htrace : WordTrace (prefixWord ++ tailWord_3817523) baseStart_3817523 baseEnd_3817523 := by
    simpa [prefixWord, tailWord_3817523, baseEnd_3817523] using wordTrace_append hprefix tailTrace_3817523
  have hstable : (prefixWord ++ tailWord_3817523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817523).length < 2 ^ (prefixWord ++ tailWord_3817523).sum := by decide
  have hdescent : baseEnd_3817523 < baseStart_3817523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817534 : List Nat := [4, 2, 1, 3, 2, 1, 1, 4, 5]
def baseStart_3817534 : Nat := 118140960795 + 3817534 * 2 ^ 59
def prefixEnd_3817534 : Nat := 4983230072969 + 3 ^ 40 * 3817534 * 2
def baseEnd_3817534 : Nat := 217803317431241346040943

theorem tailTrace_3817534 : CollatzResearch.WordTrace tailWord_3817534 prefixEnd_3817534 217803317431241346040943 := by
  unfold tailWord_3817534
  simp only [CollatzResearch.WordTrace]
  refine ⟨17404612968966721968162457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92824602501155850496866437 17404612968966721968162457)
  ·
    refine ⟨13053459726725041476121843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17404612968966721968162457 13053459726725041476121843)
    ·
      refine ⟨19580189590087562214182765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13053459726725041476121843 19580189590087562214182765)
      ·
        refine ⟨7342571096282835830318537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19580189590087562214182765 7342571096282835830318537)
        ·
          refine ⟨5506928322212126872738903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7342571096282835830318537 5506928322212126872738903)
          ·
            refine ⟨8260392483318190309108355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5506928322212126872738903 8260392483318190309108355)
            ·
              refine ⟨12390588724977285463662533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8260392483318190309108355 12390588724977285463662533)
              ·
                refine ⟨2323235385933241024436725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12390588724977285463662533 2323235385933241024436725)
                ·
                  refine ⟨217803317431241346040943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2323235385933241024436725 217803317431241346040943)
                  ·
                    rfl

theorem cell23_3817534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_3817534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817534 prefixEnd_3817534 := by exact prefixLift 3817534
  have htrace : WordTrace (prefixWord ++ tailWord_3817534) baseStart_3817534 baseEnd_3817534 := by
    simpa [prefixWord, tailWord_3817534, baseEnd_3817534] using wordTrace_append hprefix tailTrace_3817534
  have hstable : (prefixWord ++ tailWord_3817534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817534).length < 2 ^ (prefixWord ++ tailWord_3817534).sum := by decide
  have hdescent : baseEnd_3817534 < baseStart_3817534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817537 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_3817537 : Nat := 118140960795 + 3817537 * 2 ^ 59
def prefixEnd_3817537 : Nat := 4983230072969 + 3 ^ 40 * 3817537 * 2
def baseEnd_3817537 : Nat := 1960231397323135602630973

theorem tailTrace_3817537 : CollatzResearch.WordTrace tailWord_3817537 prefixEnd_3817537 1960231397323135602630973 := by
  unfold tailWord_3817537
  simp only [CollatzResearch.WordTrace]
  refine ⟨139237013170722907257658865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92824675447148604838439243 139237013170722907257658865)
  ·
    refine ⟨104427759878042180443244149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139237013170722907257658865 104427759878042180443244149)
    ·
      refine ⟨9790102488566454416554139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104427759878042180443244149 9790102488566454416554139)
      ·
        refine ⟨14685153732849681624831209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9790102488566454416554139 14685153732849681624831209)
        ·
          refine ⟨11013865299637261218623407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14685153732849681624831209 11013865299637261218623407)
          ·
            refine ⟨16520797949455891827935111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11013865299637261218623407 16520797949455891827935111)
            ·
              refine ⟨24781196924183837741902667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16520797949455891827935111 24781196924183837741902667)
              ·
                refine ⟨37171795386275756612854001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24781196924183837741902667 37171795386275756612854001)
                ·
                  refine ⟨27878846539706817459640501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37171795386275756612854001 27878846539706817459640501)
                  ·
                    refine ⟨2613641863097514136841297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27878846539706817459640501 2613641863097514136841297)
                    ·
                      refine ⟨1960231397323135602630973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2613641863097514136841297 1960231397323135602630973)
                      ·
                        rfl

theorem cell23_3817537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_3817537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817537 prefixEnd_3817537 := by exact prefixLift 3817537
  have htrace : WordTrace (prefixWord ++ tailWord_3817537) baseStart_3817537 baseEnd_3817537 := by
    simpa [prefixWord, tailWord_3817537, baseEnd_3817537] using wordTrace_append hprefix tailTrace_3817537
  have hstable : (prefixWord ++ tailWord_3817537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817537).length < 2 ^ (prefixWord ++ tailWord_3817537).sum := by decide
  have hdescent : baseEnd_3817537 < baseStart_3817537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817560 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 5, 4]
def baseStart_3817560 : Nat := 118140960795 + 3817560 * 2 ^ 59
def prefixEnd_3817560 : Nat := 4983230072969 + 3 ^ 40 * 3817560 * 2
def baseEnd_3817560 : Nat := 653414402459396337547789

theorem tailTrace_3817560 : CollatzResearch.WordTrace tailWord_3817560 prefixEnd_3817560 653414402459396337547789 := by
  unfold tailWord_3817560
  simp only [CollatzResearch.WordTrace]
  refine ⟨69618926024819791092873067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92825234699759721457164089 69618926024819791092873067)
  ·
    refine ⟨104428389037229686639309601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69618926024819791092873067 104428389037229686639309601)
    ·
      refine ⟨78321291777922264979482201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104428389037229686639309601 78321291777922264979482201)
      ·
        refine ⟨58740968833441698734611651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78321291777922264979482201 58740968833441698734611651)
        ·
          refine ⟨88111453250162548101917477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58740968833441698734611651 88111453250162548101917477)
          ·
            refine ⟨16520897484405477769109527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88111453250162548101917477 16520897484405477769109527)
            ·
              refine ⟨24781346226608216653664291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16520897484405477769109527 24781346226608216653664291)
              ·
                refine ⟨37172019339912324980496437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24781346226608216653664291 37172019339912324980496437)
                ·
                  refine ⟨3484876813116780466921541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37172019339912324980496437 3484876813116780466921541)
                  ·
                    refine ⟨653414402459396337547789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3484876813116780466921541 653414402459396337547789)
                    ·
                      rfl

theorem cell23_3817560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_3817560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817560 prefixEnd_3817560 := by exact prefixLift 3817560
  have htrace : WordTrace (prefixWord ++ tailWord_3817560) baseStart_3817560 baseEnd_3817560 := by
    simpa [prefixWord, tailWord_3817560, baseEnd_3817560] using wordTrace_append hprefix tailTrace_3817560
  have hstable : (prefixWord ++ tailWord_3817560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817560).length < 2 ^ (prefixWord ++ tailWord_3817560).sum := by decide
  have hdescent : baseEnd_3817560 < baseStart_3817560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817674 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 5, 2, 2]
def baseStart_3817674 : Nat := 118140960795 + 3817674 * 2 ^ 59
def prefixEnd_3817674 : Nat := 4983230072969 + 3 ^ 40 * 3817674 * 2
def baseEnd_3817674 : Nat := 1960301744172801566617843

theorem tailTrace_3817674 : CollatzResearch.WordTrace tailWord_3817674 prefixEnd_3817674 1960301744172801566617843 := by
  unfold tailWord_3817674
  simp only [CollatzResearch.WordTrace]
  refine ⟨34810502492806644913849019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92828006647484386436930717 34810502492806644913849019)
  ·
    refine ⟨52215753739209967370773529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34810502492806644913849019 52215753739209967370773529)
    ·
      refine ⟨39161815304407475528080147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52215753739209967370773529 39161815304407475528080147)
      ·
        refine ⟨58742722956611213292120221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39161815304407475528080147 58742722956611213292120221)
        ·
          refine ⟨22028521108729204984545083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58742722956611213292120221 22028521108729204984545083)
          ·
            refine ⟨33042781663093807476817625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22028521108729204984545083 33042781663093807476817625)
            ·
              refine ⟨24782086247320355607613219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33042781663093807476817625 24782086247320355607613219)
              ·
                refine ⟨37173129370980533411419829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24782086247320355607613219 37173129370980533411419829)
                ·
                  refine ⟨3484980878529425007320609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37173129370980533411419829 3484980878529425007320609)
                  ·
                    refine ⟨2613735658897068755490457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3484980878529425007320609 2613735658897068755490457)
                    ·
                      refine ⟨1960301744172801566617843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2613735658897068755490457 1960301744172801566617843)
                      ·
                        rfl

theorem cell23_3817674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_3817674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817674 prefixEnd_3817674 := by exact prefixLift 3817674
  have htrace : WordTrace (prefixWord ++ tailWord_3817674) baseStart_3817674 baseEnd_3817674 := by
    simpa [prefixWord, tailWord_3817674, baseEnd_3817674] using wordTrace_append hprefix tailTrace_3817674
  have hstable : (prefixWord ++ tailWord_3817674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817674).length < 2 ^ (prefixWord ++ tailWord_3817674).sum := by decide
  have hdescent : baseEnd_3817674 < baseStart_3817674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817724 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 1, 3, 3]
def baseStart_3817724 : Nat := 118140960795 + 3817724 * 2 ^ 59
def prefixEnd_3817724 : Nat := 4983230072969 + 3 ^ 40 * 3817724 * 2
def baseEnd_3817724 : Nat := 1960327418205526370992613

theorem tailTrace_3817724 : CollatzResearch.WordTrace tailWord_3817724 prefixEnd_3817724 1960327418205526370992613 := by
  unfold tailWord_3817724
  simp only [CollatzResearch.WordTrace]
  refine ⟨69621916810522719097358113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92829222414030292129810817 69621916810522719097358113)
  ·
    refine ⟨52216437607892039323018585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69621916810522719097358113 52216437607892039323018585)
    ·
      refine ⟨39162328205919029492263939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52216437607892039323018585 39162328205919029492263939)
      ·
        refine ⟨58743492308878544238395909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39162328205919029492263939 58743492308878544238395909)
        ·
          refine ⟨11014404807914727044699233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58743492308878544238395909 11014404807914727044699233)
          ·
            refine ⟨8260803605936045283524425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11014404807914727044699233 8260803605936045283524425)
            ·
              refine ⟨6195602704452033962643319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8260803605936045283524425 6195602704452033962643319)
              ·
                refine ⟨9293404056678050943964979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6195602704452033962643319 9293404056678050943964979)
                ·
                  refine ⟨13940106085017076415947469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9293404056678050943964979 13940106085017076415947469)
                  ·
                    refine ⟨5227539781881403655980301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13940106085017076415947469 5227539781881403655980301)
                    ·
                      refine ⟨1960327418205526370992613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5227539781881403655980301 1960327418205526370992613)
                      ·
                        rfl

theorem cell23_3817724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_3817724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817724 prefixEnd_3817724 := by exact prefixLift 3817724
  have htrace : WordTrace (prefixWord ++ tailWord_3817724) baseStart_3817724 baseEnd_3817724 := by
    simpa [prefixWord, tailWord_3817724, baseEnd_3817724] using wordTrace_append hprefix tailTrace_3817724
  have hstable : (prefixWord ++ tailWord_3817724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817724).length < 2 ^ (prefixWord ++ tailWord_3817724).sum := by decide
  have hdescent : baseEnd_3817724 < baseStart_3817724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817740 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 1, 8]
def baseStart_3817740 : Nat := 118140960795 + 3817740 * 2 ^ 59
def prefixEnd_3817740 : Nat := 4983230072969 + 3 ^ 40 * 3817740 * 2
def baseEnd_3817740 : Nat := 653445211298666102797513

theorem tailTrace_3817740 : CollatzResearch.WordTrace tailWord_3817740 prefixEnd_3817740 653445211298666102797513 := by
  unfold tailWord_3817740
  simp only [CollatzResearch.WordTrace]
  refine ⟨69622208594493736463649337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92829611459324981951532449 69622208594493736463649337)
  ·
    refine ⟨52216656445870302347737003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69622208594493736463649337 52216656445870302347737003)
    ·
      refine ⟨78324984668805453521605505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52216656445870302347737003 78324984668805453521605505)
      ·
        refine ⟨58743738501604090141204129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78324984668805453521605505 58743738501604090141204129)
        ·
          refine ⟨44057803876203067605903097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58743738501604090141204129 44057803876203067605903097)
          ·
            refine ⟨33043352907152300704427323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44057803876203067605903097 33043352907152300704427323)
            ·
              refine ⟨49565029360728451056640985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33043352907152300704427323 49565029360728451056640985)
              ·
                refine ⟨37173772020546338292480739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49565029360728451056640985 37173772020546338292480739)
                ·
                  refine ⟨55760658030819507438721109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37173772020546338292480739 55760658030819507438721109)
                  ·
                    refine ⟨653445211298666102797513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55760658030819507438721109 653445211298666102797513)
                    ·
                      rfl

theorem cell23_3817740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_3817740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817740 prefixEnd_3817740 := by exact prefixLift 3817740
  have htrace : WordTrace (prefixWord ++ tailWord_3817740) baseStart_3817740 baseEnd_3817740 := by
    simpa [prefixWord, tailWord_3817740, baseEnd_3817740] using wordTrace_append hprefix tailTrace_3817740
  have hstable : (prefixWord ++ tailWord_3817740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817740).length < 2 ^ (prefixWord ++ tailWord_3817740).sum := by decide
  have hdescent : baseEnd_3817740 < baseStart_3817740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817751 : List Nat := [1, 1, 3, 4, 1, 3, 1, 3, 1, 3, 2]
def baseStart_3817751 : Nat := 118140960795 + 3817751 * 2 ^ 59
def prefixEnd_3817751 : Nat := 4983230072969 + 3 ^ 40 * 3817751 * 2
def baseEnd_3817751 : Nat := 1960341282183197765354989

theorem tailTrace_3817751 : CollatzResearch.WordTrace tailWord_3817751 prefixEnd_3817751 1960341282183197765354989 := by
  unfold tailWord_3817751
  simp only [CollatzResearch.WordTrace]
  refine ⟨139244818391947621805949107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92829878927965081203966071 139244818391947621805949107)
  ·
    refine ⟨208867227587921432708923661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139244818391947621805949107 208867227587921432708923661)
    ·
      refine ⟨78325210345470537265846373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208867227587921432708923661 78325210345470537265846373)
      ·
        refine ⟨14685976939775725737346195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78325210345470537265846373 14685976939775725737346195)
        ·
          refine ⟨22028965409663588606019293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14685976939775725737346195 22028965409663588606019293)
          ·
            refine ⟨8260862028623845727257235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22028965409663588606019293 8260862028623845727257235)
            ·
              refine ⟨12391293042935768590885853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8260862028623845727257235 12391293042935768590885853)
              ·
                refine ⟨4646734891100913221582195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12391293042935768590885853 4646734891100913221582195)
                ·
                  refine ⟨6970102336651369832373293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4646734891100913221582195 6970102336651369832373293)
                  ·
                    refine ⟨2613788376244263687139985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6970102336651369832373293 2613788376244263687139985)
                    ·
                      refine ⟨1960341282183197765354989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2613788376244263687139985 1960341282183197765354989)
                      ·
                        rfl

theorem cell23_3817751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_3817751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817751 prefixEnd_3817751 := by exact prefixLift 3817751
  have htrace : WordTrace (prefixWord ++ tailWord_3817751) baseStart_3817751 baseEnd_3817751 := by
    simpa [prefixWord, tailWord_3817751, baseEnd_3817751] using wordTrace_append hprefix tailTrace_3817751
  have hstable : (prefixWord ++ tailWord_3817751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817751).length < 2 ^ (prefixWord ++ tailWord_3817751).sum := by decide
  have hdescent : baseEnd_3817751 < baseStart_3817751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817758 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_3817758 : Nat := 118140960795 + 3817758 * 2 ^ 59
def prefixEnd_3817758 : Nat := 4983230072969 + 3 ^ 40 * 3817758 * 2
def baseEnd_3817758 : Nat := 1960344876547779237967457

theorem tailTrace_3817758 : CollatzResearch.WordTrace tailWord_3817758 prefixEnd_3817758 1960344876547779237967457 := by
  unfold tailWord_3817758
  simp only [CollatzResearch.WordTrace]
  refine ⟨17405634212865282750181741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92830049135281508000969285 17405634212865282750181741)
  ·
    refine ⟨6527112829824481031318153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17405634212865282750181741 6527112829824481031318153)
    ·
      refine ⟨4895334622368360773488615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6527112829824481031318153 4895334622368360773488615)
      ·
        refine ⟨7343001933552541160232923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4895334622368360773488615 7343001933552541160232923)
        ·
          refine ⟨11014502900328811740349385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7343001933552541160232923 11014502900328811740349385)
          ·
            refine ⟨8260877175246608805262039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11014502900328811740349385 8260877175246608805262039)
            ·
              refine ⟨12391315762869913207893059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8260877175246608805262039 12391315762869913207893059)
              ·
                refine ⟨18586973644304869811839589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12391315762869913207893059 18586973644304869811839589)
                ·
                  refine ⟨3485057558307163089719923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18586973644304869811839589 3485057558307163089719923)
                  ·
                    refine ⟨5227586337460744634579885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3485057558307163089719923 5227586337460744634579885)
                    ·
                      refine ⟨1960344876547779237967457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5227586337460744634579885 1960344876547779237967457)
                      ·
                        rfl

theorem cell23_3817758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_3817758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817758 prefixEnd_3817758 := by exact prefixLift 3817758
  have htrace : WordTrace (prefixWord ++ tailWord_3817758) baseStart_3817758 baseEnd_3817758 := by
    simpa [prefixWord, tailWord_3817758, baseEnd_3817758] using wordTrace_append hprefix tailTrace_3817758
  have hstable : (prefixWord ++ tailWord_3817758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817758).length < 2 ^ (prefixWord ++ tailWord_3817758).sum := by decide
  have hdescent : baseEnd_3817758 < baseStart_3817758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817827 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 5]
def baseStart_3817827 : Nat := 118140960795 + 3817827 * 2 ^ 59
def prefixEnd_3817827 : Nat := 4983230072969 + 3 ^ 40 * 3817827 * 2
def baseEnd_3817827 : Nat := 1960380306712939468004639

theorem tailTrace_3817827 : CollatzResearch.WordTrace tailWord_3817827 prefixEnd_3817827 1960380306712939468004639 := by
  unfold tailWord_3817827
  simp only [CollatzResearch.WordTrace]
  refine ⟨139247590339672286785715735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92831726893114857857143823 139247590339672286785715735)
  ·
    refine ⟨208871385509508430178573603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139247590339672286785715735 208871385509508430178573603)
    ·
      refine ⟨313307078264262645267860405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208871385509508430178573603 313307078264262645267860405)
      ·
        refine ⟨29372538587274622993861913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 313307078264262645267860405 29372538587274622993861913)
        ·
          refine ⟨22029403940455967245396435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29372538587274622993861913 22029403940455967245396435)
          ·
            refine ⟨33044105910683950868094653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22029403940455967245396435 33044105910683950868094653)
            ·
              refine ⟨12391539716506481575535495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33044105910683950868094653 12391539716506481575535495)
              ·
                refine ⟨18587309574759722363303243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12391539716506481575535495 18587309574759722363303243)
                ·
                  refine ⟨27880964362139583544954865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18587309574759722363303243 27880964362139583544954865)
                  ·
                    refine ⟨20910723271604687658716149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27880964362139583544954865 20910723271604687658716149)
                    ·
                      refine ⟨1960380306712939468004639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20910723271604687658716149 1960380306712939468004639)
                      ·
                        rfl

theorem cell23_3817827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_3817827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817827 prefixEnd_3817827 := by exact prefixLift 3817827
  have htrace : WordTrace (prefixWord ++ tailWord_3817827) baseStart_3817827 baseEnd_3817827 := by
    simpa [prefixWord, tailWord_3817827, baseEnd_3817827] using wordTrace_append hprefix tailTrace_3817827
  have hstable : (prefixWord ++ tailWord_3817827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817827).length < 2 ^ (prefixWord ++ tailWord_3817827).sum := by decide
  have hdescent : baseEnd_3817827 < baseStart_3817827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817881 : List Nat := [1, 2, 1, 2, 1, 4, 3, 4, 1, 4]
def baseStart_3817881 : Nat := 118140960795 + 3817881 * 2 ^ 59
def prefixEnd_3817881 : Nat := 4983230072969 + 3 ^ 40 * 3817881 * 2
def baseEnd_3817881 : Nat := 653469344889427418909797

theorem tailTrace_3817881 : CollatzResearch.WordTrace tailWord_3817881 prefixEnd_3817881 653469344889427418909797 := by
  unfold tailWord_3817881
  simp only [CollatzResearch.WordTrace]
  refine ⟨139249559881476654008181497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92833039920984436005454331 139249559881476654008181497)
  ·
    refine ⟨104437169911107490506136123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139249559881476654008181497 104437169911107490506136123)
    ·
      refine ⟨156655754866661235759204185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104437169911107490506136123 156655754866661235759204185)
      ·
        refine ⟨117491816149995926819403139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156655754866661235759204185 117491816149995926819403139)
        ·
          refine ⟨176237724224993890229104709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117491816149995926819403139 176237724224993890229104709)
          ·
            refine ⟨33044573292186354417957133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176237724224993890229104709 33044573292186354417957133)
            ·
              refine ⟨12391714984569882906733925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33044573292186354417957133 12391714984569882906733925)
              ·
                refine ⟨2323446559606853045012611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12391714984569882906733925 2323446559606853045012611)
                ·
                  refine ⟨3485169839410279567518917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2323446559606853045012611 3485169839410279567518917)
                  ·
                    refine ⟨653469344889427418909797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3485169839410279567518917 653469344889427418909797)
                    ·
                      rfl

theorem cell23_3817881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 1, 4].length) (baseStart_3817881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817881 prefixEnd_3817881 := by exact prefixLift 3817881
  have htrace : WordTrace (prefixWord ++ tailWord_3817881) baseStart_3817881 baseEnd_3817881 := by
    simpa [prefixWord, tailWord_3817881, baseEnd_3817881] using wordTrace_append hprefix tailTrace_3817881
  have hstable : (prefixWord ++ tailWord_3817881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817881).length < 2 ^ (prefixWord ++ tailWord_3817881).sum := by decide
  have hdescent : baseEnd_3817881 < baseStart_3817881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817937 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 3, 6]
def baseStart_3817937 : Nat := 118140960795 + 3817937 * 2 ^ 59
def prefixEnd_3817937 : Nat := 4983230072969 + 3 ^ 40 * 3817937 * 2
def baseEnd_3817937 : Nat := 653478929861644679209711

theorem tailTrace_3817937 : CollatzResearch.WordTrace tailWord_3817937 prefixEnd_3817937 653478929861644679209711 := by
  unfold tailWord_3817937
  simp only [CollatzResearch.WordTrace]
  refine ⟨139251602369273775572220065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92834401579515850381480043 139251602369273775572220065)
  ·
    refine ⟨104438701776955331679165049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139251602369273775572220065 104438701776955331679165049)
    ·
      refine ⟨78329026332716498759373787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104438701776955331679165049 78329026332716498759373787)
      ·
        refine ⟨117493539499074748139060681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78329026332716498759373787 117493539499074748139060681)
        ·
          refine ⟨88120154624306061104295511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117493539499074748139060681 88120154624306061104295511)
          ·
            refine ⟨132180231936459091656443267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88120154624306061104295511 132180231936459091656443267)
            ·
              refine ⟨198270347904688637484664901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132180231936459091656443267 198270347904688637484664901)
              ·
                refine ⟨37175690232129119528374669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198270347904688637484664901 37175690232129119528374669)
                ·
                  refine ⟨13940883837048419823140501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37175690232129119528374669 13940883837048419823140501)
                  ·
                    refine ⟨653478929861644679209711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13940883837048419823140501 653478929861644679209711)
                    ·
                      rfl

theorem cell23_3817937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_3817937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817937 prefixEnd_3817937 := by exact prefixLift 3817937
  have htrace : WordTrace (prefixWord ++ tailWord_3817937) baseStart_3817937 baseEnd_3817937 := by
    simpa [prefixWord, tailWord_3817937, baseEnd_3817937] using wordTrace_append hprefix tailTrace_3817937
  have hstable : (prefixWord ++ tailWord_3817937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817937).length < 2 ^ (prefixWord ++ tailWord_3817937).sum := by decide
  have hdescent : baseEnd_3817937 < baseStart_3817937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817961 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 5, 2, 2]
def baseStart_3817961 : Nat := 118140960795 + 3817961 * 2 ^ 59
def prefixEnd_3817961 : Nat := 4983230072969 + 3 ^ 40 * 3817961 * 2
def baseEnd_3817961 : Nat := 1960449113120641943729023

theorem tailTrace_3817961 : CollatzResearch.WordTrace tailWord_3817961 prefixEnd_3817961 1960449113120641943729023 := by
  unfold tailWord_3817961
  simp only [CollatzResearch.WordTrace]
  refine ⟨139252477721186827671093737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92834985147457885114062491 139252477721186827671093737)
  ·
    refine ⟨104439358290890120753320303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139252477721186827671093737 104439358290890120753320303)
    ·
      refine ⟨156659037436335181129980455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104439358290890120753320303 156659037436335181129980455)
      ·
        refine ⟨234988556154502771694970683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156659037436335181129980455 234988556154502771694970683)
        ·
          refine ⟨352482834231754157542456025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234988556154502771694970683 352482834231754157542456025)
          ·
            refine ⟨264362125673815618156842019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352482834231754157542456025 264362125673815618156842019)
            ·
              refine ⟨396543188510723427235263029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264362125673815618156842019 396543188510723427235263029)
              ·
                refine ⟨37175923922880321303305909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 396543188510723427235263029 37175923922880321303305909)
                ·
                  refine ⟨3485242867770030122184929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37175923922880321303305909 3485242867770030122184929)
                  ·
                    refine ⟨2613932150827522591638697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3485242867770030122184929 2613932150827522591638697)
                    ·
                      refine ⟨1960449113120641943729023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2613932150827522591638697 1960449113120641943729023)
                      ·
                        rfl

theorem cell23_3817961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 2, 2].length) (baseStart_3817961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817961 prefixEnd_3817961 := by exact prefixLift 3817961
  have htrace : WordTrace (prefixWord ++ tailWord_3817961) baseStart_3817961 baseEnd_3817961 := by
    simpa [prefixWord, tailWord_3817961, baseEnd_3817961] using wordTrace_append hprefix tailTrace_3817961
  have hstable : (prefixWord ++ tailWord_3817961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817961).length < 2 ^ (prefixWord ++ tailWord_3817961).sum := by decide
  have hdescent : baseEnd_3817961 < baseStart_3817961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817981 : List Nat := [1, 4, 1, 1, 1, 3, 1, 5, 1, 2, 3]
def baseStart_3817981 : Nat := 118140960795 + 3817981 * 2 ^ 59
def prefixEnd_3817981 : Nat := 4983230072969 + 3 ^ 40 * 3817981 * 2
def baseEnd_3817981 : Nat := 1960459382733731865478931

theorem tailTrace_3817981 : CollatzResearch.WordTrace tailWord_3817981 prefixEnd_3817981 1960459382733731865478931 := by
  unfold tailWord_3817981
  simp only [CollatzResearch.WordTrace]
  refine ⟨139253207181114371086821797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92835471454076247391214531 139253207181114371086821797)
  ·
    refine ⟨26109976346458944578779087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139253207181114371086821797 26109976346458944578779087)
    ·
      refine ⟨39164964519688416868168631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26109976346458944578779087 39164964519688416868168631)
      ·
        refine ⟨58747446779532625302252947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39164964519688416868168631 58747446779532625302252947)
        ·
          refine ⟨88121170169298937953379421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58747446779532625302252947 88121170169298937953379421)
          ·
            refine ⟨33045438813487101732517283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88121170169298937953379421 33045438813487101732517283)
            ·
              refine ⟨49568158220230652598775925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33045438813487101732517283 49568158220230652598775925)
              ·
                refine ⟨4647014833146623681135243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49568158220230652598775925 4647014833146623681135243)
                ·
                  refine ⟨6970522249719935521702865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4647014833146623681135243 6970522249719935521702865)
                  ·
                    refine ⟨5227891687289951641277149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6970522249719935521702865 5227891687289951641277149)
                    ·
                      refine ⟨1960459382733731865478931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5227891687289951641277149 1960459382733731865478931)
                      ·
                        rfl

theorem cell23_3817981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_3817981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817981 prefixEnd_3817981 := by exact prefixLift 3817981
  have htrace : WordTrace (prefixWord ++ tailWord_3817981) baseStart_3817981 baseEnd_3817981 := by
    simpa [prefixWord, tailWord_3817981, baseEnd_3817981] using wordTrace_append hprefix tailTrace_3817981
  have hstable : (prefixWord ++ tailWord_3817981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817981).length < 2 ^ (prefixWord ++ tailWord_3817981).sum := by decide
  have hdescent : baseEnd_3817981 < baseStart_3817981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817995 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 3, 2, 2]
def baseStart_3817995 : Nat := 118140960795 + 3817995 * 2 ^ 59
def prefixEnd_3817995 : Nat := 4983230072969 + 3 ^ 40 * 3817995 * 2
def baseEnd_3817995 : Nat := 1960466571462894810703867

theorem tailTrace_3817995 : CollatzResearch.WordTrace tailWord_3817995 prefixEnd_3817995 1960466571462894810703867 := by
  unfold tailWord_3817995
  simp only [CollatzResearch.WordTrace]
  refine ⟨139253717803063651477831439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92835811868709100985220959 139253717803063651477831439)
  ·
    refine ⟨208880576704595477216747159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139253717803063651477831439 208880576704595477216747159)
    ·
      refine ⟨313320865056893215825120739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208880576704595477216747159 313320865056893215825120739)
      ·
        refine ⟨469981297585339823737681109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313320865056893215825120739 469981297585339823737681109)
        ·
          refine ⟨11015186662156402118851901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 469981297585339823737681109 11015186662156402118851901)
          ·
            refine ⟨4130694998308650794569463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11015186662156402118851901 4130694998308650794569463)
            ·
              refine ⟨6196042497462976191854195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4130694998308650794569463 6196042497462976191854195)
              ·
                refine ⟨9294063746194464287781293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6196042497462976191854195 9294063746194464287781293)
                ·
                  refine ⟨3485273904822924107917985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9294063746194464287781293 3485273904822924107917985)
                  ·
                    refine ⟨2613955428617193080938489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3485273904822924107917985 2613955428617193080938489)
                    ·
                      refine ⟨1960466571462894810703867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2613955428617193080938489 1960466571462894810703867)
                      ·
                        rfl

theorem cell23_3817995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 2, 2].length) (baseStart_3817995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3817995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3817995 prefixEnd_3817995 := by exact prefixLift 3817995
  have htrace : WordTrace (prefixWord ++ tailWord_3817995) baseStart_3817995 baseEnd_3817995 := by
    simpa [prefixWord, tailWord_3817995, baseEnd_3817995] using wordTrace_append hprefix tailTrace_3817995
  have hstable : (prefixWord ++ tailWord_3817995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817995).length < 2 ^ (prefixWord ++ tailWord_3817995).sum := by decide
  have hdescent : baseEnd_3817995 < baseStart_3817995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818029 : List Nat := [1, 5, 4, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_3818029 : Nat := 118140960795 + 3818029 * 2 ^ 59
def prefixEnd_3818029 : Nat := 4983230072969 + 3 ^ 40 * 3818029 * 2
def baseEnd_3818029 : Nat := 1960484029805147677678711

theorem tailTrace_3818029 : CollatzResearch.WordTrace tailWord_3818029 prefixEnd_3818029 1960484029805147677678711 := by
  unfold tailWord_3818029
  simp only [CollatzResearch.WordTrace]
  refine ⟨139254957884940475284569141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92836638589960316856379427 139254957884940475284569141)
  ·
    refine ⟨13055152301713169557928357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139254957884940475284569141 13055152301713169557928357)
    ·
      refine ⟨2447841056571219292111567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13055152301713169557928357 2447841056571219292111567)
      ·
        refine ⟨3671761584856828938167351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2447841056571219292111567 3671761584856828938167351)
        ·
          refine ⟨5507642377285243407251027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3671761584856828938167351 5507642377285243407251027)
          ·
            refine ⟨8261463565927865110876541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5507642377285243407251027 8261463565927865110876541)
            ·
              refine ⟨3098048837222949416578703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8261463565927865110876541 3098048837222949416578703)
              ·
                refine ⟨4647073255834424124868055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098048837222949416578703 4647073255834424124868055)
                ·
                  refine ⟨6970609883751636187302083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4647073255834424124868055 6970609883751636187302083)
                  ·
                    refine ⟨10455914825627454280953125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6970609883751636187302083 10455914825627454280953125)
                    ·
                      refine ⟨1960484029805147677678711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10455914825627454280953125 1960484029805147677678711)
                      ·
                        rfl

theorem cell23_3818029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_3818029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818029 prefixEnd_3818029 := by exact prefixLift 3818029
  have htrace : WordTrace (prefixWord ++ tailWord_3818029) baseStart_3818029 baseEnd_3818029 := by
    simpa [prefixWord, tailWord_3818029, baseEnd_3818029] using wordTrace_append hprefix tailTrace_3818029
  have hstable : (prefixWord ++ tailWord_3818029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818029).length < 2 ^ (prefixWord ++ tailWord_3818029).sum := by decide
  have hdescent : baseEnd_3818029 < baseStart_3818029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818045 : List Nat := [1, 4, 1, 3, 2, 2, 2, 2, 2, 1, 3]
def baseStart_3818045 : Nat := 118140960795 + 3818045 * 2 ^ 59
def prefixEnd_3818045 : Nat := 4983230072969 + 3 ^ 40 * 3818045 * 2
def baseEnd_3818045 : Nat := 1960492245495619615078637

theorem tailTrace_3818045 : CollatzResearch.WordTrace tailWord_3818045 prefixEnd_3818045 1960492245495619615078637 := by
  unfold tailWord_3818045
  simp only [CollatzResearch.WordTrace]
  refine ⟨139255541452882510017151589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92837027635255006678101059 139255541452882510017151589)
  ·
    refine ⟨26110414022415470628215923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139255541452882510017151589 26110414022415470628215923)
    ·
      refine ⟨39165621033623205942323885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26110414022415470628215923 39165621033623205942323885)
      ·
        refine ⟨14687107887608702228371457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39165621033623205942323885 14687107887608702228371457)
        ·
          refine ⟨11015330915706526671278593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14687107887608702228371457 11015330915706526671278593)
          ·
            refine ⟨8261498186779895003458945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11015330915706526671278593 8261498186779895003458945)
            ·
              refine ⟨6196123640084921252594209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8261498186779895003458945 6196123640084921252594209)
              ·
                refine ⟨4647092730063690939445657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6196123640084921252594209 4647092730063690939445657)
                ·
                  refine ⟨3485319547547768204584243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4647092730063690939445657 3485319547547768204584243)
                  ·
                    refine ⟨5227979321321652306876365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3485319547547768204584243 5227979321321652306876365)
                    ·
                      refine ⟨1960492245495619615078637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5227979321321652306876365 1960492245495619615078637)
                      ·
                        rfl

theorem cell23_3818045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_3818045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818045 prefixEnd_3818045 := by exact prefixLift 3818045
  have htrace : WordTrace (prefixWord ++ tailWord_3818045) baseStart_3818045 baseEnd_3818045 := by
    simpa [prefixWord, tailWord_3818045, baseEnd_3818045] using wordTrace_append hprefix tailTrace_3818045
  have hstable : (prefixWord ++ tailWord_3818045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818045).length < 2 ^ (prefixWord ++ tailWord_3818045).sum := by decide
  have hdescent : baseEnd_3818045 < baseStart_3818045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818052 : List Nat := [2, 3, 5, 1, 2, 1, 1, 8]
def baseStart_3818052 : Nat := 118140960795 + 3818052 * 2 ^ 59
def prefixEnd_3818052 : Nat := 4983230072969 + 3 ^ 40 * 3818052 * 2
def baseEnd_3818052 : Nat := 72610957031859299544115

theorem tailTrace_3818052 : CollatzResearch.WordTrace tailWord_3818052 prefixEnd_3818052 72610957031859299544115 := by
  unfold tailWord_3818052
  simp only [CollatzResearch.WordTrace]
  refine ⟨69627898381928575106328205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92837197842571433475104273 69627898381928575106328205)
  ·
    refine ⟨26110461893223215664873077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69627898381928575106328205 26110461893223215664873077)
    ·
      refine ⟨2447855802489676468581851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26110461893223215664873077 2447855802489676468581851)
      ·
        refine ⟨3671783703734514702872777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2447855802489676468581851 3671783703734514702872777)
        ·
          refine ⟨2753837777800886027154583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3671783703734514702872777 2753837777800886027154583)
          ·
            refine ⟨4130756666701329040731875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753837777800886027154583 4130756666701329040731875)
            ·
              refine ⟨6196135000051993561097813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4130756666701329040731875 6196135000051993561097813)
              ·
                refine ⟨72610957031859299544115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6196135000051993561097813 72610957031859299544115)
                ·
                  rfl

theorem cell23_3818052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 8].length) (baseStart_3818052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818052 prefixEnd_3818052 := by exact prefixLift 3818052
  have htrace : WordTrace (prefixWord ++ tailWord_3818052) baseStart_3818052 baseEnd_3818052 := by
    simpa [prefixWord, tailWord_3818052, baseEnd_3818052] using wordTrace_append hprefix tailTrace_3818052
  have hstable : (prefixWord ++ tailWord_3818052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818052).length < 2 ^ (prefixWord ++ tailWord_3818052).sum := by decide
  have hdescent : baseEnd_3818052 < baseStart_3818052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818061 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_3818061 : Nat := 118140960795 + 3818061 * 2 ^ 59
def prefixEnd_3818061 : Nat := 4983230072969 + 3 ^ 40 * 3818061 * 2
def baseEnd_3818061 : Nat := 653500153728697184159521

theorem tailTrace_3818061 : CollatzResearch.WordTrace tailWord_3818061 prefixEnd_3818061 653500153728697184159521 := by
  unfold tailWord_3818061
  simp only [CollatzResearch.WordTrace]
  refine ⟨139256125020824544749734037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92837416680549696499822691 139256125020824544749734037)
  ·
    refine ⟨6527630860351150535143783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 139256125020824544749734037 6527630860351150535143783)
    ·
      refine ⟨9791446290526725802715675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6527630860351150535143783 9791446290526725802715675)
      ·
        refine ⟨14687169435790088704073513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9791446290526725802715675 14687169435790088704073513)
        ·
          refine ⟨11015377076842566528055135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14687169435790088704073513 11015377076842566528055135)
          ·
            refine ⟨16523065615263849792082703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11015377076842566528055135 16523065615263849792082703)
            ·
              refine ⟨24784598422895774688124055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16523065615263849792082703 24784598422895774688124055)
              ·
                refine ⟨37176897634343662032186083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24784598422895774688124055 37176897634343662032186083)
                ·
                  refine ⟨55765346451515493048279125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37176897634343662032186083 55765346451515493048279125)
                  ·
                    refine ⟨653500153728697184159521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55765346451515493048279125 653500153728697184159521)
                    ·
                      rfl

theorem cell23_3818061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_3818061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818061 prefixEnd_3818061 := by exact prefixLift 3818061
  have htrace : WordTrace (prefixWord ++ tailWord_3818061) baseStart_3818061 baseEnd_3818061 := by
    simpa [prefixWord, tailWord_3818061, baseEnd_3818061] using wordTrace_append hprefix tailTrace_3818061
  have hstable : (prefixWord ++ tailWord_3818061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818061).length < 2 ^ (prefixWord ++ tailWord_3818061).sum := by decide
  have hdescent : baseEnd_3818061 < baseStart_3818061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818068 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 1, 4, 2]
def baseStart_3818068 : Nat := 118140960795 + 3818068 * 2 ^ 59
def prefixEnd_3818068 : Nat := 4983230072969 + 3 ^ 40 * 3818068 * 2
def baseEnd_3818068 : Nat := 1960504055550673025091031

theorem tailTrace_3818068 : CollatzResearch.WordTrace tailWord_3818068 prefixEnd_3818068 1960504055550673025091031 := by
  unfold tailWord_3818068
  simp only [CollatzResearch.WordTrace]
  refine ⟨69628190165899592472619429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92837586887866123296825905 69628190165899592472619429)
  ·
    refine ⟨13055285656106173588616143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69628190165899592472619429 13055285656106173588616143)
    ·
      refine ⟨19582928484159260382924215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13055285656106173588616143 19582928484159260382924215)
      ·
        refine ⟨29374392726238890574386323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19582928484159260382924215 29374392726238890574386323)
        ·
          refine ⟨44061589089358335861579485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29374392726238890574386323 44061589089358335861579485)
          ·
            refine ⟨16523095908509375948092307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44061589089358335861579485 16523095908509375948092307)
            ·
              refine ⟨24784643862764063922138461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16523095908509375948092307 24784643862764063922138461)
              ·
                refine ⟨9294241448536523970801923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24784643862764063922138461 9294241448536523970801923)
                ·
                  refine ⟨13941362172804785956202885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9294241448536523970801923 13941362172804785956202885)
                  ·
                    refine ⟨2614005407400897366788041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13941362172804785956202885 2614005407400897366788041)
                    ·
                      refine ⟨1960504055550673025091031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2614005407400897366788041 1960504055550673025091031)
                      ·
                        rfl

theorem cell23_3818068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_3818068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818068 prefixEnd_3818068 := by exact prefixLift 3818068
  have htrace : WordTrace (prefixWord ++ tailWord_3818068) baseStart_3818068 baseEnd_3818068 := by
    simpa [prefixWord, tailWord_3818068, baseEnd_3818068] using wordTrace_append hprefix tailTrace_3818068
  have hstable : (prefixWord ++ tailWord_3818068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818068).length < 2 ^ (prefixWord ++ tailWord_3818068).sum := by decide
  have hdescent : baseEnd_3818068 < baseStart_3818068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818102 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2]
def baseStart_3818102 : Nat := 118140960795 + 3818102 * 2 ^ 59
def prefixEnd_3818102 : Nat := 4983230072969 + 3 ^ 40 * 3818102 * 2
def baseEnd_3818102 : Nat := 1960521513892925892065875

theorem tailTrace_3818102 : CollatzResearch.WordTrace tailWord_3818102 prefixEnd_3818102 1960521513892925892065875 := by
  unfold tailWord_3818102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8703601275854750546998535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92838413609117339167984373 8703601275854750546998535)
  ·
    refine ⟨13055401913782125820497803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8703601275854750546998535 13055401913782125820497803)
    ·
      refine ⟨19583102870673188730746705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13055401913782125820497803 19583102870673188730746705)
      ·
        refine ⟨14687327153004891548060029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19583102870673188730746705 14687327153004891548060029)
        ·
          refine ⟨5507747682376834330522511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14687327153004891548060029 5507747682376834330522511)
          ·
            refine ⟨8261621523565251495783767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5507747682376834330522511 8261621523565251495783767)
            ·
              refine ⟨12392432285347877243675651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8261621523565251495783767 12392432285347877243675651)
              ·
                refine ⟨18588648428021815865513477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12392432285347877243675651 18588648428021815865513477)
                ·
                  refine ⟨3485371580254090474783777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18588648428021815865513477 3485371580254090474783777)
                  ·
                    refine ⟨2614028685190567856087833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3485371580254090474783777 2614028685190567856087833)
                    ·
                      refine ⟨1960521513892925892065875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2614028685190567856087833 1960521513892925892065875)
                      ·
                        rfl

theorem cell23_3818102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_3818102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818102 prefixEnd_3818102 := by exact prefixLift 3818102
  have htrace : WordTrace (prefixWord ++ tailWord_3818102) baseStart_3818102 baseEnd_3818102 := by
    simpa [prefixWord, tailWord_3818102, baseEnd_3818102] using wordTrace_append hprefix tailTrace_3818102
  have hstable : (prefixWord ++ tailWord_3818102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818102).length < 2 ^ (prefixWord ++ tailWord_3818102).sum := by decide
  have hdescent : baseEnd_3818102 < baseStart_3818102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818111 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 2, 5, 2]
def baseStart_3818111 : Nat := 118140960795 + 3818111 * 2 ^ 59
def prefixEnd_3818111 : Nat := 4983230072969 + 3 ^ 40 * 3818111 * 2
def baseEnd_3818111 : Nat := 1960526135218816356853333

theorem tailTrace_3818111 : CollatzResearch.WordTrace tailWord_3818111 prefixEnd_3818111 1960526135218816356853333 := by
  unfold tailWord_3818111
  simp only [CollatzResearch.WordTrace]
  refine ⟨139257948670643403289054187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92838632447095602192702791 139257948670643403289054187)
  ·
    refine ⟨208886923005965104933581281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139257948670643403289054187 208886923005965104933581281)
    ·
      refine ⟨156665192254473828700185961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208886923005965104933581281 156665192254473828700185961)
      ·
        refine ⟨117498894190855371525139471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156665192254473828700185961 117498894190855371525139471)
        ·
          refine ⟨176248341286283057287709207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117498894190855371525139471 176248341286283057287709207)
          ·
            refine ⟨264372511929424585931563811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176248341286283057287709207 264372511929424585931563811)
            ·
              refine ⟨396558767894136878897345717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264372511929424585931563811 396558767894136878897345717)
              ·
                refine ⟨37177384490075332396626161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 396558767894136878897345717 37177384490075332396626161)
                ·
                  refine ⟨27883038367556499297469621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37177384490075332396626161 27883038367556499297469621)
                  ·
                    refine ⟨2614034846958421809137777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27883038367556499297469621 2614034846958421809137777)
                    ·
                      refine ⟨1960526135218816356853333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2614034846958421809137777 1960526135218816356853333)
                      ·
                        rfl

theorem cell23_3818111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 5, 2].length) (baseStart_3818111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818111 prefixEnd_3818111 := by exact prefixLift 3818111
  have htrace : WordTrace (prefixWord ++ tailWord_3818111) baseStart_3818111 baseEnd_3818111 := by
    simpa [prefixWord, tailWord_3818111, baseEnd_3818111] using wordTrace_append hprefix tailTrace_3818111
  have hstable : (prefixWord ++ tailWord_3818111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818111).length < 2 ^ (prefixWord ++ tailWord_3818111).sum := by decide
  have hdescent : baseEnd_3818111 < baseStart_3818111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818141 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_3818141 : Nat := 118140960795 + 3818141 * 2 ^ 59
def prefixEnd_3818141 : Nat := 4983230072969 + 3 ^ 40 * 3818141 * 2
def baseEnd_3818141 : Nat := 1960541539638451239478195

theorem tailTrace_3818141 : CollatzResearch.WordTrace tailWord_3818141 prefixEnd_3818141 1960541539638451239478195 := by
  unfold tailWord_3818141
  simp only [CollatzResearch.WordTrace]
  refine ⟨139259042860534718412646277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92839361907023145608430851 139259042860534718412646277)
  ·
    refine ⟨26111070536350259702371177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139259042860534718412646277 26111070536350259702371177)
    ·
      refine ⟨19583302902262694776778383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26111070536350259702371177 19583302902262694776778383)
      ·
        refine ⟨29374954353394042165167575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19583302902262694776778383 29374954353394042165167575)
        ·
          refine ⟨44062431530091063247751363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29374954353394042165167575 44062431530091063247751363)
          ·
            refine ⟨66093647295136594871627045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44062431530091063247751363 66093647295136594871627045)
            ·
              refine ⟨12392558867838111538430071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66093647295136594871627045 12392558867838111538430071)
              ·
                refine ⟨18588838301757167307645107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12392558867838111538430071 18588838301757167307645107)
                ·
                  refine ⟨27883257452635750961467661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18588838301757167307645107 27883257452635750961467661)
                  ·
                    refine ⟨10456221544738406610550373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27883257452635750961467661 10456221544738406610550373)
                    ·
                      refine ⟨1960541539638451239478195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10456221544738406610550373 1960541539638451239478195)
                      ·
                        rfl

theorem cell23_3818141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_3818141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818141 prefixEnd_3818141 := by exact prefixLift 3818141
  have htrace : WordTrace (prefixWord ++ tailWord_3818141) baseStart_3818141 baseEnd_3818141 := by
    simpa [prefixWord, tailWord_3818141, baseEnd_3818141] using wordTrace_append hprefix tailTrace_3818141
  have hstable : (prefixWord ++ tailWord_3818141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818141).length < 2 ^ (prefixWord ++ tailWord_3818141).sum := by decide
  have hdescent : baseEnd_3818141 < baseStart_3818141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818218 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 3, 5, 2]
def baseStart_3818218 : Nat := 118140960795 + 3818218 * 2 ^ 59
def prefixEnd_3818218 : Nat := 4983230072969 + 3 ^ 40 * 3818218 * 2
def baseEnd_3818218 : Nat := 1960581077648847438215341

theorem tailTrace_3818218 : CollatzResearch.WordTrace tailWord_3818218 prefixEnd_3818218 1960581077648847438215341 := by
  unfold tailWord_3818218
  simp only [CollatzResearch.WordTrace]
  refine ⟨34815462820313940140799827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92841234187503840375466205 34815462820313940140799827)
  ·
    refine ⟨52223194230470910211199741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34815462820313940140799827 52223194230470910211199741)
    ·
      refine ⟨19583697836426591329199903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52223194230470910211199741 19583697836426591329199903)
      ·
        refine ⟨29375546754639886993799855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19583697836426591329199903 29375546754639886993799855)
        ·
          refine ⟨44063320131959830490699783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29375546754639886993799855 44063320131959830490699783)
          ·
            refine ⟨66094980197939745736049675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44063320131959830490699783 66094980197939745736049675)
            ·
              refine ⟨99142470296909618604074513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66094980197939745736049675 99142470296909618604074513)
              ·
                refine ⟨74356852722682213953055885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99142470296909618604074513 74356852722682213953055885)
                ·
                  refine ⟨27883819771005830232395957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74356852722682213953055885 27883819771005830232395957)
                  ·
                    refine ⟨2614108103531796584287121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27883819771005830232395957 2614108103531796584287121)
                    ·
                      refine ⟨1960581077648847438215341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2614108103531796584287121 1960581077648847438215341)
                      ·
                        rfl

theorem cell23_3818218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_3818218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818218 prefixEnd_3818218 := by exact prefixLift 3818218
  have htrace : WordTrace (prefixWord ++ tailWord_3818218) baseStart_3818218 baseEnd_3818218 := by
    simpa [prefixWord, tailWord_3818218, baseEnd_3818218] using wordTrace_append hprefix tailTrace_3818218
  have hstable : (prefixWord ++ tailWord_3818218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818218).length < 2 ^ (prefixWord ++ tailWord_3818218).sum := by decide
  have hdescent : baseEnd_3818218 < baseStart_3818218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818242 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_3818242 : Nat := 118140960795 + 3818242 * 2 ^ 59
def prefixEnd_3818242 : Nat := 4983230072969 + 3 ^ 40 * 3818242 * 2
def baseEnd_3818242 : Nat := 1960593401184555344315231

theorem tailTrace_3818242 : CollatzResearch.WordTrace tailWord_3818242 prefixEnd_3818242 1960593401184555344315231 := by
  unfold tailWord_3818242
  simp only [CollatzResearch.WordTrace]
  refine ⟨34815681658292203165518245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92841817755445875108048653 34815681658292203165518245)
  ·
    refine ⟨6527940310929788093534671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34815681658292203165518245 6527940310929788093534671)
    ·
      refine ⟨9791910466394682140302007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6527940310929788093534671 9791910466394682140302007)
      ·
        refine ⟨14687865699592023210453011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9791910466394682140302007 14687865699592023210453011)
        ·
          refine ⟨22031798549388034815679517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14687865699592023210453011 22031798549388034815679517)
          ·
            refine ⟨8261924456020513055879819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22031798549388034815679517 8261924456020513055879819)
            ·
              refine ⟨12392886684030769583819729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8261924456020513055879819 12392886684030769583819729)
              ·
                refine ⟨9294665013023077187864797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12392886684030769583819729 9294665013023077187864797)
                ·
                  refine ⟨3485499379883653945449299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9294665013023077187864797 3485499379883653945449299)
                  ·
                    refine ⟨5228249069825480918173949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3485499379883653945449299 5228249069825480918173949)
                    ·
                      refine ⟨1960593401184555344315231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5228249069825480918173949 1960593401184555344315231)
                      ·
                        rfl

theorem cell23_3818242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_3818242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818242 prefixEnd_3818242 := by exact prefixLift 3818242
  have htrace : WordTrace (prefixWord ++ tailWord_3818242) baseStart_3818242 baseEnd_3818242 := by
    simpa [prefixWord, tailWord_3818242, baseEnd_3818242] using wordTrace_append hprefix tailTrace_3818242
  have hstable : (prefixWord ++ tailWord_3818242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818242).length < 2 ^ (prefixWord ++ tailWord_3818242).sum := by decide
  have hdescent : baseEnd_3818242 < baseStart_3818242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818248 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_3818248 : Nat := 118140960795 + 3818248 * 2 ^ 59
def prefixEnd_3818248 : Nat := 4983230072969 + 3 ^ 40 * 3818248 * 2
def baseEnd_3818248 : Nat := 1960596482068482320840203

theorem tailTrace_3818248 : CollatzResearch.WordTrace tailWord_3818248 prefixEnd_3818248 1960596482068482320840203 := by
  unfold tailWord_3818248
  simp only [CollatzResearch.WordTrace]
  refine ⟨69631472735573537843395699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92841963647431383791194265 69631472735573537843395699)
  ·
    refine ⟨104447209103360306765093549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69631472735573537843395699 104447209103360306765093549)
    ·
      refine ⟨39167703413760115036910081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104447209103360306765093549 39167703413760115036910081)
      ·
        refine ⟨29375777560320086277682561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39167703413760115036910081 29375777560320086277682561)
        ·
          refine ⟨22031833170240064708261921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29375777560320086277682561 22031833170240064708261921)
          ·
            refine ⟨16523874877680048531196441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22031833170240064708261921 16523874877680048531196441)
            ·
              refine ⟨12392906158260036398397331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16523874877680048531196441 12392906158260036398397331)
              ·
                refine ⟨18589359237390054597595997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12392906158260036398397331 18589359237390054597595997)
                ·
                  refine ⟨6971009714021270474098499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18589359237390054597595997 6971009714021270474098499)
                  ·
                    refine ⟨10456514571031905711147749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6971009714021270474098499 10456514571031905711147749)
                    ·
                      refine ⟨1960596482068482320840203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10456514571031905711147749 1960596482068482320840203)
                      ·
                        rfl

theorem cell23_3818248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_3818248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818248 prefixEnd_3818248 := by exact prefixLift 3818248
  have htrace : WordTrace (prefixWord ++ tailWord_3818248) baseStart_3818248 baseEnd_3818248 := by
    simpa [prefixWord, tailWord_3818248, baseEnd_3818248] using wordTrace_append hprefix tailTrace_3818248
  have hstable : (prefixWord ++ tailWord_3818248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818248).length < 2 ^ (prefixWord ++ tailWord_3818248).sum := by decide
  have hdescent : baseEnd_3818248 < baseStart_3818248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818271 : List Nat := [1, 1, 2, 4, 2, 3, 10]
def baseStart_3818271 : Nat := 118140960795 + 3818271 * 2 ^ 59
def prefixEnd_3818271 : Nat := 4983230072969 + 3 ^ 40 * 3818271 * 2
def baseEnd_3818271 : Nat := 24205040643500441121637

theorem tailTrace_3818271 : CollatzResearch.WordTrace tailWord_3818271 prefixEnd_3818271 24205040643500441121637 := by
  unfold tailWord_3818271
  simp only [CollatzResearch.WordTrace]
  refine ⟨139263784350063750614878667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92842522900042500409919111 139263784350063750614878667)
  ·
    refine ⟨208895676525095625922318001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139263784350063750614878667 208895676525095625922318001)
    ·
      refine ⟨156671757393821719441738501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208895676525095625922318001 156671757393821719441738501)
      ·
        refine ⟨29375954511341572395325969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156671757393821719441738501 29375954511341572395325969)
        ·
          refine ⟨22031965883506179296494477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29375954511341572395325969 22031965883506179296494477)
          ·
            refine ⟨8261987206314817236185429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22031965883506179296494477 8261987206314817236185429)
            ·
              refine ⟨24205040643500441121637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8261987206314817236185429 24205040643500441121637)
              ·
                rfl

theorem cell23_3818271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 10].length) (baseStart_3818271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818271 prefixEnd_3818271 := by exact prefixLift 3818271
  have htrace : WordTrace (prefixWord ++ tailWord_3818271) baseStart_3818271 baseEnd_3818271 := by
    simpa [prefixWord, tailWord_3818271, baseEnd_3818271] using wordTrace_append hprefix tailTrace_3818271
  have hstable : (prefixWord ++ tailWord_3818271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818271).length < 2 ^ (prefixWord ++ tailWord_3818271).sum := by decide
  have hdescent : baseEnd_3818271 < baseStart_3818271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818292 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_3818292 : Nat := 118140960795 + 3818292 * 2 ^ 59
def prefixEnd_3818292 : Nat := 4983230072969 + 3 ^ 40 * 3818292 * 2
def baseEnd_3818292 : Nat := 653539691739093382896667

theorem tailTrace_3818292 : CollatzResearch.WordTrace tailWord_3818292 prefixEnd_3818292 653539691739093382896667 := by
  unfold tailWord_3818292
  simp only [CollatzResearch.WordTrace]
  refine ⟨69632275141493835600696565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92843033521991780800928753 69632275141493835600696565)
  ·
    refine ⟨6528025794515047087565303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69632275141493835600696565 6528025794515047087565303)
    ·
      refine ⟨9792038691772570631347955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6528025794515047087565303 9792038691772570631347955)
      ·
        refine ⟨14688058037658855947021933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9792038691772570631347955 14688058037658855947021933)
        ·
          refine ⟨5508021764122070980133225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14688058037658855947021933 5508021764122070980133225)
          ·
            refine ⟨4131016323091553235099919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5508021764122070980133225 4131016323091553235099919)
            ·
              refine ⟨6196524484637329852649879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4131016323091553235099919 6196524484637329852649879)
              ·
                refine ⟨9294786726955994778974819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6196524484637329852649879 9294786726955994778974819)
                ·
                  refine ⟨13942180090433992168462229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9294786726955994778974819 13942180090433992168462229)
                  ·
                    refine ⟨653539691739093382896667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13942180090433992168462229 653539691739093382896667)
                    ·
                      rfl

theorem cell23_3818292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_3818292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818292 prefixEnd_3818292 := by exact prefixLift 3818292
  have htrace : WordTrace (prefixWord ++ tailWord_3818292) baseStart_3818292 baseEnd_3818292 := by
    simpa [prefixWord, tailWord_3818292, baseEnd_3818292] using wordTrace_append hprefix tailTrace_3818292
  have hstable : (prefixWord ++ tailWord_3818292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818292).length < 2 ^ (prefixWord ++ tailWord_3818292).sum := by decide
  have hdescent : baseEnd_3818292 < baseStart_3818292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818305 : List Nat := [1, 2, 5, 3, 1, 1, 1, 9]
def baseStart_3818305 : Nat := 118140960795 + 3818305 * 2 ^ 59
def prefixEnd_3818305 : Nat := 4983230072969 + 3 ^ 40 * 3818305 * 2
def baseEnd_3818305 : Nat := 72615768535769948067683

theorem tailTrace_3818305 : CollatzResearch.WordTrace tailWord_3818305 prefixEnd_3818305 72615768535769948067683 := by
  unfold tailWord_3818305
  simp only [CollatzResearch.WordTrace]
  refine ⟨139265024431940574421616369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92843349621293716281077579 139265024431940574421616369)
  ·
    refine ⟨104448768323955430816212277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139265024431940574421616369 104448768323955430816212277)
    ·
      refine ⟨9792072030370821639019901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104448768323955430816212277 9792072030370821639019901)
      ·
        refine ⟨3672027011389058114632463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9792072030370821639019901 3672027011389058114632463)
        ·
          refine ⟨5508040517083587171948695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3672027011389058114632463 5508040517083587171948695)
          ·
            refine ⟨8262060775625380757923043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5508040517083587171948695 8262060775625380757923043)
            ·
              refine ⟨12393091163438071136884565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8262060775625380757923043 12393091163438071136884565)
              ·
                refine ⟨72615768535769948067683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12393091163438071136884565 72615768535769948067683)
                ·
                  rfl

theorem cell23_3818305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 9].length) (baseStart_3818305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818305 prefixEnd_3818305 := by exact prefixLift 3818305
  have htrace : WordTrace (prefixWord ++ tailWord_3818305) baseStart_3818305 baseEnd_3818305 := by
    simpa [prefixWord, tailWord_3818305, baseEnd_3818305] using wordTrace_append hprefix tailTrace_3818305
  have hstable : (prefixWord ++ tailWord_3818305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818305).length < 2 ^ (prefixWord ++ tailWord_3818305).sum := by decide
  have hdescent : baseEnd_3818305 < baseStart_3818305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818310 : List Nat := [6, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_3818310 : Nat := 118140960795 + 3818310 * 2 ^ 59
def prefixEnd_3818310 : Nat := 4983230072969 + 3 ^ 40 * 3818310 * 2
def baseEnd_3818310 : Nat := 1960628317869061078264919

theorem tailTrace_3818310 : CollatzResearch.WordTrace tailWord_3818310 prefixEnd_3818310 1960628317869061078264919 := by
  unfold tailWord_3818310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4352037712403826883610887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92843471197948306850365589 4352037712403826883610887)
  ·
    refine ⟨6528056568605740325416331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4352037712403826883610887 6528056568605740325416331)
    ·
      refine ⟨9792084852908610488124497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6528056568605740325416331 9792084852908610488124497)
      ·
        refine ⟨7344063639681457866093373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9792084852908610488124497 7344063639681457866093373)
        ·
          refine ⟨2754023864880546699785015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7344063639681457866093373 2754023864880546699785015)
          ·
            refine ⟨4131035797320820049677523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2754023864880546699785015 4131035797320820049677523)
            ·
              refine ⟨6196553695981230074516285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4131035797320820049677523 6196553695981230074516285)
              ·
                refine ⟨2323707635992961277943607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6196553695981230074516285 2323707635992961277943607)
                ·
                  refine ⟨3485561453989441916915411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2323707635992961277943607 3485561453989441916915411)
                  ·
                    refine ⟨5228342180984162875373117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3485561453989441916915411 5228342180984162875373117)
                    ·
                      refine ⟨1960628317869061078264919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5228342180984162875373117 1960628317869061078264919)
                      ·
                        rfl

theorem cell23_3818310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_3818310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818310 prefixEnd_3818310 := by exact prefixLift 3818310
  have htrace : WordTrace (prefixWord ++ tailWord_3818310) baseStart_3818310 baseEnd_3818310 := by
    simpa [prefixWord, tailWord_3818310, baseEnd_3818310] using wordTrace_append hprefix tailTrace_3818310
  have hstable : (prefixWord ++ tailWord_3818310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818310).length < 2 ^ (prefixWord ++ tailWord_3818310).sum := by decide
  have hdescent : baseEnd_3818310 < baseStart_3818310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818316 : List Nat := [2, 2, 1, 3, 3, 3, 1, 3, 1, 2, 2]
def baseStart_3818316 : Nat := 118140960795 + 3818316 * 2 ^ 59
def prefixEnd_3818316 : Nat := 4983230072969 + 3 ^ 40 * 3818316 * 2
def baseEnd_3818316 : Nat := 1960631398752988054789891

theorem tailTrace_3818316 : CollatzResearch.WordTrace tailWord_3818316 prefixEnd_3818316 1960631398752988054789891 := by
  unfold tailWord_3818316
  simp only [CollatzResearch.WordTrace]
  refine ⟨69632712817450361650133401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92843617089933815533511201 69632712817450361650133401)
  ·
    refine ⟨52224534613087771237600051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69632712817450361650133401 52224534613087771237600051)
    ·
      refine ⟨78336801919631656856400077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52224534613087771237600051 78336801919631656856400077)
      ·
        refine ⟨29376300719861871321150029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78336801919631656856400077 29376300719861871321150029)
        ·
          refine ⟨11016112769948201745431261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29376300719861871321150029 11016112769948201745431261)
          ·
            refine ⟨4131042288730575654536723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11016112769948201745431261 4131042288730575654536723)
            ·
              refine ⟨6196563433095863481805085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4131042288730575654536723 6196563433095863481805085)
              ·
                refine ⟨2323711287410948805676907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6196563433095863481805085 2323711287410948805676907)
                ·
                  refine ⟨3485566931116423208515361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2323711287410948805676907 3485566931116423208515361)
                  ·
                    refine ⟨2614175198337317406386521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3485566931116423208515361 2614175198337317406386521)
                    ·
                      refine ⟨1960631398752988054789891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2614175198337317406386521 1960631398752988054789891)
                      ·
                        rfl

theorem cell23_3818316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_3818316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818316 prefixEnd_3818316 := by exact prefixLift 3818316
  have htrace : WordTrace (prefixWord ++ tailWord_3818316) baseStart_3818316 baseEnd_3818316 := by
    simpa [prefixWord, tailWord_3818316, baseEnd_3818316] using wordTrace_append hprefix tailTrace_3818316
  have hstable : (prefixWord ++ tailWord_3818316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818316).length < 2 ^ (prefixWord ++ tailWord_3818316).sum := by decide
  have hdescent : baseEnd_3818316 < baseStart_3818316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818332 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_3818332 : Nat := 118140960795 + 3818332 * 2 ^ 59
def prefixEnd_3818332 : Nat := 4983230072969 + 3 ^ 40 * 3818332 * 2
def baseEnd_3818332 : Nat := 1960639614443459992189817

theorem tailTrace_3818332 : CollatzResearch.WordTrace tailWord_3818332 prefixEnd_3818332 1960639614443459992189817 := by
  unfold tailWord_3818332
  simp only [CollatzResearch.WordTrace]
  refine ⟨69633004601421379016424625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92844006135228505355232833 69633004601421379016424625)
  ·
    refine ⟨52224753451066034262318469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69633004601421379016424625 52224753451066034262318469)
    ·
      refine ⟨9792141272074881424184713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52224753451066034262318469 9792141272074881424184713)
      ·
        refine ⟨7344105954056161068138535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9792141272074881424184713 7344105954056161068138535)
        ·
          refine ⟨11016158931084241602207803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7344105954056161068138535 11016158931084241602207803)
          ·
            refine ⟨16524238396626362403311705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11016158931084241602207803 16524238396626362403311705)
            ·
              refine ⟨12393178797469771802483779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16524238396626362403311705 12393178797469771802483779)
              ·
                refine ⟨18589768196204657703725669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12393178797469771802483779 18589768196204657703725669)
                ·
                  refine ⟨3485581536788373319448563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18589768196204657703725669 3485581536788373319448563)
                  ·
                    refine ⟨5228372305182559979172845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3485581536788373319448563 5228372305182559979172845)
                    ·
                      refine ⟨1960639614443459992189817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5228372305182559979172845 1960639614443459992189817)
                      ·
                        rfl

theorem cell23_3818332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_3818332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818332 prefixEnd_3818332 := by exact prefixLift 3818332
  have htrace : WordTrace (prefixWord ++ tailWord_3818332) baseStart_3818332 baseEnd_3818332 := by
    simpa [prefixWord, tailWord_3818332, baseEnd_3818332] using wordTrace_append hprefix tailTrace_3818332
  have hstable : (prefixWord ++ tailWord_3818332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818332).length < 2 ^ (prefixWord ++ tailWord_3818332).sum := by decide
  have hdescent : baseEnd_3818332 < baseStart_3818332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818351 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 6]
def baseStart_3818351 : Nat := 118140960795 + 3818351 * 2 ^ 59
def prefixEnd_3818351 : Nat := 4983230072969 + 3 ^ 40 * 3818351 * 2
def baseEnd_3818351 : Nat := 1960649370575895417852229

theorem tailTrace_3818351 : CollatzResearch.WordTrace tailWord_3818351 prefixEnd_3818351 1960649370575895417852229 := by
  unfold tailWord_3818351
  simp only [CollatzResearch.WordTrace]
  refine ⟨139266702189773924277790907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92844468126515949518527271 139266702189773924277790907)
  ·
    refine ⟨208900053284660886416686361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139266702189773924277790907 208900053284660886416686361)
    ·
      refine ⟨156675039963495664812514771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208900053284660886416686361 156675039963495664812514771)
      ·
        refine ⟨235012559945243497218772157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156675039963495664812514771 235012559945243497218772157)
        ·
          refine ⟨88129709979466311457039559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235012559945243497218772157 88129709979466311457039559)
          ·
            refine ⟨132194564969199467185559339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88129709979466311457039559 132194564969199467185559339)
            ·
              refine ⟨198291847453799200778339009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132194564969199467185559339 198291847453799200778339009)
              ·
                refine ⟨148718885590349400583754257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198291847453799200778339009 148718885590349400583754257)
                ·
                  refine ⟨111539164192762050437815693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148718885590349400583754257 111539164192762050437815693)
                  ·
                    refine ⟨41827186572285768914180885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111539164192762050437815693 41827186572285768914180885)
                    ·
                      refine ⟨1960649370575895417852229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41827186572285768914180885 1960649370575895417852229)
                      ·
                        rfl

theorem cell23_3818351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_3818351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818351 prefixEnd_3818351 := by exact prefixLift 3818351
  have htrace : WordTrace (prefixWord ++ tailWord_3818351) baseStart_3818351 baseEnd_3818351 := by
    simpa [prefixWord, tailWord_3818351, baseEnd_3818351] using wordTrace_append hprefix tailTrace_3818351
  have hstable : (prefixWord ++ tailWord_3818351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818351).length < 2 ^ (prefixWord ++ tailWord_3818351).sum := by decide
  have hdescent : baseEnd_3818351 < baseStart_3818351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818389 : List Nat := [1, 3, 2, 1, 1, 5, 2, 2, 2, 2, 2]
def baseStart_3818389 : Nat := 118140960795 + 3818389 * 2 ^ 59
def prefixEnd_3818389 : Nat := 4983230072969 + 3 ^ 40 * 3818389 * 2
def baseEnd_3818389 : Nat := 1960668882840766269177055

theorem tailTrace_3818389 : CollatzResearch.WordTrace tailWord_3818389 prefixEnd_3818389 1960668882840766269177055 := by
  unfold tailWord_3818389
  simp only [CollatzResearch.WordTrace]
  refine ⟨139268088163636256767674221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92845392109090837845116147 139268088163636256767674221)
  ·
    refine ⟨52225533061363596287877833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139268088163636256767674221 52225533061363596287877833)
    ·
      refine ⟨39169149796022697215908375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52225533061363596287877833 39169149796022697215908375)
      ·
        refine ⟨58753724694034045823862563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39169149796022697215908375 58753724694034045823862563)
        ·
          refine ⟨88130587041051068735793845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58753724694034045823862563 88130587041051068735793845)
          ·
            refine ⟨8262242535098537693980673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88130587041051068735793845 8262242535098537693980673)
            ·
              refine ⟨6196681901323903270485505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8262242535098537693980673 6196681901323903270485505)
              ·
                refine ⟨4647511425992927452864129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6196681901323903270485505 4647511425992927452864129)
                ·
                  refine ⟨3485633569494695589648097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4647511425992927452864129 3485633569494695589648097)
                  ·
                    refine ⟨2614225177121021692236073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3485633569494695589648097 2614225177121021692236073)
                    ·
                      refine ⟨1960668882840766269177055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2614225177121021692236073 1960668882840766269177055)
                      ·
                        rfl

theorem cell23_3818389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_3818389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818389 prefixEnd_3818389 := by exact prefixLift 3818389
  have htrace : WordTrace (prefixWord ++ tailWord_3818389) baseStart_3818389 baseEnd_3818389 := by
    simpa [prefixWord, tailWord_3818389, baseEnd_3818389] using wordTrace_append hprefix tailTrace_3818389
  have hstable : (prefixWord ++ tailWord_3818389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818389).length < 2 ^ (prefixWord ++ tailWord_3818389).sum := by decide
  have hdescent : baseEnd_3818389 < baseStart_3818389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818425 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 2, 5]
def baseStart_3818425 : Nat := 118140960795 + 3818425 * 2 ^ 59
def prefixEnd_3818425 : Nat := 4983230072969 + 3 ^ 40 * 3818425 * 2
def baseEnd_3818425 : Nat := 653562456048109376108963

theorem tailTrace_3818425 : CollatzResearch.WordTrace tailWord_3818425 prefixEnd_3818425 653562456048109376108963 := by
  unfold tailWord_3818425
  simp only [CollatzResearch.WordTrace]
  refine ⟨139269401191505834915984729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92846267461003889943989819 139269401191505834915984729)
  ·
    refine ⟨104452050893629376186988547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139269401191505834915984729 104452050893629376186988547)
    ·
      refine ⟨156678076340444064280482821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104452050893629376186988547 156678076340444064280482821)
      ·
        refine ⟨29377139313833262052590529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156678076340444064280482821 29377139313833262052590529)
        ·
          refine ⟨22032854485374946539442897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29377139313833262052590529 22032854485374946539442897)
          ·
            refine ⟨16524640864031209904582173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22032854485374946539442897 16524640864031209904582173)
            ·
              refine ⟨6196740324011703714218315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16524640864031209904582173 6196740324011703714218315)
              ·
                refine ⟨9295110486017555571327473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6196740324011703714218315 9295110486017555571327473)
                ·
                  refine ⟨6971332864513166678495605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9295110486017555571327473 6971332864513166678495605)
                  ·
                    refine ⟨653562456048109376108963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6971332864513166678495605 653562456048109376108963)
                    ·
                      rfl

theorem cell23_3818425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 5].length) (baseStart_3818425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818425 prefixEnd_3818425 := by exact prefixLift 3818425
  have htrace : WordTrace (prefixWord ++ tailWord_3818425) baseStart_3818425 baseEnd_3818425 := by
    simpa [prefixWord, tailWord_3818425, baseEnd_3818425] using wordTrace_append hprefix tailTrace_3818425
  have hstable : (prefixWord ++ tailWord_3818425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818425).length < 2 ^ (prefixWord ++ tailWord_3818425).sum := by decide
  have hdescent : baseEnd_3818425 < baseStart_3818425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818506 : List Nat := [3, 1, 2, 2, 3, 2, 3, 2, 1, 4]
def baseStart_3818506 : Nat := 118140960795 + 3818506 * 2 ^ 59
def prefixEnd_3818506 : Nat := 4983230072969 + 3 ^ 40 * 3818506 * 2
def baseEnd_3818506 : Nat := 653576320025780770471339

theorem tailTrace_3818506 : CollatzResearch.WordTrace tailWord_3818506 prefixEnd_3818506 653576320025780770471339 := by
  unfold tailWord_3818506
  simp only [CollatzResearch.WordTrace]
  refine ⟨34818088876053096437420843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92848237002808257166455581 34818088876053096437420843)
  ·
    refine ⟨52227133314079644656131265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34818088876053096437420843 52227133314079644656131265)
    ·
      refine ⟨39170349985559733492098449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52227133314079644656131265 39170349985559733492098449)
      ·
        refine ⟨29377762489169800119073837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39170349985559733492098449 29377762489169800119073837)
        ·
          refine ⟨11016660933438675044652689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29377762489169800119073837 11016660933438675044652689)
          ·
            refine ⟨8262495700079006283489517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11016660933438675044652689 8262495700079006283489517)
            ·
              refine ⟨3098435887529627356308569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8262495700079006283489517 3098435887529627356308569)
              ·
                refine ⟨2323826915647220517231427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3098435887529627356308569 2323826915647220517231427)
                ·
                  refine ⟨3485740373470830775847141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2323826915647220517231427 3485740373470830775847141)
                  ·
                    refine ⟨653576320025780770471339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3485740373470830775847141 653576320025780770471339)
                    ·
                      rfl

theorem cell23_3818506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_3818506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818506 prefixEnd_3818506 := by exact prefixLift 3818506
  have htrace : WordTrace (prefixWord ++ tailWord_3818506) baseStart_3818506 baseEnd_3818506 := by
    simpa [prefixWord, tailWord_3818506, baseEnd_3818506] using wordTrace_append hprefix tailTrace_3818506
  have hstable : (prefixWord ++ tailWord_3818506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818506).length < 2 ^ (prefixWord ++ tailWord_3818506).sum := by decide
  have hdescent : baseEnd_3818506 < baseStart_3818506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818519 : List Nat := [1, 1, 3, 5, 1, 3, 2, 1, 6]
def baseStart_3818519 : Nat := 118140960795 + 3818519 * 2 ^ 59
def prefixEnd_3818519 : Nat := 4983230072969 + 3 ^ 40 * 3818519 * 2
def baseEnd_3818519 : Nat := 217859515036205640061273

theorem tailTrace_3818519 : CollatzResearch.WordTrace tailWord_3818519 prefixEnd_3818519 217859515036205640061273 := by
  unfold tailWord_3818519
  simp only [CollatzResearch.WordTrace]
  refine ⟨139272829653165288969906611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92848553102110192646604407 139272829653165288969906611)
  ·
    refine ⟨208909244479747933454859917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139272829653165288969906611 208909244479747933454859917)
    ·
      refine ⟨78340966679905475045572469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208909244479747933454859917 78340966679905475045572469)
      ·
        refine ⟨7344465626241138285522419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78340966679905475045572469 7344465626241138285522419)
        ·
          refine ⟨11016698439361707428283629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7344465626241138285522419 11016698439361707428283629)
          ·
            refine ⟨4131261914760640285606361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11016698439361707428283629 4131261914760640285606361)
            ·
              refine ⟨3098446436070480214204771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4131261914760640285606361 3098446436070480214204771)
              ·
                refine ⟨4647669654105720321307157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098446436070480214204771 4647669654105720321307157)
                ·
                  refine ⟨217859515036205640061273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4647669654105720321307157 217859515036205640061273)
                  ·
                    rfl

theorem cell23_3818519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 6].length) (baseStart_3818519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818519 prefixEnd_3818519 := by exact prefixLift 3818519
  have htrace : WordTrace (prefixWord ++ tailWord_3818519) baseStart_3818519 baseEnd_3818519 := by
    simpa [prefixWord, tailWord_3818519, baseEnd_3818519] using wordTrace_append hprefix tailTrace_3818519
  have hstable : (prefixWord ++ tailWord_3818519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818519).length < 2 ^ (prefixWord ++ tailWord_3818519).sum := by decide
  have hdescent : baseEnd_3818519 < baseStart_3818519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818522 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2]
def baseStart_3818522 : Nat := 118140960795 + 3818522 * 2 ^ 59
def prefixEnd_3818522 : Nat := 4983230072969 + 3 ^ 40 * 3818522 * 2
def baseEnd_3818522 : Nat := 1960737175767814248813943

theorem tailTrace_3818522 : CollatzResearch.WordTrace tailWord_3818522 prefixEnd_3818522 1960737175767814248813943 := by
  unfold tailWord_3818522
  simp only [CollatzResearch.WordTrace]
  refine ⟨34818234768038605120566455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92848626048102946988177213 34818234768038605120566455)
  ·
    refine ⟨52227352152057907680849683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34818234768038605120566455 52227352152057907680849683)
    ·
      refine ⟨78341028228086861521274525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52227352152057907680849683 78341028228086861521274525)
      ·
        refine ⟨29377885585532573070477947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78341028228086861521274525 29377885585532573070477947)
        ·
          refine ⟨44066828378298859605716921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29377885585532573070477947 44066828378298859605716921)
          ·
            refine ⟨33050121283724144704287691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44066828378298859605716921 33050121283724144704287691)
            ·
              refine ⟨49575181925586217056431537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33050121283724144704287691 49575181925586217056431537)
              ·
                refine ⟨37181386444189662792323653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49575181925586217056431537 37181386444189662792323653)
                ·
                  refine ⟨6971509958285561773560685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37181386444189662792323653 6971509958285561773560685)
                  ·
                    refine ⟨2614316234357085665085257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6971509958285561773560685 2614316234357085665085257)
                    ·
                      refine ⟨1960737175767814248813943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2614316234357085665085257 1960737175767814248813943)
                      ·
                        rfl

theorem cell23_3818522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_3818522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818522 prefixEnd_3818522 := by exact prefixLift 3818522
  have htrace : WordTrace (prefixWord ++ tailWord_3818522) baseStart_3818522 baseEnd_3818522 := by
    simpa [prefixWord, tailWord_3818522, baseEnd_3818522] using wordTrace_append hprefix tailTrace_3818522
  have hstable : (prefixWord ++ tailWord_3818522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818522).length < 2 ^ (prefixWord ++ tailWord_3818522).sum := by decide
  have hdescent : baseEnd_3818522 < baseStart_3818522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818532 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 3, 5]
def baseStart_3818532 : Nat := 118140960795 + 3818532 * 2 ^ 59
def prefixEnd_3818532 : Nat := 4983230072969 + 3 ^ 40 * 3818532 * 2
def baseEnd_3818532 : Nat := 653580770191453069896299

theorem tailTrace_3818532 : CollatzResearch.WordTrace tailWord_3818532 prefixEnd_3818532 653580770191453069896299 := by
  unfold tailWord_3818532
  simp only [CollatzResearch.WordTrace]
  refine ⟨69636651901059096095064925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92848869201412128126753233 69636651901059096095064925)
  ·
    refine ⟨26113744462897161035649347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69636651901059096095064925 26113744462897161035649347)
    ·
      refine ⟨39170616694345741553474021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26113744462897161035649347 39170616694345741553474021)
      ·
        refine ⟨7344490630189826541276379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39170616694345741553474021 7344490630189826541276379)
        ·
          refine ⟨11016735945284739811914569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7344490630189826541276379 11016735945284739811914569)
          ·
            refine ⟨8262551958963554858935927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11016735945284739811914569 8262551958963554858935927)
            ·
              refine ⟨12393827938445332288403891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8262551958963554858935927 12393827938445332288403891)
              ·
                refine ⟨18590741907667998432605837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12393827938445332288403891 18590741907667998432605837)
                ·
                  refine ⟨6971528215375499412227189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18590741907667998432605837 6971528215375499412227189)
                  ·
                    refine ⟨653580770191453069896299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6971528215375499412227189 653580770191453069896299)
                    ·
                      rfl

theorem cell23_3818532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_3818532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818532 prefixEnd_3818532 := by exact prefixLift 3818532
  have htrace : WordTrace (prefixWord ++ tailWord_3818532) baseStart_3818532 baseEnd_3818532 := by
    simpa [prefixWord, tailWord_3818532, baseEnd_3818532] using wordTrace_append hprefix tailTrace_3818532
  have hstable : (prefixWord ++ tailWord_3818532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818532).length < 2 ^ (prefixWord ++ tailWord_3818532).sum := by decide
  have hdescent : baseEnd_3818532 < baseStart_3818532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818545 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 1, 6]
def baseStart_3818545 : Nat := 118140960795 + 3818545 * 2 ^ 59
def prefixEnd_3818545 : Nat := 4983230072969 + 3 ^ 40 * 3818545 * 2
def baseEnd_3818545 : Nat := 653582995274289219608779

theorem tailTrace_3818545 : CollatzResearch.WordTrace tailWord_3818545 prefixEnd_3818545 653582995274289219608779 := by
  unfold tailWord_3818545
  simp only [CollatzResearch.WordTrace]
  refine ⟨139273777951071095410353089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92849185300714063606902059 139273777951071095410353089)
  ·
    refine ⟨104455333463303321557764817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139273777951071095410353089 104455333463303321557764817)
    ·
      refine ⟨78341500097477491168323613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104455333463303321557764817 78341500097477491168323613)
      ·
        refine ⟨29378062536554059188121355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78341500097477491168323613 29378062536554059188121355)
        ·
          refine ⟨44067093804831088782182033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29378062536554059188121355 44067093804831088782182033)
          ·
            refine ⟨33050320353623316586636525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44067093804831088782182033 33050320353623316586636525)
            ·
              refine ⟨12393870132608743719988697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33050320353623316586636525 12393870132608743719988697)
              ·
                refine ⟨9295402599456557789991523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12393870132608743719988697 9295402599456557789991523)
                ·
                  refine ⟨13943103899184836684987285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9295402599456557789991523 13943103899184836684987285)
                  ·
                    refine ⟨653582995274289219608779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13943103899184836684987285 653582995274289219608779)
                    ·
                      rfl

theorem cell23_3818545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_3818545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818545 prefixEnd_3818545 := by exact prefixLift 3818545
  have htrace : WordTrace (prefixWord ++ tailWord_3818545) baseStart_3818545 baseEnd_3818545 := by
    simpa [prefixWord, tailWord_3818545, baseEnd_3818545] using wordTrace_append hprefix tailTrace_3818545
  have hstable : (prefixWord ++ tailWord_3818545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818545).length < 2 ^ (prefixWord ++ tailWord_3818545).sum := by decide
  have hdescent : baseEnd_3818545 < baseStart_3818545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818555 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 3]
def baseStart_3818555 : Nat := 118140960795 + 3818555 * 2 ^ 59
def prefixEnd_3818555 : Nat := 4983230072969 + 3 ^ 40 * 3818555 * 2
def baseEnd_3818555 : Nat := 1960754120629412619701291

theorem tailTrace_3818555 : CollatzResearch.WordTrace tailWord_3818555 prefixEnd_3818555 1960754120629412619701291 := by
  unfold tailWord_3818555
  simp only [CollatzResearch.WordTrace]
  refine ⟨139274142681034867118217119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92849428454023244745478079 139274142681034867118217119)
  ·
    refine ⟨208911214021552300677325679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139274142681034867118217119 208911214021552300677325679)
    ·
      refine ⟨313366821032328451015988519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208911214021552300677325679 313366821032328451015988519)
      ·
        refine ⟨470050231548492676523982779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313366821032328451015988519 470050231548492676523982779)
        ·
          refine ⟨705075347322739014785974169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470050231548492676523982779 705075347322739014785974169)
          ·
            refine ⟨528806510492054261089480627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705075347322739014785974169 528806510492054261089480627)
            ·
              refine ⟨793209765738081391634220941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528806510492054261089480627 793209765738081391634220941)
              ·
                refine ⟨297453662151780521862832853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 793209765738081391634220941 297453662151780521862832853)
                ·
                  refine ⟨6971570206682355981160145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 297453662151780521862832853 6971570206682355981160145)
                  ·
                    refine ⟨5228677655011766985870109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6971570206682355981160145 5228677655011766985870109)
                    ·
                      refine ⟨1960754120629412619701291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5228677655011766985870109 1960754120629412619701291)
                      ·
                        rfl

theorem cell23_3818555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 3].length) (baseStart_3818555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818555 prefixEnd_3818555 := by exact prefixLift 3818555
  have htrace : WordTrace (prefixWord ++ tailWord_3818555) baseStart_3818555 baseEnd_3818555 := by
    simpa [prefixWord, tailWord_3818555, baseEnd_3818555] using wordTrace_append hprefix tailTrace_3818555
  have hstable : (prefixWord ++ tailWord_3818555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818555).length < 2 ^ (prefixWord ++ tailWord_3818555).sum := by decide
  have hdescent : baseEnd_3818555 < baseStart_3818555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818590 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_3818590 : Nat := 118140960795 + 3818590 * 2 ^ 59
def prefixEnd_3818590 : Nat := 4983230072969 + 3 ^ 40 * 3818590 * 2
def baseEnd_3818590 : Nat := 1960772092452319982763631

theorem tailTrace_3818590 : CollatzResearch.WordTrace tailWord_3818590 prefixEnd_3818590 1960772092452319982763631 := by
  unfold tailWord_3818590
  simp only [CollatzResearch.WordTrace]
  refine ⟨17409427404488508511967653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92850279490605378730494149 17409427404488508511967653)
  ·
    refine ⟨3264267638341595345993935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17409427404488508511967653 3264267638341595345993935)
    ·
      refine ⟨4896401457512393018990903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3264267638341595345993935 4896401457512393018990903)
      ·
        refine ⟨7344602186268589528486355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4896401457512393018990903 7344602186268589528486355)
        ·
          refine ⟨11016903279402884292729533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7344602186268589528486355 11016903279402884292729533)
          ·
            refine ⟨4131338729776081609773575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11016903279402884292729533 4131338729776081609773575)
            ·
              refine ⟨6197008094664122414660363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4131338729776081609773575 6197008094664122414660363)
              ·
                refine ⟨9295512141996183621990545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6197008094664122414660363 9295512141996183621990545)
                ·
                  refine ⟨6971634106497137716492909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9295512141996183621990545 6971634106497137716492909)
                  ·
                    refine ⟨2614362789936426643684841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6971634106497137716492909 2614362789936426643684841)
                    ·
                      refine ⟨1960772092452319982763631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2614362789936426643684841 1960772092452319982763631)
                      ·
                        rfl

theorem cell23_3818590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_3818590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818590 prefixEnd_3818590 := by exact prefixLift 3818590
  have htrace : WordTrace (prefixWord ++ tailWord_3818590) baseStart_3818590 baseEnd_3818590 := by
    simpa [prefixWord, tailWord_3818590, baseEnd_3818590] using wordTrace_append hprefix tailTrace_3818590
  have hstable : (prefixWord ++ tailWord_3818590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818590).length < 2 ^ (prefixWord ++ tailWord_3818590).sum := by decide
  have hdescent : baseEnd_3818590 < baseStart_3818590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818606 : List Nat := [4, 1, 2, 2, 1, 2, 4, 1, 1, 2, 3]
def baseStart_3818606 : Nat := 118140960795 + 3818606 * 2 ^ 59
def prefixEnd_3818606 : Nat := 4983230072969 + 3 ^ 40 * 3818606 * 2
def baseEnd_3818606 : Nat := 1960780308142791920163557

theorem tailTrace_3818606 : CollatzResearch.WordTrace tailWord_3818606 prefixEnd_3818606 1960780308142791920163557 := by
  unfold tailWord_3818606
  simp only [CollatzResearch.WordTrace]
  refine ⟨17409500350481262853540459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92850668535900068552215781 17409500350481262853540459)
  ·
    refine ⟨26114250525721894280310689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17409500350481262853540459 26114250525721894280310689)
    ·
      refine ⟨19585687894291420710233017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26114250525721894280310689 19585687894291420710233017)
      ·
        refine ⟨14689265920718565532674763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19585687894291420710233017 14689265920718565532674763)
        ·
          refine ⟨22033898881077848299012145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14689265920718565532674763 22033898881077848299012145)
          ·
            refine ⟨16525424160808386224259109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22033898881077848299012145 16525424160808386224259109)
            ·
              refine ⟨3098517030151572417048583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16525424160808386224259109 3098517030151572417048583)
              ·
                refine ⟨4647775545227358625572875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098517030151572417048583 4647775545227358625572875)
                ·
                  refine ⟨6971663317841037938359313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4647775545227358625572875 6971663317841037938359313)
                  ·
                    refine ⟨5228747488380778453769485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6971663317841037938359313 5228747488380778453769485)
                    ·
                      refine ⟨1960780308142791920163557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5228747488380778453769485 1960780308142791920163557)
                      ·
                        rfl

theorem cell23_3818606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_3818606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818606 prefixEnd_3818606 := by exact prefixLift 3818606
  have htrace : WordTrace (prefixWord ++ tailWord_3818606) baseStart_3818606 baseEnd_3818606 := by
    simpa [prefixWord, tailWord_3818606, baseEnd_3818606] using wordTrace_append hprefix tailTrace_3818606
  have hstable : (prefixWord ++ tailWord_3818606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818606).length < 2 ^ (prefixWord ++ tailWord_3818606).sum := by decide
  have hdescent : baseEnd_3818606 < baseStart_3818606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818613 : List Nat := [1, 3, 4, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3818613 : Nat := 118140960795 + 3818613 * 2 ^ 59
def prefixEnd_3818613 : Nat := 4983230072969 + 3 ^ 40 * 3818613 * 2
def baseEnd_3818613 : Nat := 653594634169124464258675

theorem tailTrace_3818613 : CollatzResearch.WordTrace tailWord_3818613 prefixEnd_3818613 653594634169124464258675 := by
  unfold tailWord_3818613
  simp only [CollatzResearch.WordTrace]
  refine ⟨139276258114824743023828493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92850838743216495349218995 139276258114824743023828493)
  ·
    refine ⟨52228596793059278633935685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139276258114824743023828493 52228596793059278633935685)
    ·
      refine ⟨9792861898698614743862941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52228596793059278633935685 9792861898698614743862941)
      ·
        refine ⟨3672323212011980528948603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9792861898698614743862941 3672323212011980528948603)
        ·
          refine ⟨5508484818017970793422905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3672323212011980528948603 5508484818017970793422905)
          ·
            refine ⟨4131363613513478095067179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5508484818017970793422905 4131363613513478095067179)
            ·
              refine ⟨6197045420270217142600769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4131363613513478095067179 6197045420270217142600769)
              ·
                refine ⟨4647784065202662856950577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6197045420270217142600769 4647784065202662856950577)
                ·
                  refine ⟨3485838048901997142712933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4647784065202662856950577 3485838048901997142712933)
                  ·
                    refine ⟨653594634169124464258675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3485838048901997142712933 653594634169124464258675)
                    ·
                      rfl

theorem cell23_3818613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3818613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818613 prefixEnd_3818613 := by exact prefixLift 3818613
  have htrace : WordTrace (prefixWord ++ tailWord_3818613) baseStart_3818613 baseEnd_3818613 := by
    simpa [prefixWord, tailWord_3818613, baseEnd_3818613] using wordTrace_append hprefix tailTrace_3818613
  have hstable : (prefixWord ++ tailWord_3818613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818613).length < 2 ^ (prefixWord ++ tailWord_3818613).sum := by decide
  have hdescent : baseEnd_3818613 < baseStart_3818613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818695 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 3, 7]
def baseStart_3818695 : Nat := 118140960795 + 3818695 * 2 ^ 59
def prefixEnd_3818695 : Nat := 4983230072969 + 3 ^ 40 * 3818695 * 2
def baseEnd_3818695 : Nat := 653608669307014023983549

theorem tailTrace_3818695 : CollatzResearch.WordTrace tailWord_3818695 prefixEnd_3818695 653608669307014023983549 := by
  unfold tailWord_3818695
  simp only [CollatzResearch.WordTrace]
  refine ⟨139279248900527671028313539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92852832600351780685542359 139279248900527671028313539)
  ·
    refine ⟨208918873350791506542470309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139279248900527671028313539 208918873350791506542470309)
    ·
      refine ⟨39172288753273407476713183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208918873350791506542470309 39172288753273407476713183)
      ·
        refine ⟨58758433129910111215069775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39172288753273407476713183 58758433129910111215069775)
        ·
          refine ⟨88137649694865166822604663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58758433129910111215069775 88137649694865166822604663)
          ·
            refine ⟨132206474542297750233906995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88137649694865166822604663 132206474542297750233906995)
            ·
              refine ⟨198309711813446625350860493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132206474542297750233906995 198309711813446625350860493)
              ·
                refine ⟨74366141930042484506572685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198309711813446625350860493 74366141930042484506572685)
                ·
                  refine ⟨27887303223765931689964757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74366141930042484506572685 27887303223765931689964757)
                  ·
                    refine ⟨653608669307014023983549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27887303223765931689964757 653608669307014023983549)
                    ·
                      rfl

theorem cell23_3818695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_3818695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818695 prefixEnd_3818695 := by exact prefixLift 3818695
  have htrace : WordTrace (prefixWord ++ tailWord_3818695) baseStart_3818695 baseEnd_3818695 := by
    simpa [prefixWord, tailWord_3818695, baseEnd_3818695] using wordTrace_append hprefix tailTrace_3818695
  have hstable : (prefixWord ++ tailWord_3818695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818695).length < 2 ^ (prefixWord ++ tailWord_3818695).sum := by decide
  have hdescent : baseEnd_3818695 < baseStart_3818695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818705 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 7]
def baseStart_3818705 : Nat := 118140960795 + 3818705 * 2 ^ 59
def prefixEnd_3818705 : Nat := 4983230072969 + 3 ^ 40 * 3818705 * 2
def baseEnd_3818705 : Nat := 1960831142727587032825601

theorem tailTrace_3818705 : CollatzResearch.WordTrace tailWord_3818705 prefixEnd_3818705 1960831142727587032825601 := by
  unfold tailWord_3818705
  simp only [CollatzResearch.WordTrace]
  refine ⟨139279613630491442736177569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92853075753660961824118379 139279613630491442736177569)
  ·
    refine ⟨104459710222868582052133177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139279613630491442736177569 104459710222868582052133177)
    ·
      refine ⟨78344782667151436539099883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104459710222868582052133177 78344782667151436539099883)
      ·
        refine ⟨117517174000727154808649825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78344782667151436539099883 117517174000727154808649825)
        ·
          refine ⟨88137880500545366106487369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117517174000727154808649825 88137880500545366106487369)
          ·
            refine ⟨66103410375409024579865527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88137880500545366106487369 66103410375409024579865527)
            ·
              refine ⟨99155115563113536869798291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66103410375409024579865527 99155115563113536869798291)
              ·
                refine ⟨148732673344670305304697437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99155115563113536869798291 148732673344670305304697437)
                ·
                  refine ⟨55774752504251364489261539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148732673344670305304697437 55774752504251364489261539)
                  ·
                    refine ⟨83662128756377046733892309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55774752504251364489261539 83662128756377046733892309)
                    ·
                      refine ⟨1960831142727587032825601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83662128756377046733892309 1960831142727587032825601)
                      ·
                        rfl

theorem cell23_3818705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_3818705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818705 prefixEnd_3818705 := by exact prefixLift 3818705
  have htrace : WordTrace (prefixWord ++ tailWord_3818705) baseStart_3818705 baseEnd_3818705 := by
    simpa [prefixWord, tailWord_3818705, baseEnd_3818705] using wordTrace_append hprefix tailTrace_3818705
  have hstable : (prefixWord ++ tailWord_3818705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818705).length < 2 ^ (prefixWord ++ tailWord_3818705).sum := by decide
  have hdescent : baseEnd_3818705 < baseStart_3818705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818733 : List Nat := [1, 5, 1, 2, 2, 3, 2, 2, 5]
def baseStart_3818733 : Nat := 118140960795 + 3818733 * 2 ^ 59
def prefixEnd_3818733 : Nat := 4983230072969 + 3 ^ 40 * 3818733 * 2
def baseEnd_3818733 : Nat := 217871724465101435919497

theorem tailTrace_3818733 : CollatzResearch.WordTrace tailWord_3818733 prefixEnd_3818733 217871724465101435919497 := by
  unfold tailWord_3818733
  simp only [CollatzResearch.WordTrace]
  refine ⟨139280634874390003518196853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92853756582926669012131235 139280634874390003518196853)
  ·
    refine ⟨13057559519474062829830955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139280634874390003518196853 13057559519474062829830955)
    ·
      refine ⟨19586339279211094244746433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13057559519474062829830955 19586339279211094244746433)
      ·
        refine ⟨14689754459408320683559825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19586339279211094244746433 14689754459408320683559825)
        ·
          refine ⟨11017315844556240512669869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14689754459408320683559825 11017315844556240512669869)
          ·
            refine ⟨4131493441708590192251201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11017315844556240512669869 4131493441708590192251201)
            ·
              refine ⟨3098620081281442644188401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4131493441708590192251201 3098620081281442644188401)
              ·
                refine ⟨2323965060961081983141301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3098620081281442644188401 2323965060961081983141301)
                ·
                  refine ⟨217871724465101435919497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2323965060961081983141301 217871724465101435919497)
                  ·
                    rfl

theorem cell23_3818733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_3818733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818733 prefixEnd_3818733 := by exact prefixLift 3818733
  have htrace : WordTrace (prefixWord ++ tailWord_3818733) baseStart_3818733 baseEnd_3818733 := by
    simpa [prefixWord, tailWord_3818733, baseEnd_3818733] using wordTrace_append hprefix tailTrace_3818733
  have hstable : (prefixWord ++ tailWord_3818733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818733).length < 2 ^ (prefixWord ++ tailWord_3818733).sum := by decide
  have hdescent : baseEnd_3818733 < baseStart_3818733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818742 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_3818742 : Nat := 118140960795 + 3818742 * 2 ^ 59
def prefixEnd_3818742 : Nat := 4983230072969 + 3 ^ 40 * 3818742 * 2
def baseEnd_3818742 : Nat := 653616713837267796020977

theorem tailTrace_3818742 : CollatzResearch.WordTrace tailWord_3818742 prefixEnd_3818742 653616713837267796020977 := by
  unfold tailWord_3818742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8705060195709837378454655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92853975420904932036849653 8705060195709837378454655)
  ·
    refine ⟨13057590293564756067681983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8705060195709837378454655 13057590293564756067681983)
    ·
      refine ⟨19586385440347134101522975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13057590293564756067681983 19586385440347134101522975)
      ·
        refine ⟨29379578160520701152284463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19586385440347134101522975 29379578160520701152284463)
        ·
          refine ⟨44069367240781051728426695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29379578160520701152284463 44069367240781051728426695)
          ·
            refine ⟨66104050861171577592640043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44069367240781051728426695 66104050861171577592640043)
            ·
              refine ⟨99156076291757366388960065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66104050861171577592640043 99156076291757366388960065)
              ·
                refine ⟨74367057218818024791720049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99156076291757366388960065 74367057218818024791720049)
                ·
                  refine ⟨55775292914113518593790037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74367057218818024791720049 55775292914113518593790037)
                  ·
                    refine ⟨653616713837267796020977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55775292914113518593790037 653616713837267796020977)
                    ·
                      rfl

theorem cell23_3818742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_3818742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818742 prefixEnd_3818742 := by exact prefixLift 3818742
  have htrace : WordTrace (prefixWord ++ tailWord_3818742) baseStart_3818742 baseEnd_3818742 := by
    simpa [prefixWord, tailWord_3818742, baseEnd_3818742] using wordTrace_append hprefix tailTrace_3818742
  have hstable : (prefixWord ++ tailWord_3818742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818742).length < 2 ^ (prefixWord ++ tailWord_3818742).sum := by decide
  have hdescent : baseEnd_3818742 < baseStart_3818742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818752 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 3]
def baseStart_3818752 : Nat := 118140960795 + 3818752 * 2 ^ 59
def prefixEnd_3818752 : Nat := 4983230072969 + 3 ^ 40 * 3818752 * 2
def baseEnd_3818752 : Nat := 1960855276318348348937885

theorem tailTrace_3818752 : CollatzResearch.WordTrace tailWord_3818752 prefixEnd_3818752 1960855276318348348937885 := by
  unfold tailWord_3818752
  simp only [CollatzResearch.WordTrace]
  refine ⟨69640663930660584881569255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92854218574214113175425673 69640663930660584881569255)
  ·
    refine ⟨104460995895990877322353883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69640663930660584881569255 104460995895990877322353883)
    ·
      refine ⟨156691493843986315983530825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104460995895990877322353883 156691493843986315983530825)
      ·
        refine ⟨117518620382989736987648119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156691493843986315983530825 117518620382989736987648119)
        ·
          refine ⟨176277930574484605481472179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117518620382989736987648119 176277930574484605481472179)
          ·
            refine ⟨264416895861726908222208269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176277930574484605481472179 264416895861726908222208269)
            ·
              refine ⟨99156335948147590583328101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264416895861726908222208269 99156335948147590583328101)
              ·
                refine ⟨18591812990277673234374019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99156335948147590583328101 18591812990277673234374019)
                ·
                  refine ⟨27887719485416509851561029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18591812990277673234374019 27887719485416509851561029)
                  ·
                    refine ⟨5228947403515595597167693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27887719485416509851561029 5228947403515595597167693)
                    ·
                      refine ⟨1960855276318348348937885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5228947403515595597167693 1960855276318348348937885)
                      ·
                        rfl

theorem cell23_3818752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_3818752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818752 prefixEnd_3818752 := by exact prefixLift 3818752
  have htrace : WordTrace (prefixWord ++ tailWord_3818752) baseStart_3818752 baseEnd_3818752 := by
    simpa [prefixWord, tailWord_3818752, baseEnd_3818752] using wordTrace_append hprefix tailTrace_3818752
  have hstable : (prefixWord ++ tailWord_3818752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818752).length < 2 ^ (prefixWord ++ tailWord_3818752).sum := by decide
  have hdescent : baseEnd_3818752 < baseStart_3818752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818766 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4]
def baseStart_3818766 : Nat := 118140960795 + 3818766 * 2 ^ 59
def prefixEnd_3818766 : Nat := 4983230072969 + 3 ^ 40 * 3818766 * 2
def baseEnd_3818766 : Nat := 1960862465047511294162821

theorem tailTrace_3818766 : CollatzResearch.WordTrace tailWord_3818766 prefixEnd_3818766 1960862465047511294162821 := by
  unfold tailWord_3818766
  simp only [CollatzResearch.WordTrace]
  refine ⟨17410229810408806269268519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92854558988846966769432101 17410229810408806269268519)
  ·
    refine ⟨26115344715613209403902779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17410229810408806269268519 26115344715613209403902779)
    ·
      refine ⟨39173017073419814105854169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26115344715613209403902779 39173017073419814105854169)
      ·
        refine ⟨29379762805064860579390627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39173017073419814105854169 29379762805064860579390627)
        ·
          refine ⟨44069644207597290869085941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29379762805064860579390627 44069644207597290869085941)
          ·
            refine ⟨4131529144462246018976807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44069644207597290869085941 4131529144462246018976807)
            ·
              refine ⟨6197293716693369028465211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4131529144462246018976807 6197293716693369028465211)
              ·
                refine ⟨9295940575040053542697817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6197293716693369028465211 9295940575040053542697817)
                ·
                  refine ⟨6971955431280040157023363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9295940575040053542697817 6971955431280040157023363)
                  ·
                    refine ⟨10457933146920060235535045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6971955431280040157023363 10457933146920060235535045)
                    ·
                      refine ⟨1960862465047511294162821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10457933146920060235535045 1960862465047511294162821)
                      ·
                        rfl

theorem cell23_3818766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_3818766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818766 prefixEnd_3818766 := by exact prefixLift 3818766
  have htrace : WordTrace (prefixWord ++ tailWord_3818766) baseStart_3818766 baseEnd_3818766 := by
    simpa [prefixWord, tailWord_3818766, baseEnd_3818766] using wordTrace_append hprefix tailTrace_3818766
  have hstable : (prefixWord ++ tailWord_3818766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818766).length < 2 ^ (prefixWord ++ tailWord_3818766).sum := by decide
  have hdescent : baseEnd_3818766 < baseStart_3818766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818776 : List Nat := [2, 1, 2, 3, 1, 3, 1, 5, 1, 4]
def baseStart_3818776 : Nat := 118140960795 + 3818776 * 2 ^ 59
def prefixEnd_3818776 : Nat := 4983230072969 + 3 ^ 40 * 3818776 * 2
def baseEnd_3818776 : Nat := 653622533284685418345925

theorem tailTrace_3818776 : CollatzResearch.WordTrace tailWord_3818776 prefixEnd_3818776 653622533284685418345925 := by
  unfold tailWord_3818776
  simp only [CollatzResearch.WordTrace]
  refine ⟨69641101606617110931006091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92854802142156147908008121 69641101606617110931006091)
  ·
    refine ⟨104461652409925666396509137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69641101606617110931006091 104461652409925666396509137)
    ·
      refine ⟨78346239307444249797381853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104461652409925666396509137 78346239307444249797381853)
      ·
        refine ⟨29379839740291593674018195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78346239307444249797381853 29379839740291593674018195)
        ·
          refine ⟨44069759610437390511027293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29379839740291593674018195 44069759610437390511027293)
          ·
            refine ⟨16526159853914021441635235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44069759610437390511027293 16526159853914021441635235)
            ·
              refine ⟨24789239780871032162452853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16526159853914021441635235 24789239780871032162452853)
              ·
                refine ⟨2323991229456659265229955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24789239780871032162452853 2323991229456659265229955)
                ·
                  refine ⟨3485986844184988897844933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2323991229456659265229955 3485986844184988897844933)
                  ·
                    refine ⟨653622533284685418345925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3485986844184988897844933 653622533284685418345925)
                    ·
                      rfl

theorem cell23_3818776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 1, 4].length) (baseStart_3818776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818776 prefixEnd_3818776 := by exact prefixLift 3818776
  have htrace : WordTrace (prefixWord ++ tailWord_3818776) baseStart_3818776 baseEnd_3818776 := by
    simpa [prefixWord, tailWord_3818776, baseEnd_3818776] using wordTrace_append hprefix tailTrace_3818776
  have hstable : (prefixWord ++ tailWord_3818776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818776).length < 2 ^ (prefixWord ++ tailWord_3818776).sum := by decide
  have hdescent : baseEnd_3818776 < baseStart_3818776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818789 : List Nat := [1, 3, 1, 2, 4, 1, 3, 2, 6]
def baseStart_3818789 : Nat := 118140960795 + 3818789 * 2 ^ 59
def prefixEnd_3818789 : Nat := 4983230072969 + 3 ^ 40 * 3818789 * 2
def baseEnd_3818789 : Nat := 217874919455840522686135

theorem tailTrace_3818789 : CollatzResearch.WordTrace tailWord_3818789 prefixEnd_3818789 217874919455840522686135 := by
  unfold tailWord_3818789
  simp only [CollatzResearch.WordTrace]
  refine ⟨139282677362187125082235421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92855118241458083388156947 139282677362187125082235421)
  ·
    refine ⟨52231004010820171905838283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139282677362187125082235421 52231004010820171905838283)
    ·
      refine ⟨78346506016230257858757425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52231004010820171905838283 78346506016230257858757425)
      ·
        refine ⟨58759879512172693394068069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78346506016230257858757425 58759879512172693394068069)
        ·
          refine ⟨11017477408532380011387763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58759879512172693394068069 11017477408532380011387763)
          ·
            refine ⟨16526216112798570017081645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11017477408532380011387763 16526216112798570017081645)
            ·
              refine ⟨6197331042299463756405617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16526216112798570017081645 6197331042299463756405617)
              ·
                refine ⟨4647998281724597817304213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6197331042299463756405617 4647998281724597817304213)
                ·
                  refine ⟨217874919455840522686135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4647998281724597817304213 217874919455840522686135)
                  ·
                    rfl

theorem cell23_3818789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 6].length) (baseStart_3818789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818789 prefixEnd_3818789 := by exact prefixLift 3818789
  have htrace : WordTrace (prefixWord ++ tailWord_3818789) baseStart_3818789 baseEnd_3818789 := by
    simpa [prefixWord, tailWord_3818789, baseEnd_3818789] using wordTrace_append hprefix tailTrace_3818789
  have hstable : (prefixWord ++ tailWord_3818789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818789).length < 2 ^ (prefixWord ++ tailWord_3818789).sum := by decide
  have hdescent : baseEnd_3818789 < baseStart_3818789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818832 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 3, 6]
def baseStart_3818832 : Nat := 118140960795 + 3818832 * 2 ^ 59
def prefixEnd_3818832 : Nat := 4983230072969 + 3 ^ 40 * 3818832 * 2
def baseEnd_3818832 : Nat := 653632118256902678645839

theorem tailTrace_3818832 : CollatzResearch.WordTrace tailWord_3818832 prefixEnd_3818832 653632118256902678645839 := by
  unfold tailWord_3818832
  simp only [CollatzResearch.WordTrace]
  refine ⟨69642122850515671713025375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92856163800687562284033833 69642122850515671713025375)
  ·
    refine ⟨104463184275773507569538063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69642122850515671713025375 104463184275773507569538063)
    ·
      refine ⟨156694776413660261354307095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104463184275773507569538063 156694776413660261354307095)
      ·
        refine ⟨235042164620490392031460643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156694776413660261354307095 235042164620490392031460643)
        ·
          refine ⟨352563246930735588047190965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235042164620490392031460643 352563246930735588047190965)
          ·
            refine ⟨33052804399756461379424153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 352563246930735588047190965 33052804399756461379424153)
            ·
              refine ⟨24789603299817346034568115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33052804399756461379424153 24789603299817346034568115)
              ·
                refine ⟨37184404949726019051852173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24789603299817346034568115 37184404949726019051852173)
                ·
                  refine ⟨13944151856147257144444565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37184404949726019051852173 13944151856147257144444565)
                  ·
                    refine ⟨653632118256902678645839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13944151856147257144444565 653632118256902678645839)
                    ·
                      rfl

theorem cell23_3818832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 3, 6].length) (baseStart_3818832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818832 prefixEnd_3818832 := by exact prefixLift 3818832
  have htrace : WordTrace (prefixWord ++ tailWord_3818832) baseStart_3818832 baseEnd_3818832 := by
    simpa [prefixWord, tailWord_3818832, baseEnd_3818832] using wordTrace_append hprefix tailTrace_3818832
  have hstable : (prefixWord ++ tailWord_3818832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818832).length < 2 ^ (prefixWord ++ tailWord_3818832).sum := by decide
  have hdescent : baseEnd_3818832 < baseStart_3818832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818866 : List Nat := [3, 2, 1, 2, 1, 2, 3, 3, 2, 4]
def baseStart_3818866 : Nat := 118140960795 + 3818866 * 2 ^ 59
def prefixEnd_3818866 : Nat := 4983230072969 + 3 ^ 40 * 3818866 * 2
def baseEnd_3818866 : Nat := 653637937704320300970787

theorem tailTrace_3818866 : CollatzResearch.WordTrace tailWord_3818866 prefixEnd_3818866 653637937704320300970787 := by
  unfold tailWord_3818866
  simp only [CollatzResearch.WordTrace]
  refine ⟨34821371445727041808197113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92856990521938778155192301 34821371445727041808197113)
  ·
    refine ⟨26116028584295281356147835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34821371445727041808197113 26116028584295281356147835)
    ·
      refine ⟨39174042876442922034221753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26116028584295281356147835 39174042876442922034221753)
      ·
        refine ⟨29380532157332191525666315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39174042876442922034221753 29380532157332191525666315)
        ·
          refine ⟨44070798235998287288499473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29380532157332191525666315 44070798235998287288499473)
          ·
            refine ⟨33053098676998715466374605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44070798235998287288499473 33053098676998715466374605)
            ·
              refine ⟨12394912003874518299890477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33053098676998715466374605 12394912003874518299890477)
              ·
                refine ⟨4648092001452944362458929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12394912003874518299890477 4648092001452944362458929)
                ·
                  refine ⟨3486069001089708271844197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4648092001452944362458929 3486069001089708271844197)
                  ·
                    refine ⟨653637937704320300970787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3486069001089708271844197 653637937704320300970787)
                    ·
                      rfl

theorem cell23_3818866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_3818866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818866 prefixEnd_3818866 := by exact prefixLift 3818866
  have htrace : WordTrace (prefixWord ++ tailWord_3818866) baseStart_3818866 baseEnd_3818866 := by
    simpa [prefixWord, tailWord_3818866, baseEnd_3818866] using wordTrace_append hprefix tailTrace_3818866
  have hstable : (prefixWord ++ tailWord_3818866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818866).length < 2 ^ (prefixWord ++ tailWord_3818866).sum := by decide
  have hdescent : baseEnd_3818866 < baseStart_3818866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818909 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 2, 7]
def baseStart_3818909 : Nat := 118140960795 + 3818909 * 2 ^ 59
def prefixEnd_3818909 : Nat := 4983230072969 + 3 ^ 40 * 3818909 * 2
def baseEnd_3818909 : Nat := 653645297593701411558221

theorem tailTrace_3818909 : CollatzResearch.WordTrace tailWord_3818909 prefixEnd_3818909 653645297593701411558221 := by
  unfold tailWord_3818909
  simp only [CollatzResearch.WordTrace]
  refine ⟨139287054121752385576603781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92858036081168257051069187 139287054121752385576603781)
  ·
    refine ⟨26116322647828572295613209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139287054121752385576603781 26116322647828572295613209)
    ·
      refine ⟨19587241985871429221709907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26116322647828572295613209 19587241985871429221709907)
      ·
        refine ⟨29380862978807143832564861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19587241985871429221709907 29380862978807143832564861)
        ·
          refine ⟨11017823617052678937211823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29380862978807143832564861 11017823617052678937211823)
          ·
            refine ⟨16526735425579018405817735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11017823617052678937211823 16526735425579018405817735)
            ·
              refine ⟨24790103138368527608726603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16526735425579018405817735 24790103138368527608726603)
              ·
                refine ⟨37185154707552791413089905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24790103138368527608726603 37185154707552791413089905)
                ·
                  refine ⟨27888866030664593559817429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37185154707552791413089905 27888866030664593559817429)
                  ·
                    refine ⟨653645297593701411558221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27888866030664593559817429 653645297593701411558221)
                    ·
                      rfl

theorem cell23_3818909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_3818909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818909 prefixEnd_3818909 := by exact prefixLift 3818909
  have htrace : WordTrace (prefixWord ++ tailWord_3818909) baseStart_3818909 baseEnd_3818909 := by
    simpa [prefixWord, tailWord_3818909, baseEnd_3818909] using wordTrace_append hprefix tailTrace_3818909
  have hstable : (prefixWord ++ tailWord_3818909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818909).length < 2 ^ (prefixWord ++ tailWord_3818909).sum := by decide
  have hdescent : baseEnd_3818909 < baseStart_3818909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818929 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 2, 3, 4]
def baseStart_3818929 : Nat := 118140960795 + 3818929 * 2 ^ 59
def prefixEnd_3818929 : Nat := 4983230072969 + 3 ^ 40 * 3818929 * 2
def baseEnd_3818929 : Nat := 1960946162394194156424571

theorem tailTrace_3818929 : CollatzResearch.WordTrace tailWord_3818929 prefixEnd_3818929 1960946162394194156424571 := by
  unfold tailWord_3818929
  simp only [CollatzResearch.WordTrace]
  refine ⟨139287783581679928992331841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92858522387786619328221227 139287783581679928992331841)
  ·
    refine ⟨104465837686259946744248881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139287783581679928992331841 104465837686259946744248881)
    ·
      refine ⟨78349378264694960058186661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104465837686259946744248881 78349378264694960058186661)
      ·
        refine ⟨14690508424630305010909999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78349378264694960058186661 14690508424630305010909999)
        ·
          refine ⟨22035762636945457516364999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14690508424630305010909999 22035762636945457516364999)
          ·
            refine ⟨33053643955418186274547499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22035762636945457516364999 33053643955418186274547499)
            ·
              refine ⟨49580465933127279411821249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33053643955418186274547499 49580465933127279411821249)
              ·
                refine ⟨37185349449845459558865937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49580465933127279411821249 37185349449845459558865937)
                ·
                  refine ⟨27889012087384094669149453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37185349449845459558865937 27889012087384094669149453)
                  ·
                    refine ⟨10458379532769035500931045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27889012087384094669149453 10458379532769035500931045)
                    ·
                      refine ⟨1960946162394194156424571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10458379532769035500931045 1960946162394194156424571)
                      ·
                        rfl

theorem cell23_3818929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_3818929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818929 prefixEnd_3818929 := by exact prefixLift 3818929
  have htrace : WordTrace (prefixWord ++ tailWord_3818929) baseStart_3818929 baseEnd_3818929 := by
    simpa [prefixWord, tailWord_3818929, baseEnd_3818929] using wordTrace_append hprefix tailTrace_3818929
  have hstable : (prefixWord ++ tailWord_3818929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818929).length < 2 ^ (prefixWord ++ tailWord_3818929).sum := by decide
  have hdescent : baseEnd_3818929 < baseStart_3818929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818933 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 3, 3, 2]
def baseStart_3818933 : Nat := 118140960795 + 3818933 * 2 ^ 59
def prefixEnd_3818933 : Nat := 4983230072969 + 3 ^ 40 * 3818933 * 2
def baseEnd_3818933 : Nat := 1960948216316812140774553

theorem tailTrace_3818933 : CollatzResearch.WordTrace tailWord_3818933 prefixEnd_3818933 1960948216316812140774553 := by
  unfold tailWord_3818933
  simp only [CollatzResearch.WordTrace]
  refine ⟨139287929473665437675477453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92858619649110291783651635 139287929473665437675477453)
  ·
    refine ⟨52232973552624539128304045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139287929473665437675477453 52232973552624539128304045)
    ·
      refine ⟨19587365082234202173114017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52232973552624539128304045 19587365082234202173114017)
      ·
        refine ⟨14690523811675651629835513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19587365082234202173114017 14690523811675651629835513)
        ·
          refine ⟨11017892858756738722376635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14690523811675651629835513 11017892858756738722376635)
          ·
            refine ⟨16526839288135108083564953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11017892858756738722376635 16526839288135108083564953)
            ·
              refine ⟨12395129466101331062673715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16526839288135108083564953 12395129466101331062673715)
              ·
                refine ⟨18592694199151996594010573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12395129466101331062673715 18592694199151996594010573)
                ·
                  refine ⟨6972260324681998722753965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18592694199151996594010573 6972260324681998722753965)
                  ·
                    refine ⟨2614597621755749521032737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6972260324681998722753965 2614597621755749521032737)
                    ·
                      refine ⟨1960948216316812140774553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2614597621755749521032737 1960948216316812140774553)
                      ·
                        rfl

theorem cell23_3818933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_3818933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818933 prefixEnd_3818933 := by exact prefixLift 3818933
  have htrace : WordTrace (prefixWord ++ tailWord_3818933) baseStart_3818933 baseEnd_3818933 := by
    simpa [prefixWord, tailWord_3818933, baseEnd_3818933] using wordTrace_append hprefix tailTrace_3818933
  have hstable : (prefixWord ++ tailWord_3818933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818933).length < 2 ^ (prefixWord ++ tailWord_3818933).sum := by decide
  have hdescent : baseEnd_3818933 < baseStart_3818933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818959 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 4]
def baseStart_3818959 : Nat := 118140960795 + 3818959 * 2 ^ 59
def prefixEnd_3818959 : Nat := 4983230072969 + 3 ^ 40 * 3818959 * 2
def baseEnd_3818959 : Nat := 1960961566813829039049433

theorem tailTrace_3818959 : CollatzResearch.WordTrace tailWord_3818959 prefixEnd_3818959 1960961566813829039049433 := by
  unfold tailWord_3818959
  simp only [CollatzResearch.WordTrace]
  refine ⟨139288877771571244115923931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92859251847714162743949287 139288877771571244115923931)
  ·
    refine ⟨208933316657356866173885897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139288877771571244115923931 208933316657356866173885897)
    ·
      refine ⟨156699987493017649630414423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208933316657356866173885897 156699987493017649630414423)
      ·
        refine ⟨235049981239526474445621635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156699987493017649630414423 235049981239526474445621635)
        ·
          refine ⟨352574971859289711668432453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235049981239526474445621635 352574971859289711668432453)
          ·
            refine ⟨66107807223616820937831085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352574971859289711668432453 66107807223616820937831085)
            ·
              refine ⟨24790427708856307851686657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66107807223616820937831085 24790427708856307851686657)
              ·
                refine ⟨18592820781642230888764993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24790427708856307851686657 18592820781642230888764993)
                ·
                  refine ⟨13944615586231673166573745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18592820781642230888764993 13944615586231673166573745)
                  ·
                    refine ⟨10458461689673754874930309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13944615586231673166573745 10458461689673754874930309)
                    ·
                      refine ⟨1960961566813829039049433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10458461689673754874930309 1960961566813829039049433)
                      ·
                        rfl

theorem cell23_3818959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_3818959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818959 prefixEnd_3818959 := by exact prefixLift 3818959
  have htrace : WordTrace (prefixWord ++ tailWord_3818959) baseStart_3818959 baseEnd_3818959 := by
    simpa [prefixWord, tailWord_3818959, baseEnd_3818959] using wordTrace_append hprefix tailTrace_3818959
  have hstable : (prefixWord ++ tailWord_3818959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818959).length < 2 ^ (prefixWord ++ tailWord_3818959).sum := by decide
  have hdescent : baseEnd_3818959 < baseStart_3818959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818969 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 7]
def baseStart_3818969 : Nat := 118140960795 + 3818969 * 2 ^ 59
def prefixEnd_3818969 : Nat := 4983230072969 + 3 ^ 40 * 3818969 * 2
def baseEnd_3818969 : Nat := 217885189068930444436043

theorem tailTrace_3818969 : CollatzResearch.WordTrace tailWord_3818969 prefixEnd_3818969 217885189068930444436043 := by
  unfold tailWord_3818969
  simp only [CollatzResearch.WordTrace]
  refine ⟨139289242501535015823787961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92859495001023343882525307 139289242501535015823787961)
  ·
    refine ⟨104466931876151261867840971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139289242501535015823787961 104466931876151261867840971)
    ·
      refine ⟨156700397814226892801761457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104466931876151261867840971 156700397814226892801761457)
      ·
        refine ⟨117525298360670169601321093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156700397814226892801761457 117525298360670169601321093)
        ·
          refine ⟨22035993442625656800247705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117525298360670169601321093 22035993442625656800247705)
          ·
            refine ⟨16526995081969242600185779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22035993442625656800247705 16526995081969242600185779)
            ·
              refine ⟨24790492622953863900278669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16526995081969242600185779 24790492622953863900278669)
              ·
                refine ⟨9296434733607698962604501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24790492622953863900278669 9296434733607698962604501)
                ·
                  refine ⟨217885189068930444436043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9296434733607698962604501 217885189068930444436043)
                  ·
                    rfl

theorem cell23_3818969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 7].length) (baseStart_3818969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3818969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3818969 prefixEnd_3818969 := by exact prefixLift 3818969
  have htrace : WordTrace (prefixWord ++ tailWord_3818969) baseStart_3818969 baseEnd_3818969 := by
    simpa [prefixWord, tailWord_3818969, baseEnd_3818969] using wordTrace_append hprefix tailTrace_3818969
  have hstable : (prefixWord ++ tailWord_3818969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818969).length < 2 ^ (prefixWord ++ tailWord_3818969).sum := by decide
  have hdescent : baseEnd_3818969 < baseStart_3818969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819020 : List Nat := [2, 2, 1, 2, 5, 1, 3, 2, 5]
def baseStart_3819020 : Nat := 118140960795 + 3819020 * 2 ^ 59
def prefixEnd_3819020 : Nat := 4983230072969 + 3 ^ 40 * 3819020 * 2
def baseEnd_3819020 : Nat := 217888098792639255598517

theorem tailTrace_3819020 : CollatzResearch.WordTrace tailWord_3819020 prefixEnd_3819020 217888098792639255598517 := by
  unfold tailWord_3819020
  simp only [CollatzResearch.WordTrace]
  refine ⟨69645551312175125766947257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92860735082900167689263009 69645551312175125766947257)
  ·
    refine ⟨52234163484131344325210443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69645551312175125766947257 52234163484131344325210443)
    ·
      refine ⟨78351245226197016487815665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52234163484131344325210443 78351245226197016487815665)
      ·
        refine ⟨58763433919647762365861749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78351245226197016487815665 58763433919647762365861749)
        ·
          refine ⟨5509071929966977721799539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58763433919647762365861749 5509071929966977721799539)
          ·
            refine ⟨8263607894950466582699309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5509071929966977721799539 8263607894950466582699309)
            ·
              refine ⟨3098852960606424968512241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8263607894950466582699309 3098852960606424968512241)
              ·
                refine ⟨2324139720454818726384181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3098852960606424968512241 2324139720454818726384181)
                ·
                  refine ⟨217888098792639255598517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2324139720454818726384181 217888098792639255598517)
                  ·
                    rfl

theorem cell23_3819020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 5].length) (baseStart_3819020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819020 prefixEnd_3819020 := by exact prefixLift 3819020
  have htrace : WordTrace (prefixWord ++ tailWord_3819020) baseStart_3819020 baseEnd_3819020 := by
    simpa [prefixWord, tailWord_3819020, baseEnd_3819020] using wordTrace_append hprefix tailTrace_3819020
  have hstable : (prefixWord ++ tailWord_3819020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819020).length < 2 ^ (prefixWord ++ tailWord_3819020).sum := by decide
  have hdescent : baseEnd_3819020 < baseStart_3819020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819036 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_3819036 : Nat := 118140960795 + 3819036 * 2 ^ 59
def prefixEnd_3819036 : Nat := 4983230072969 + 3 ^ 40 * 3819036 * 2
def baseEnd_3819036 : Nat := 1961001104824225237786579

theorem tailTrace_3819036 : CollatzResearch.WordTrace tailWord_3819036 prefixEnd_3819036 1961001104824225237786579 := by
  unfold tailWord_3819036
  simp only [CollatzResearch.WordTrace]
  refine ⟨69645843096146143133238481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92861124128194857510984641 69645843096146143133238481)
  ·
    refine ⟨52234382322109607349928861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69645843096146143133238481 52234382322109607349928861)
    ·
      refine ⟨19587893370791102756223323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52234382322109607349928861 19587893370791102756223323)
      ·
        refine ⟨29381840056186654134334985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19587893370791102756223323 29381840056186654134334985)
        ·
          refine ⟨22036380042139990600751239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29381840056186654134334985 22036380042139990600751239)
          ·
            refine ⟨33054570063209985901126859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22036380042139990600751239 33054570063209985901126859)
            ·
              refine ⟨49581855094814978851690289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33054570063209985901126859 49581855094814978851690289)
              ·
                refine ⟨37186391321111234138767717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49581855094814978851690289 37186391321111234138767717)
                ·
                  refine ⟨6972448372708356401018947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37186391321111234138767717 6972448372708356401018947)
                  ·
                    refine ⟨10458672559062534601528421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6972448372708356401018947 10458672559062534601528421)
                    ·
                      refine ⟨1961001104824225237786579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10458672559062534601528421 1961001104824225237786579)
                      ·
                        rfl

theorem cell23_3819036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_3819036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819036 prefixEnd_3819036 := by exact prefixLift 3819036
  have htrace : WordTrace (prefixWord ++ tailWord_3819036) baseStart_3819036 baseEnd_3819036 := by
    simpa [prefixWord, tailWord_3819036, baseEnd_3819036] using wordTrace_append hprefix tailTrace_3819036
  have hstable : (prefixWord ++ tailWord_3819036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819036).length < 2 ^ (prefixWord ++ tailWord_3819036).sum := by decide
  have hdescent : baseEnd_3819036 < baseStart_3819036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819073 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_3819073 : Nat := 118140960795 + 3819073 * 2 ^ 59
def prefixEnd_3819073 : Nat := 4983230072969 + 3 ^ 40 * 3819073 * 2
def baseEnd_3819073 : Nat := 1961020103608441593023909

theorem tailTrace_3819073 : CollatzResearch.WordTrace tailWord_3819073 prefixEnd_3819073 1961020103608441593023909 := by
  unfold tailWord_3819073
  simp only [CollatzResearch.WordTrace]
  refine ⟨139293035693158241585573873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92862023795438827723715915 139293035693158241585573873)
  ·
    refine ⟨104469776769868681189180405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139293035693158241585573873 104469776769868681189180405)
    ·
      refine ⟨9794041572175188861485663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104469776769868681189180405 9794041572175188861485663)
      ·
        refine ⟨14691062358262783292228495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9794041572175188861485663 14691062358262783292228495)
        ·
          refine ⟨22036593537394174938342743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14691062358262783292228495 22036593537394174938342743)
          ·
            refine ⟨33054890306091262407514115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22036593537394174938342743 33054890306091262407514115)
            ·
              refine ⟨49582335459136893611271173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33054890306091262407514115 49582335459136893611271173)
              ·
                refine ⟨9296687898588167552113345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49582335459136893611271173 9296687898588167552113345)
                ·
                  refine ⟨6972515923941125664085009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9296687898588167552113345 6972515923941125664085009)
                  ·
                    refine ⟨5229386942955844248063757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6972515923941125664085009 5229386942955844248063757)
                    ·
                      refine ⟨1961020103608441593023909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5229386942955844248063757 1961020103608441593023909)
                      ·
                        rfl

theorem cell23_3819073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_3819073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819073 prefixEnd_3819073 := by exact prefixLift 3819073
  have htrace : WordTrace (prefixWord ++ tailWord_3819073) baseStart_3819073 baseEnd_3819073 := by
    simpa [prefixWord, tailWord_3819073, baseEnd_3819073] using wordTrace_append hprefix tailTrace_3819073
  have hstable : (prefixWord ++ tailWord_3819073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819073).length < 2 ^ (prefixWord ++ tailWord_3819073).sum := by decide
  have hdescent : baseEnd_3819073 < baseStart_3819073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819086 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3]
def baseStart_3819086 : Nat := 118140960795 + 3819086 * 2 ^ 59
def prefixEnd_3819086 : Nat := 4983230072969 + 3 ^ 40 * 3819086 * 2
def baseEnd_3819086 : Nat := 1961026778856950042161349

theorem tailTrace_3819086 : CollatzResearch.WordTrace tailWord_3819086 prefixEnd_3819086 1961026778856950042161349 := by
  unfold tailWord_3819086
  simp only [CollatzResearch.WordTrace]
  refine ⟨17411688730263893100724639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92862339894740763203864741 17411688730263893100724639)
  ·
    refine ⟨26117533095395839651086959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17411688730263893100724639 26117533095395839651086959)
    ·
      refine ⟨39176299643093759476630439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26117533095395839651086959 39176299643093759476630439)
      ·
        refine ⟨58764449464640639214945659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39176299643093759476630439 58764449464640639214945659)
        ·
          refine ⟨88146674196960958822418489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58764449464640639214945659 88146674196960958822418489)
          ·
            refine ⟨66110005647720719116813867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88146674196960958822418489 66110005647720719116813867)
            ·
              refine ⟨99165008471581078675220801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66110005647720719116813867 99165008471581078675220801)
              ·
                refine ⟨74373756353685809006415601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99165008471581078675220801 74373756353685809006415601)
                ·
                  refine ⟨55780317265264356754811701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74373756353685809006415601 55780317265264356754811701)
                  ·
                    refine ⟨5229404743618533445763597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55780317265264356754811701 5229404743618533445763597)
                    ·
                      refine ⟨1961026778856950042161349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5229404743618533445763597 1961026778856950042161349)
                      ·
                        rfl

theorem cell23_3819086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_3819086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819086 prefixEnd_3819086 := by exact prefixLift 3819086
  have htrace : WordTrace (prefixWord ++ tailWord_3819086) baseStart_3819086 baseEnd_3819086 := by
    simpa [prefixWord, tailWord_3819086, baseEnd_3819086] using wordTrace_append hprefix tailTrace_3819086
  have hstable : (prefixWord ++ tailWord_3819086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819086).length < 2 ^ (prefixWord ++ tailWord_3819086).sum := by decide
  have hdescent : baseEnd_3819086 < baseStart_3819086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819137 : List Nat := [1, 2, 4, 2, 1, 2, 2, 4, 1, 1, 3]
def baseStart_3819137 : Nat := 118140960795 + 3819137 * 2 ^ 59
def prefixEnd_3819137 : Nat := 4983230072969 + 3 ^ 40 * 3819137 * 2
def baseEnd_3819137 : Nat := 1961052966370329342623615

theorem tailTrace_3819137 : CollatzResearch.WordTrace tailWord_3819137 prefixEnd_3819137 1961052966370329342623615 := by
  unfold tailWord_3819137
  simp only [CollatzResearch.WordTrace]
  refine ⟨139295369964926380515903665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92863579976617587010602443 139295369964926380515903665)
  ·
    refine ⟨104471527473694785386927749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139295369964926380515903665 104471527473694785386927749)
    ·
      refine ⟨19588411401317772260048953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104471527473694785386927749 19588411401317772260048953)
      ·
        refine ⟨14691308550988329195036715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19588411401317772260048953 14691308550988329195036715)
        ·
          refine ⟨22036962826482493792555073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14691308550988329195036715 22036962826482493792555073)
          ·
            refine ⟨16527722119861870344416305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22036962826482493792555073 16527722119861870344416305)
            ·
              refine ⟨12395791589896402758312229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16527722119861870344416305 12395791589896402758312229)
              ·
                refine ⟨2324210923105575517183543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12395791589896402758312229 2324210923105575517183543)
                ·
                  refine ⟨3486316384658363275775315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324210923105575517183543 3486316384658363275775315)
                  ·
                    refine ⟨5229474576987544913662973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3486316384658363275775315 5229474576987544913662973)
                    ·
                      refine ⟨1961052966370329342623615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5229474576987544913662973 1961052966370329342623615)
                      ·
                        rfl

theorem cell23_3819137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_3819137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819137 prefixEnd_3819137 := by exact prefixLift 3819137
  have htrace : WordTrace (prefixWord ++ tailWord_3819137) baseStart_3819137 baseEnd_3819137 := by
    simpa [prefixWord, tailWord_3819137, baseEnd_3819137] using wordTrace_append hprefix tailTrace_3819137
  have hstable : (prefixWord ++ tailWord_3819137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819137).length < 2 ^ (prefixWord ++ tailWord_3819137).sum := by decide
  have hdescent : baseEnd_3819137 < baseStart_3819137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819160 : List Nat := [2, 1, 2, 4, 1, 3, 2, 2, 1, 1, 4]
def baseStart_3819160 : Nat := 118140960795 + 3819160 * 2 ^ 59
def prefixEnd_3819160 : Nat := 4983230072969 + 3 ^ 40 * 3819160 * 2
def baseEnd_3819160 : Nat := 1961064776425382752636009

theorem tailTrace_3819160 : CollatzResearch.WordTrace tailWord_3819160 prefixEnd_3819160 1961064776425382752636009 := by
  unfold tailWord_3819160
  simp only [CollatzResearch.WordTrace]
  refine ⟨69648104421921527721995467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92864139229228703629327289 69648104421921527721995467)
  ·
    refine ⟨104472156632882291582993201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69648104421921527721995467 104472156632882291582993201)
    ·
      refine ⟨78354117474661718687244901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104472156632882291582993201 78354117474661718687244901)
      ·
        refine ⟨14691397026499072253858419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78354117474661718687244901 14691397026499072253858419)
        ·
          refine ⟨22037095539748608380787629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14691397026499072253858419 22037095539748608380787629)
          ·
            refine ⟨8263910827405728142795361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22037095539748608380787629 8263910827405728142795361)
            ·
              refine ⟨6197933120554296107096521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8263910827405728142795361 6197933120554296107096521)
              ·
                refine ⟨4648449840415722080322391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6197933120554296107096521 4648449840415722080322391)
                ·
                  refine ⟨6972674760623583120483587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4648449840415722080322391 6972674760623583120483587)
                  ·
                    refine ⟨10459012140935374680725381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6972674760623583120483587 10459012140935374680725381)
                    ·
                      refine ⟨1961064776425382752636009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10459012140935374680725381 1961064776425382752636009)
                      ·
                        rfl

theorem cell23_3819160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_3819160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819160 prefixEnd_3819160 := by exact prefixLift 3819160
  have htrace : WordTrace (prefixWord ++ tailWord_3819160) baseStart_3819160 baseEnd_3819160 := by
    simpa [prefixWord, tailWord_3819160, baseEnd_3819160] using wordTrace_append hprefix tailTrace_3819160
  have hstable : (prefixWord ++ tailWord_3819160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819160).length < 2 ^ (prefixWord ++ tailWord_3819160).sum := by decide
  have hdescent : baseEnd_3819160 < baseStart_3819160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819190 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3819190 : Nat := 118140960795 + 3819190 * 2 ^ 59
def prefixEnd_3819190 : Nat := 4983230072969 + 3 ^ 40 * 3819190 * 2
def baseEnd_3819190 : Nat := 1961080180845017635260871

theorem tailTrace_3819190 : CollatzResearch.WordTrace tailWord_3819190 prefixEnd_3819190 1961080180845017635260871 := by
  unfold tailWord_3819190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8706081439608398160473939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92864868689156247045055349 8706081439608398160473939)
  ·
    refine ⟨13059122159412597240710909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8706081439608398160473939 13059122159412597240710909)
    ·
      refine ⟨4897170809779723965266591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13059122159412597240710909 4897170809779723965266591)
      ·
        refine ⟨7345756214669585947899887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4897170809779723965266591 7345756214669585947899887)
        ·
          refine ⟨11018634322004378921849831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7345756214669585947899887 11018634322004378921849831)
          ·
            refine ⟨16527951483006568382774747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11018634322004378921849831 16527951483006568382774747)
            ·
              refine ⟨24791927224509852574162121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16527951483006568382774747 24791927224509852574162121)
              ·
                refine ⟨18593945418382389430621591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24791927224509852574162121 18593945418382389430621591)
                ·
                  refine ⟨27890918127573584145932387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18593945418382389430621591 27890918127573584145932387)
                  ·
                    refine ⟨41836377191360376218898581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27890918127573584145932387 41836377191360376218898581)
                    ·
                      refine ⟨1961080180845017635260871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41836377191360376218898581 1961080180845017635260871)
                      ·
                        rfl

theorem cell23_3819190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3819190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819190 prefixEnd_3819190 := by exact prefixLift 3819190
  have htrace : WordTrace (prefixWord ++ tailWord_3819190) baseStart_3819190 baseEnd_3819190 := by
    simpa [prefixWord, tailWord_3819190, baseEnd_3819190] using wordTrace_append hprefix tailTrace_3819190
  have hstable : (prefixWord ++ tailWord_3819190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819190).length < 2 ^ (prefixWord ++ tailWord_3819190).sum := by decide
  have hdescent : baseEnd_3819190 < baseStart_3819190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819216 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 4]
def baseStart_3819216 : Nat := 118140960795 + 3819216 * 2 ^ 59
def prefixEnd_3819216 : Nat := 4983230072969 + 3 ^ 40 * 3819216 * 2
def baseEnd_3819216 : Nat := 1961093531342034533535751

theorem tailTrace_3819216 : CollatzResearch.WordTrace tailWord_3819216 prefixEnd_3819216 1961093531342034533535751 := by
  unfold tailWord_3819216
  simp only [CollatzResearch.WordTrace]
  refine ⟨69649125665820088504014751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92865500887760118005353001 69649125665820088504014751)
  ·
    refine ⟨104473688498730132756022127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69649125665820088504014751 104473688498730132756022127)
    ·
      refine ⟨156710532748095199134033191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104473688498730132756022127 156710532748095199134033191)
      ·
        refine ⟨235065799122142798701049787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156710532748095199134033191 235065799122142798701049787)
        ·
          refine ⟨352598698683214198051574681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235065799122142798701049787 352598698683214198051574681)
          ·
            refine ⟨264449024012410648538681011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352598698683214198051574681 264449024012410648538681011)
            ·
              refine ⟨396673536018615972808021517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264449024012410648538681011 396673536018615972808021517)
              ·
                refine ⟨148752576006980989803008069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 396673536018615972808021517 148752576006980989803008069)
                ·
                  refine ⟨27891108001308935588064013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148752576006980989803008069 27891108001308935588064013)
                  ·
                    refine ⟨10459165500490850845524005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27891108001308935588064013 10459165500490850845524005)
                    ·
                      refine ⟨1961093531342034533535751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10459165500490850845524005 1961093531342034533535751)
                      ·
                        rfl

theorem cell23_3819216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_3819216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819216 prefixEnd_3819216 := by exact prefixLift 3819216
  have htrace : WordTrace (prefixWord ++ tailWord_3819216) baseStart_3819216 baseEnd_3819216 := by
    simpa [prefixWord, tailWord_3819216, baseEnd_3819216] using wordTrace_append hprefix tailTrace_3819216
  have hstable : (prefixWord ++ tailWord_3819216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819216).length < 2 ^ (prefixWord ++ tailWord_3819216).sum := by decide
  have hdescent : baseEnd_3819216 < baseStart_3819216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819250 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 3, 4, 2]
def baseStart_3819250 : Nat := 118140960795 + 3819250 * 2 ^ 59
def prefixEnd_3819250 : Nat := 4983230072969 + 3 ^ 40 * 3819250 * 2
def baseEnd_3819250 : Nat := 1961110989684287400510595

theorem tailTrace_3819250 : CollatzResearch.WordTrace tailWord_3819250 prefixEnd_3819250 1961110989684287400510595 := by
  unfold tailWord_3819250
  simp only [CollatzResearch.WordTrace]
  refine ⟨34824872853379250203691801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92866327609011333876511469 34824872853379250203691801)
  ·
    refine ⟨26118654640034437652768851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34824872853379250203691801 26118654640034437652768851)
    ·
      refine ⟨39177981960051656479153277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26118654640034437652768851 39177981960051656479153277)
      ·
        refine ⟨14691743235019371179682479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39177981960051656479153277 14691743235019371179682479)
        ·
          refine ⟨22037614852529056769523719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14691743235019371179682479 22037614852529056769523719)
          ·
            refine ⟨33056422278793585154285579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22037614852529056769523719 33056422278793585154285579)
            ·
              refine ⟨49584633418190377731428369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33056422278793585154285579 49584633418190377731428369)
              ·
                refine ⟨37188475063642783298571277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49584633418190377731428369 37188475063642783298571277)
                ·
                  refine ⟨13945678148866043736964229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37188475063642783298571277 13945678148866043736964229)
                  ·
                    refine ⟨2614814652912383200680793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13945678148866043736964229 2614814652912383200680793)
                    ·
                      refine ⟨1961110989684287400510595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2614814652912383200680793 1961110989684287400510595)
                      ·
                        rfl

theorem cell23_3819250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_3819250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819250 prefixEnd_3819250 := by exact prefixLift 3819250
  have htrace : WordTrace (prefixWord ++ tailWord_3819250) baseStart_3819250 baseEnd_3819250 := by
    simpa [prefixWord, tailWord_3819250, baseEnd_3819250] using wordTrace_append hprefix tailTrace_3819250
  have hstable : (prefixWord ++ tailWord_3819250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819250).length < 2 ^ (prefixWord ++ tailWord_3819250).sum := by decide
  have hdescent : baseEnd_3819250 < baseStart_3819250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819267 : List Nat := [1, 1, 1, 3, 2, 2, 4, 3, 2, 2, 2]
def baseStart_3819267 : Nat := 118140960795 + 3819267 * 2 ^ 59
def prefixEnd_3819267 : Nat := 4983230072969 + 3 ^ 40 * 3819267 * 2
def baseEnd_3819267 : Nat := 1961119718855413833998017

theorem tailTrace_3819267 : CollatzResearch.WordTrace tailWord_3819267 prefixEnd_3819267 1961119718855413833998017 := by
  unfold tailWord_3819267
  simp only [CollatzResearch.WordTrace]
  refine ⟨139300111454455412718136055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92866740969636941812090703 139300111454455412718136055)
  ·
    refine ⟨208950167181683119077204083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139300111454455412718136055 208950167181683119077204083)
    ·
      refine ⟨313425250772524678615806125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208950167181683119077204083 313425250772524678615806125)
      ·
        refine ⟨117534469039696754480927297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313425250772524678615806125 117534469039696754480927297)
        ·
          refine ⟨88150851779772565860695473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117534469039696754480927297 88150851779772565860695473)
          ·
            refine ⟨66113138834829424395521605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88150851779772565860695473 66113138834829424395521605)
            ·
              refine ⟨12396213531530517074160301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66113138834829424395521605 12396213531530517074160301)
              ·
                refine ⟨4648580074323943902810113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12396213531530517074160301 4648580074323943902810113)
                ·
                  refine ⟨3486435055742957927107585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4648580074323943902810113 3486435055742957927107585)
                  ·
                    refine ⟨2614826291807218445330689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3486435055742957927107585 2614826291807218445330689)
                    ·
                      refine ⟨1961119718855413833998017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2614826291807218445330689 1961119718855413833998017)
                      ·
                        rfl

theorem cell23_3819267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 2, 2].length) (baseStart_3819267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819267 prefixEnd_3819267 := by exact prefixLift 3819267
  have htrace : WordTrace (prefixWord ++ tailWord_3819267) baseStart_3819267 baseEnd_3819267 := by
    simpa [prefixWord, tailWord_3819267, baseEnd_3819267] using wordTrace_append hprefix tailTrace_3819267
  have hstable : (prefixWord ++ tailWord_3819267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819267).length < 2 ^ (prefixWord ++ tailWord_3819267).sum := by decide
  have hdescent : baseEnd_3819267 < baseStart_3819267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819290 : List Nat := [3, 1, 1, 3, 2, 2, 1, 5, 5]
def baseStart_3819290 : Nat := 118140960795 + 3819290 * 2 ^ 59
def prefixEnd_3819290 : Nat := 4983230072969 + 3 ^ 40 * 3819290 * 2
def baseEnd_3819290 : Nat := 217903503212274138223379

theorem tailTrace_3819290 : CollatzResearch.WordTrace tailWord_3819290 prefixEnd_3819290 217903503212274138223379 := by
  unfold tailWord_3819290
  simp only [CollatzResearch.WordTrace]
  refine ⟨34825237583343021911555831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92867300222248058430815549 34825237583343021911555831)
  ·
    refine ⟨52237856375014532867333747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34825237583343021911555831 52237856375014532867333747)
    ·
      refine ⟨78356784562521799301000621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52237856375014532867333747 78356784562521799301000621)
      ·
        refine ⟨29383794210945674737875233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78356784562521799301000621 29383794210945674737875233)
        ·
          refine ⟨22037845658209256053406425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29383794210945674737875233 22037845658209256053406425)
          ·
            refine ⟨16528384243656942040054819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22037845658209256053406425 16528384243656942040054819)
            ·
              refine ⟨24792576365485413060082229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16528384243656942040054819 24792576365485413060082229)
              ·
                refine ⟨2324304034264257474382709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24792576365485413060082229 2324304034264257474382709)
                ·
                  refine ⟨217903503212274138223379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2324304034264257474382709 217903503212274138223379)
                  ·
                    rfl

theorem cell23_3819290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 5].length) (baseStart_3819290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819290 prefixEnd_3819290 := by exact prefixLift 3819290
  have htrace : WordTrace (prefixWord ++ tailWord_3819290) baseStart_3819290 baseEnd_3819290 := by
    simpa [prefixWord, tailWord_3819290, baseEnd_3819290] using wordTrace_append hprefix tailTrace_3819290
  have hstable : (prefixWord ++ tailWord_3819290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819290).length < 2 ^ (prefixWord ++ tailWord_3819290).sum := by decide
  have hdescent : baseEnd_3819290 < baseStart_3819290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819300 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 2, 3, 3]
def baseStart_3819300 : Nat := 118140960795 + 3819300 * 2 ^ 59
def prefixEnd_3819300 : Nat := 4983230072969 + 3 ^ 40 * 3819300 * 2
def baseEnd_3819300 : Nat := 1961136663717012204885365

theorem tailTrace_3819300 : CollatzResearch.WordTrace tailWord_3819300 prefixEnd_3819300 1961136663717012204885365 := by
  unfold tailWord_3819300
  simp only [CollatzResearch.WordTrace]
  refine ⟨69650657531667929677043677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92867543375557239569391569 69650657531667929677043677)
  ·
    refine ⟨26118996574375473628891379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69650657531667929677043677 26118996574375473628891379)
    ·
      refine ⟨39178494861563210443337069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26118996574375473628891379 39178494861563210443337069)
      ·
        refine ⟨14691935573086203916251401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39178494861563210443337069 14691935573086203916251401)
        ·
          refine ⟨11018951679814652937188551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14691935573086203916251401 11018951679814652937188551)
          ·
            refine ⟨16528427519721979405782827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11018951679814652937188551 16528427519721979405782827)
            ·
              refine ⟨24792641279582969108674241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16528427519721979405782827 24792641279582969108674241)
              ·
                refine ⟨18594480959687226831505681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24792641279582969108674241 18594480959687226831505681)
                ·
                  refine ⟨13945860719765420123629261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18594480959687226831505681 13945860719765420123629261)
                  ·
                    refine ⟨5229697769912032546360973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13945860719765420123629261 5229697769912032546360973)
                    ·
                      refine ⟨1961136663717012204885365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5229697769912032546360973 1961136663717012204885365)
                      ·
                        rfl

theorem cell23_3819300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_3819300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819300 prefixEnd_3819300 := by exact prefixLift 3819300
  have htrace : WordTrace (prefixWord ++ tailWord_3819300) baseStart_3819300 baseEnd_3819300 := by
    simpa [prefixWord, tailWord_3819300, baseEnd_3819300] using wordTrace_append hprefix tailTrace_3819300
  have hstable : (prefixWord ++ tailWord_3819300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819300).length < 2 ^ (prefixWord ++ tailWord_3819300).sum := by decide
  have hdescent : baseEnd_3819300 < baseStart_3819300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819318 : List Nat := [5, 1, 2, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_3819318 : Nat := 118140960795 + 3819318 * 2 ^ 59
def prefixEnd_3819318 : Nat := 4983230072969 + 3 ^ 40 * 3819318 * 2
def baseEnd_3819318 : Nat := 1961145906368793134460283

theorem tailTrace_3819318 : CollatzResearch.WordTrace tailWord_3819318 prefixEnd_3819318 1961145906368793134460283 := by
  unfold tailWord_3819318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8706373223579415526765163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92867981051513765618828405 8706373223579415526765163)
  ·
    refine ⟨13059559835369123290147745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8706373223579415526765163 13059559835369123290147745)
    ·
      refine ⟨9794669876526842467610809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13059559835369123290147745 9794669876526842467610809)
      ·
        refine ⟨7346002407395131850708107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9794669876526842467610809 7346002407395131850708107)
        ·
          refine ⟨11019003611092697776062161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7346002407395131850708107 11019003611092697776062161)
          ·
            refine ⟨8264252708319523332046621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11019003611092697776062161 8264252708319523332046621)
            ·
              refine ⟨3099094765619821249517483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8264252708319523332046621 3099094765619821249517483)
              ·
                refine ⟨4648642148429731874276225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3099094765619821249517483 4648642148429731874276225)
                ·
                  refine ⟨3486481611322298905707169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4648642148429731874276225 3486481611322298905707169)
                  ·
                    refine ⟨2614861208491724179280377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3486481611322298905707169 2614861208491724179280377)
                    ·
                      refine ⟨1961145906368793134460283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2614861208491724179280377 1961145906368793134460283)
                      ·
                        rfl

theorem cell23_3819318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_3819318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819318 prefixEnd_3819318 := by exact prefixLift 3819318
  have htrace : WordTrace (prefixWord ++ tailWord_3819318) baseStart_3819318 baseEnd_3819318 := by
    simpa [prefixWord, tailWord_3819318, baseEnd_3819318] using wordTrace_append hprefix tailTrace_3819318
  have hstable : (prefixWord ++ tailWord_3819318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819318).length < 2 ^ (prefixWord ++ tailWord_3819318).sum := by decide
  have hdescent : baseEnd_3819318 < baseStart_3819318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819360 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 3]
def baseStart_3819360 : Nat := 118140960795 + 3819360 * 2 ^ 59
def prefixEnd_3819360 : Nat := 4983230072969 + 3 ^ 40 * 3819360 * 2
def baseEnd_3819360 : Nat := 1961167472556281970135089

theorem tailTrace_3819360 : CollatzResearch.WordTrace tailWord_3819360 prefixEnd_3819360 1961167472556281970135089 := by
  unfold tailWord_3819360
  simp only [CollatzResearch.WordTrace]
  refine ⟨69651751721559244800635767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92869002295412326400847689 69651751721559244800635767)
  ·
    refine ⟨104477627582338867200953651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69651751721559244800635767 104477627582338867200953651)
    ·
      refine ⟨156716441373508300801430477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104477627582338867200953651 156716441373508300801430477)
      ·
        refine ⟨58768665515065612800536429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156716441373508300801430477 58768665515065612800536429)
        ·
          refine ⟨22038249568149604800201161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58768665515065612800536429 22038249568149604800201161)
          ·
            refine ⟨16528687176112203600150871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22038249568149604800201161 16528687176112203600150871)
            ·
              refine ⟨24793030764168305400226307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16528687176112203600150871 24793030764168305400226307)
              ·
                refine ⟨37189546146252458100339461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24793030764168305400226307 37189546146252458100339461)
                ·
                  refine ⟨6973039902422335893813649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37189546146252458100339461 6973039902422335893813649)
                  ·
                    refine ⟨5229779926816751920360237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6973039902422335893813649 5229779926816751920360237)
                    ·
                      refine ⟨1961167472556281970135089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5229779926816751920360237 1961167472556281970135089)
                      ·
                        rfl

theorem cell23_3819360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_3819360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819360 prefixEnd_3819360 := by exact prefixLift 3819360
  have htrace : WordTrace (prefixWord ++ tailWord_3819360) baseStart_3819360 baseEnd_3819360 := by
    simpa [prefixWord, tailWord_3819360, baseEnd_3819360] using wordTrace_append hprefix tailTrace_3819360
  have hstable : (prefixWord ++ tailWord_3819360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819360).length < 2 ^ (prefixWord ++ tailWord_3819360).sum := by decide
  have hdescent : baseEnd_3819360 < baseStart_3819360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819417 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 2, 3, 2]
def baseStart_3819417 : Nat := 118140960795 + 3819417 * 2 ^ 59
def prefixEnd_3819417 : Nat := 4983230072969 + 3 ^ 40 * 3819417 * 2
def baseEnd_3819417 : Nat := 1961196740953588247122327

theorem tailTrace_3819417 : CollatzResearch.WordTrace tailWord_3819417 prefixEnd_3819417 1961196740953588247122327 := by
  unfold tailWord_3819417
  simp only [CollatzResearch.WordTrace]
  refine ⟨139305582403911988336096505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92870388269274658890731003 139305582403911988336096505)
  ·
    refine ⟨104479186802933991252072379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139305582403911988336096505 104479186802933991252072379)
    ·
      refine ⟨156718780204400986878108569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104479186802933991252072379 156718780204400986878108569)
      ·
        refine ⟨117539085153300740158581427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156718780204400986878108569 117539085153300740158581427)
        ·
          refine ⟨176308627729951110237872141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117539085153300740158581427 176308627729951110237872141)
          ·
            refine ⟨66115735398731666339202053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176308627729951110237872141 66115735398731666339202053)
            ·
              refine ⟨12396700387262187438600385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66115735398731666339202053 12396700387262187438600385)
              ·
                refine ⟨9297525290446640578950289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12396700387262187438600385 9297525290446640578950289)
                ·
                  refine ⟨6973143967834980434212717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9297525290446640578950289 6973143967834980434212717)
                  ·
                    refine ⟨2614928987938117662829769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6973143967834980434212717 2614928987938117662829769)
                    ·
                      refine ⟨1961196740953588247122327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2614928987938117662829769 1961196740953588247122327)
                      ·
                        rfl

theorem cell23_3819417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 3, 2].length) (baseStart_3819417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819417 prefixEnd_3819417 := by exact prefixLift 3819417
  have htrace : WordTrace (prefixWord ++ tailWord_3819417) baseStart_3819417 baseEnd_3819417 := by
    simpa [prefixWord, tailWord_3819417, baseEnd_3819417] using wordTrace_append hprefix tailTrace_3819417
  have hstable : (prefixWord ++ tailWord_3819417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819417).length < 2 ^ (prefixWord ++ tailWord_3819417).sum := by decide
  have hdescent : baseEnd_3819417 < baseStart_3819417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819464 : List Nat := [2, 1, 3, 1, 4, 1, 4, 1, 1, 1, 4]
def baseStart_3819464 : Nat := 118140960795 + 3819464 * 2 ^ 59
def prefixEnd_3819464 : Nat := 4983230072969 + 3 ^ 40 * 3819464 * 2
def baseEnd_3819464 : Nat := 1961220874544349563234611

theorem tailTrace_3819464 : CollatzResearch.WordTrace tailWord_3819464 prefixEnd_3819464 1961220874544349563234611 := by
  unfold tailWord_3819464
  simp only [CollatzResearch.WordTrace]
  refine ⟨69653648317370857681528723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92871531089827810242038297 69653648317370857681528723)
  ·
    refine ⟨104480472476056286522293085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69653648317370857681528723 104480472476056286522293085)
    ·
      refine ⟨39180177178521107445859907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104480472476056286522293085 39180177178521107445859907)
      ·
        refine ⟨58770265767781661168789861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39180177178521107445859907 58770265767781661168789861)
        ·
          refine ⟨11019424831459061469148099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58770265767781661168789861 11019424831459061469148099)
          ·
            refine ⟨16529137247188592203722149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11019424831459061469148099 16529137247188592203722149)
            ·
              refine ⟨3099213233847861038197903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16529137247188592203722149 3099213233847861038197903)
              ·
                refine ⟨4648819850771791557296855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3099213233847861038197903 4648819850771791557296855)
                ·
                  refine ⟨6973229776157687335945283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4648819850771791557296855 6973229776157687335945283)
                  ·
                    refine ⟨10459844664236531003917925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6973229776157687335945283 10459844664236531003917925)
                    ·
                      refine ⟨1961220874544349563234611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10459844664236531003917925 1961220874544349563234611)
                      ·
                        rfl

theorem cell23_3819464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_3819464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819464 prefixEnd_3819464 := by exact prefixLift 3819464
  have htrace : WordTrace (prefixWord ++ tailWord_3819464) baseStart_3819464 baseEnd_3819464 := by
    simpa [prefixWord, tailWord_3819464, baseEnd_3819464] using wordTrace_append hprefix tailTrace_3819464
  have hstable : (prefixWord ++ tailWord_3819464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819464).length < 2 ^ (prefixWord ++ tailWord_3819464).sum := by decide
  have hdescent : baseEnd_3819464 < baseStart_3819464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819467 : List Nat := [1, 1, 1, 1, 3, 4, 3, 3, 1, 2, 3]
def baseStart_3819467 : Nat := 118140960795 + 3819467 * 2 ^ 59
def prefixEnd_3819467 : Nat := 4983230072969 + 3 ^ 40 * 3819467 * 2
def baseEnd_3819467 : Nat := 1961222414986313051497097

theorem tailTrace_3819467 : CollatzResearch.WordTrace tailWord_3819467 prefixEnd_3819467 1961222414986313051497097 := by
  unfold tailWord_3819467
  simp only [CollatzResearch.WordTrace]
  refine ⟨139307406053730846875416655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92871604035820564583611103 139307406053730846875416655)
  ·
    refine ⟨208961109080596270313124983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139307406053730846875416655 208961109080596270313124983)
    ·
      refine ⟨313441663620894405469687475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208961109080596270313124983 313441663620894405469687475)
      ·
        refine ⟨470162495431341608204531213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313441663620894405469687475 470162495431341608204531213)
        ·
          refine ⟨176310935786753103076699205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 470162495431341608204531213 176310935786753103076699205)
          ·
            refine ⟨33058300460016206826881101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176310935786753103076699205 33058300460016206826881101)
            ·
              refine ⟨12396862672506077560080413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33058300460016206826881101 12396862672506077560080413)
              ·
                refine ⟨4648823502189779085030155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12396862672506077560080413 4648823502189779085030155)
                ·
                  refine ⟨6973235253284668627545233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4648823502189779085030155 6973235253284668627545233)
                  ·
                    refine ⟨5229926439963501470658925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6973235253284668627545233 5229926439963501470658925)
                    ·
                      refine ⟨1961222414986313051497097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5229926439963501470658925 1961222414986313051497097)
                      ·
                        rfl

theorem cell23_3819467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 2, 3].length) (baseStart_3819467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819467 prefixEnd_3819467 := by exact prefixLift 3819467
  have htrace : WordTrace (prefixWord ++ tailWord_3819467) baseStart_3819467 baseEnd_3819467 := by
    simpa [prefixWord, tailWord_3819467, baseEnd_3819467] using wordTrace_append hprefix tailTrace_3819467
  have hstable : (prefixWord ++ tailWord_3819467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819467).length < 2 ^ (prefixWord ++ tailWord_3819467).sum := by decide
  have hdescent : baseEnd_3819467 < baseStart_3819467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819474 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 4, 4]
def baseStart_3819474 : Nat := 118140960795 + 3819474 * 2 ^ 59
def prefixEnd_3819474 : Nat := 4983230072969 + 3 ^ 40 * 3819474 * 2
def baseEnd_3819474 : Nat := 653742003116964841369855

theorem tailTrace_3819474 : CollatzResearch.WordTrace tailWord_3819474 prefixEnd_3819474 653742003116964841369855 := by
  unfold tailWord_3819474
  simp only [CollatzResearch.WordTrace]
  refine ⟨34826915341176371767730369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92871774243136991380614317 34826915341176371767730369)
  ·
    refine ⟨26120186505882278825797777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34826915341176371767730369 26120186505882278825797777)
    ·
      refine ⟨19590139879411709119348333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26120186505882278825797777 19590139879411709119348333)
      ·
        refine ⟨7346302454779390919755625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19590139879411709119348333 7346302454779390919755625)
        ·
          refine ⟨5509726841084543189816719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7346302454779390919755625 5509726841084543189816719)
          ·
            refine ⟨8264590261626814784725079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5509726841084543189816719 8264590261626814784725079)
            ·
              refine ⟨12396885392440222177087619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8264590261626814784725079 12396885392440222177087619)
              ·
                refine ⟨18595328088660333265631429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12396885392440222177087619 18595328088660333265631429)
                ·
                  refine ⟨3486624016623812487305893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18595328088660333265631429 3486624016623812487305893)
                  ·
                    refine ⟨653742003116964841369855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3486624016623812487305893 653742003116964841369855)
                    ·
                      rfl

theorem cell23_3819474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_3819474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819474 prefixEnd_3819474 := by exact prefixLift 3819474
  have htrace : WordTrace (prefixWord ++ tailWord_3819474) baseStart_3819474 baseEnd_3819474 := by
    simpa [prefixWord, tailWord_3819474, baseEnd_3819474] using wordTrace_append hprefix tailTrace_3819474
  have hstable : (prefixWord ++ tailWord_3819474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819474).length < 2 ^ (prefixWord ++ tailWord_3819474).sum := by decide
  have hdescent : baseEnd_3819474 < baseStart_3819474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819481 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 3, 2, 2]
def baseStart_3819481 : Nat := 118140960795 + 3819481 * 2 ^ 59
def prefixEnd_3819481 : Nat := 4983230072969 + 3 ^ 40 * 3819481 * 2
def baseEnd_3819481 : Nat := 1961229603715475996722033

theorem tailTrace_3819481 : CollatzResearch.WordTrace tailWord_3819481 prefixEnd_3819481 1961229603715475996722033 := by
  unfold tailWord_3819481
  simp only [CollatzResearch.WordTrace]
  refine ⟨139307916675680127266426297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92871944450453418177617531 139307916675680127266426297)
  ·
    refine ⟨104480937506760095449819723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139307916675680127266426297 104480937506760095449819723)
    ·
      refine ⟨156721406260140143174729585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104480937506760095449819723 156721406260140143174729585)
      ·
        refine ⟨117541054695105107381047189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156721406260140143174729585 117541054695105107381047189)
        ·
          refine ⟨5509736938833051908486587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117541054695105107381047189 5509736938833051908486587)
          ·
            refine ⟨8264605408249577862729881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5509736938833051908486587 8264605408249577862729881)
            ·
              refine ⟨6198454056187183397047411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8264605408249577862729881 6198454056187183397047411)
              ·
                refine ⟨9297681084280775095571117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6198454056187183397047411 9297681084280775095571117)
                ·
                  refine ⟨3486630406605290660839169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9297681084280775095571117 3486630406605290660839169)
                  ·
                    refine ⟨2614972804953967995629377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3486630406605290660839169 2614972804953967995629377)
                    ·
                      refine ⟨1961229603715475996722033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2614972804953967995629377 1961229603715475996722033)
                      ·
                        rfl

theorem cell23_3819481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 2, 2].length) (baseStart_3819481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819481 prefixEnd_3819481 := by exact prefixLift 3819481
  have htrace : WordTrace (prefixWord ++ tailWord_3819481) baseStart_3819481 baseEnd_3819481 := by
    simpa [prefixWord, tailWord_3819481, baseEnd_3819481] using wordTrace_append hprefix tailTrace_3819481
  have hstable : (prefixWord ++ tailWord_3819481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819481).length < 2 ^ (prefixWord ++ tailWord_3819481).sum := by decide
  have hdescent : baseEnd_3819481 < baseStart_3819481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819507 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 3, 3, 2]
def baseStart_3819507 : Nat := 118140960795 + 3819507 * 2 ^ 59
def prefixEnd_3819507 : Nat := 4983230072969 + 3 ^ 40 * 3819507 * 2
def baseEnd_3819507 : Nat := 1961242954212492894996913

theorem tailTrace_3819507 : CollatzResearch.WordTrace tailWord_3819507 prefixEnd_3819507 1961242954212492894996913 := by
  unfold tailWord_3819507
  simp only [CollatzResearch.WordTrace]
  refine ⟨139308864973585933706872775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92872576649057289137915183 139308864973585933706872775)
  ·
    refine ⟨208963297460378900560309163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139308864973585933706872775 208963297460378900560309163)
    ·
      refine ⟨313444946190568350840463745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208963297460378900560309163 313444946190568350840463745)
      ·
        refine ⟨235083709642926263130347809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313444946190568350840463745 235083709642926263130347809)
        ·
          refine ⟨176312782232194697347760857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235083709642926263130347809 176312782232194697347760857)
          ·
            refine ⟨132234586674146023010820643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176312782232194697347760857 132234586674146023010820643)
            ·
              refine ⟨198351880011219034516230965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132234586674146023010820643 198351880011219034516230965)
              ·
                refine ⟨18595488751051784485896653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198351880011219034516230965 18595488751051784485896653)
                ·
                  refine ⟨6973308281644419182211245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18595488751051784485896653 6973308281644419182211245)
                  ·
                    refine ⟨2614990605616657193329217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6973308281644419182211245 2614990605616657193329217)
                    ·
                      refine ⟨1961242954212492894996913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2614990605616657193329217 1961242954212492894996913)
                      ·
                        rfl

theorem cell23_3819507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 3, 2].length) (baseStart_3819507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819507 prefixEnd_3819507 := by exact prefixLift 3819507
  have htrace : WordTrace (prefixWord ++ tailWord_3819507) baseStart_3819507 baseEnd_3819507 := by
    simpa [prefixWord, tailWord_3819507, baseEnd_3819507] using wordTrace_append hprefix tailTrace_3819507
  have hstable : (prefixWord ++ tailWord_3819507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819507).length < 2 ^ (prefixWord ++ tailWord_3819507).sum := by decide
  have hdescent : baseEnd_3819507 < baseStart_3819507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819548 : List Nat := [2, 2, 3, 1, 3, 3, 2, 1, 2, 1, 3]
def baseStart_3819548 : Nat := 118140960795 + 3819548 * 2 ^ 59
def prefixEnd_3819548 : Nat := 4983230072969 + 3 ^ 40 * 3819548 * 2
def baseEnd_3819548 : Nat := 1961264006919327234584225

theorem tailTrace_3819548 : CollatzResearch.WordTrace tailWord_3819548 prefixEnd_3819548 1961264006919327234584225 := by
  unfold tailWord_3819548
  simp only [CollatzResearch.WordTrace]
  refine ⟨69655180183218698854557649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92873573577624931806076865 69655180183218698854557649)
  ·
    refine ⟨52241385137414024140918237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69655180183218698854557649 52241385137414024140918237)
    ·
      refine ⟨19590519426530259052844339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52241385137414024140918237 19590519426530259052844339)
      ·
        refine ⟨29385779139795388579266509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19590519426530259052844339 29385779139795388579266509)
        ·
          refine ⟨11019667177423270717224941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29385779139795388579266509 11019667177423270717224941)
          ·
            refine ⟨4132375191533726518959353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11019667177423270717224941 4132375191533726518959353)
            ·
              refine ⟨3099281393650294889219515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4132375191533726518959353 3099281393650294889219515)
              ·
                refine ⟨4648922090475442333829273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3099281393650294889219515 4648922090475442333829273)
                ·
                  refine ⟨3486691567856581750371955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4648922090475442333829273 3486691567856581750371955)
                  ·
                    refine ⟨5230037351784872625557933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3486691567856581750371955 5230037351784872625557933)
                    ·
                      refine ⟨1961264006919327234584225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5230037351784872625557933 1961264006919327234584225)
                      ·
                        rfl

theorem cell23_3819548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_3819548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819548 prefixEnd_3819548 := by exact prefixLift 3819548
  have htrace : WordTrace (prefixWord ++ tailWord_3819548) baseStart_3819548 baseEnd_3819548 := by
    simpa [prefixWord, tailWord_3819548, baseEnd_3819548] using wordTrace_append hprefix tailTrace_3819548
  have hstable : (prefixWord ++ tailWord_3819548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819548).length < 2 ^ (prefixWord ++ tailWord_3819548).sum := by decide
  have hdescent : baseEnd_3819548 < baseStart_3819548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819554 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 1, 4, 2]
def baseStart_3819554 : Nat := 118140960795 + 3819554 * 2 ^ 59
def prefixEnd_3819554 : Nat := 4983230072969 + 3 ^ 40 * 3819554 * 2
def baseEnd_3819554 : Nat := 1961267087803254211109197

theorem tailTrace_3819554 : CollatzResearch.WordTrace tailWord_3819554 prefixEnd_3819554 1961267087803254211109197 := by
  unfold tailWord_3819554
  simp only [CollatzResearch.WordTrace]
  refine ⟨34827644801103915183458429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92873719469610440489222477 34827644801103915183458429)
  ·
    refine ⟨13060366800413968193796911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34827644801103915183458429 13060366800413968193796911)
    ·
      refine ⟨19590550200620952290695367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13060366800413968193796911 19590550200620952290695367)
      ·
        refine ⟨29385825300931428436043051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19590550200620952290695367 29385825300931428436043051)
        ·
          refine ⟨44078737951397142654064577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29385825300931428436043051 44078737951397142654064577)
          ·
            refine ⟨33059053463547856990548433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44078737951397142654064577 33059053463547856990548433)
            ·
              refine ⟨24794290097660892742911325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33059053463547856990548433 24794290097660892742911325)
              ·
                refine ⟨9297858786622834778591747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24794290097660892742911325 9297858786622834778591747)
                ·
                  refine ⟨13946788179934252167887621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9297858786622834778591747 13946788179934252167887621)
                  ·
                    refine ⟨2615022783737672281478929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13946788179934252167887621 2615022783737672281478929)
                    ·
                      refine ⟨1961267087803254211109197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2615022783737672281478929 1961267087803254211109197)
                      ·
                        rfl

theorem cell23_3819554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_3819554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819554 prefixEnd_3819554 := by exact prefixLift 3819554
  have htrace : WordTrace (prefixWord ++ tailWord_3819554) baseStart_3819554 baseEnd_3819554 := by
    simpa [prefixWord, tailWord_3819554, baseEnd_3819554] using wordTrace_append hprefix tailTrace_3819554
  have hstable : (prefixWord ++ tailWord_3819554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819554).length < 2 ^ (prefixWord ++ tailWord_3819554).sum := by decide
  have hdescent : baseEnd_3819554 < baseStart_3819554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819644 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 2, 4, 2]
def baseStart_3819644 : Nat := 118140960795 + 3819644 * 2 ^ 59
def prefixEnd_3819644 : Nat := 4983230072969 + 3 ^ 40 * 3819644 * 2
def baseEnd_3819644 : Nat := 1961313301062158858983783

theorem tailTrace_3819644 : CollatzResearch.WordTrace tailWord_3819644 prefixEnd_3819644 1961313301062158858983783 := by
  unfold tailWord_3819644
  simp only [CollatzResearch.WordTrace]
  refine ⟨69656930887044803052304993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92875907849393070736406657 69656930887044803052304993)
  ·
    refine ⟨52242698165283602289228745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69656930887044803052304993 52242698165283602289228745)
    ·
      refine ⟨39182023623962701716921559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52242698165283602289228745 39182023623962701716921559)
      ·
        refine ⟨58773035435944052575382339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39182023623962701716921559 58773035435944052575382339)
        ·
          refine ⟨88159553153916078863073509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58773035435944052575382339 88159553153916078863073509)
          ·
            refine ⟨16529916216359264786826283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88159553153916078863073509 16529916216359264786826283)
            ·
              refine ⟨24794874324538897180239425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16529916216359264786826283 24794874324538897180239425)
              ·
                refine ⟨18596155743404172885179569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24794874324538897180239425 18596155743404172885179569)
                ·
                  refine ⟨13947116807553129663884677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18596155743404172885179569 13947116807553129663884677)
                  ·
                    refine ⟨2615084401416211811978377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13947116807553129663884677 2615084401416211811978377)
                    ·
                      refine ⟨1961313301062158858983783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2615084401416211811978377 1961313301062158858983783)
                      ·
                        rfl

theorem cell23_3819644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_3819644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819644 prefixEnd_3819644 := by exact prefixLift 3819644
  have htrace : WordTrace (prefixWord ++ tailWord_3819644) baseStart_3819644 baseEnd_3819644 := by
    simpa [prefixWord, tailWord_3819644, baseEnd_3819644] using wordTrace_append hprefix tailTrace_3819644
  have hstable : (prefixWord ++ tailWord_3819644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819644).length < 2 ^ (prefixWord ++ tailWord_3819644).sum := by decide
  have hdescent : baseEnd_3819644 < baseStart_3819644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819727 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 1, 6]
def baseStart_3819727 : Nat := 118140960795 + 3819727 * 2 ^ 59
def prefixEnd_3819727 : Nat := 4983230072969 + 3 ^ 40 * 3819727 * 2
def baseEnd_3819727 : Nat := 653785306652160678081967

theorem tailTrace_3819727 : CollatzResearch.WordTrace tailWord_3819727 prefixEnd_3819727 653785306652160678081967 := by
  unfold tailWord_3819727
  simp only [CollatzResearch.WordTrace]
  refine ⟨139316889032788911279881435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92877926021859274186587623 139316889032788911279881435)
  ·
    refine ⟨208975333549183366919822153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139316889032788911279881435 208975333549183366919822153)
    ·
      refine ⟨156731500161887525189866615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208975333549183366919822153 156731500161887525189866615)
      ·
        refine ⟨235097250242831287784799923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156731500161887525189866615 235097250242831287784799923)
        ·
          refine ⟨352645875364246931677199885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235097250242831287784799923 352645875364246931677199885)
          ·
            refine ⟨132242203261592599378949957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352645875364246931677199885 132242203261592599378949957)
            ·
              refine ⟨24795413111548612383553117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132242203261592599378949957 24795413111548612383553117)
              ·
                refine ⟨9298279916830729643832419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24795413111548612383553117 9298279916830729643832419)
                ·
                  refine ⟨13947419875246094465748629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9298279916830729643832419 13947419875246094465748629)
                  ·
                    refine ⟨653785306652160678081967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13947419875246094465748629 653785306652160678081967)
                    ·
                      rfl

theorem cell23_3819727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 6].length) (baseStart_3819727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819727 prefixEnd_3819727 := by exact prefixLift 3819727
  have htrace : WordTrace (prefixWord ++ tailWord_3819727) baseStart_3819727 baseEnd_3819727 := by
    simpa [prefixWord, tailWord_3819727, baseEnd_3819727] using wordTrace_append hprefix tailTrace_3819727
  have hstable : (prefixWord ++ tailWord_3819727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819727).length < 2 ^ (prefixWord ++ tailWord_3819727).sum := by decide
  have hdescent : baseEnd_3819727 < baseStart_3819727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819737 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 3, 1, 5]
def baseStart_3819737 : Nat := 118140960795 + 3819737 * 2 ^ 59
def prefixEnd_3819737 : Nat := 4983230072969 + 3 ^ 40 * 3819737 * 2
def baseEnd_3819737 : Nat := 1961361054763026995120855

theorem tailTrace_3819737 : CollatzResearch.WordTrace tailWord_3819737 prefixEnd_3819737 1961361054763026995120855 := by
  unfold tailWord_3819737
  simp only [CollatzResearch.WordTrace]
  refine ⟨139317253762752682987745465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92878169175168455325163643 139317253762752682987745465)
  ·
    refine ⟨104487940322064512240809099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139317253762752682987745465 104487940322064512240809099)
    ·
      refine ⟨156731910483096768361213649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104487940322064512240809099 156731910483096768361213649)
      ·
        refine ⟨117548932862322576270910237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156731910483096768361213649 117548932862322576270910237)
        ·
          refine ⟨44080849823370966101591339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117548932862322576270910237 44080849823370966101591339)
          ·
            refine ⟨66121274735056449152387009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44080849823370966101591339 66121274735056449152387009)
            ·
              refine ⟨49590956051292336864290257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66121274735056449152387009 49590956051292336864290257)
              ·
                refine ⟨37193217038469252648217693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49590956051292336864290257 37193217038469252648217693)
                ·
                  refine ⟨13947456389425969743081635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37193217038469252648217693 13947456389425969743081635)
                  ·
                    refine ⟨20921184584138954614622453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13947456389425969743081635 20921184584138954614622453)
                    ·
                      refine ⟨1961361054763026995120855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20921184584138954614622453 1961361054763026995120855)
                      ·
                        rfl

theorem cell23_3819737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_3819737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819737 prefixEnd_3819737 := by exact prefixLift 3819737
  have htrace : WordTrace (prefixWord ++ tailWord_3819737) baseStart_3819737 baseEnd_3819737 := by
    simpa [prefixWord, tailWord_3819737, baseEnd_3819737] using wordTrace_append hprefix tailTrace_3819737
  have hstable : (prefixWord ++ tailWord_3819737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819737).length < 2 ^ (prefixWord ++ tailWord_3819737).sum := by decide
  have hdescent : baseEnd_3819737 < baseStart_3819737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819757 : List Nat := [1, 5, 1, 2, 14]
def baseStart_3819757 : Nat := 118140960795 + 3819757 * 2 ^ 59
def prefixEnd_3819757 : Nat := 4983230072969 + 3 ^ 40 * 3819757 * 2
def baseEnd_3819757 : Nat := 2690495643862986168547

theorem tailTrace_3819757 : CollatzResearch.WordTrace tailWord_3819757 prefixEnd_3819757 2690495643862986168547 := by
  unfold tailWord_3819757
  simp only [CollatzResearch.WordTrace]
  refine ⟨139317983222680226403473525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92878655481786817602315683 139317983222680226403473525)
  ·
    refine ⟨13061060927126271225325643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139317983222680226403473525 13061060927126271225325643)
    ·
      refine ⟨19591591390689406837988465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13061060927126271225325643 19591591390689406837988465)
      ·
        refine ⟨14693693543017055128491349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19591591390689406837988465 14693693543017055128491349)
        ·
          refine ⟨2690495643862986168547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 14693693543017055128491349 2690495643862986168547)
          ·
            rfl

theorem cell23_3819757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 14].length) (baseStart_3819757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819757 prefixEnd_3819757 := by exact prefixLift 3819757
  have htrace : WordTrace (prefixWord ++ tailWord_3819757) baseStart_3819757 baseEnd_3819757 := by
    simpa [prefixWord, tailWord_3819757, baseEnd_3819757] using wordTrace_append hprefix tailTrace_3819757
  have hstable : (prefixWord ++ tailWord_3819757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819757).length < 2 ^ (prefixWord ++ tailWord_3819757).sum := by decide
  have hdescent : baseEnd_3819757 < baseStart_3819757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819762 : List Nat := [3, 2, 1, 3, 2, 3, 2, 2, 1, 1, 3]
def baseStart_3819762 : Nat := 118140960795 + 3819762 * 2 ^ 59
def prefixEnd_3819762 : Nat := 4983230072969 + 3 ^ 40 * 3819762 * 2
def baseEnd_3819762 : Nat := 1961373891779389397308241

theorem tailTrace_3819762 : CollatzResearch.WordTrace tailWord_3819762 prefixEnd_3819762 1961373891779389397308241 := by
  unfold tailWord_3819762
  simp only [CollatzResearch.WordTrace]
  refine ⟨34829541396915528064351385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92878777058441408171603693 34829541396915528064351385)
  ·
    refine ⟨26122156047686646048263539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34829541396915528064351385 26122156047686646048263539)
    ·
      refine ⟨39183234071529969072395309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26122156047686646048263539 39183234071529969072395309)
      ·
        refine ⟨14693712776823738402148241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39183234071529969072395309 14693712776823738402148241)
        ·
          refine ⟨11020284582617803801611181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14693712776823738402148241 11020284582617803801611181)
          ·
            refine ⟨4132606718481676425604193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11020284582617803801611181 4132606718481676425604193)
            ·
              refine ⟨3099455038861257319203145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4132606718481676425604193 3099455038861257319203145)
              ·
                refine ⟨2324591279145942989402359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3099455038861257319203145 2324591279145942989402359)
                ·
                  refine ⟨3486886918718914484103539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324591279145942989402359 3486886918718914484103539)
                  ·
                    refine ⟨5230330378078371726155309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3486886918718914484103539 5230330378078371726155309)
                    ·
                      refine ⟨1961373891779389397308241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5230330378078371726155309 1961373891779389397308241)
                      ·
                        rfl

theorem cell23_3819762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_3819762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819762 prefixEnd_3819762 := by exact prefixLift 3819762
  have htrace : WordTrace (prefixWord ++ tailWord_3819762) baseStart_3819762 baseEnd_3819762 := by
    simpa [prefixWord, tailWord_3819762, baseEnd_3819762] using wordTrace_append hprefix tailTrace_3819762
  have hstable : (prefixWord ++ tailWord_3819762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819762).length < 2 ^ (prefixWord ++ tailWord_3819762).sum := by decide
  have hdescent : baseEnd_3819762 < baseStart_3819762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819778 : List Nat := [3, 4, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_3819778 : Nat := 118140960795 + 3819778 * 2 ^ 59
def prefixEnd_3819778 : Nat := 4983230072969 + 3 ^ 40 * 3819778 * 2
def baseEnd_3819778 : Nat := 653794035823287111569389

theorem tailTrace_3819778 : CollatzResearch.WordTrace tailWord_3819778 prefixEnd_3819778 653794035823287111569389 := by
  unfold tailWord_3819778
  simp only [CollatzResearch.WordTrace]
  refine ⟨34829687288901036747496997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92879166103736097993325325 34829687288901036747496997)
  ·
    refine ⟨6530566366668944390155687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34829687288901036747496997 6530566366668944390155687)
    ·
      refine ⟨9795849550003416585233531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6530566366668944390155687 9795849550003416585233531)
      ·
        refine ⟨14693774325005124877850297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9795849550003416585233531 14693774325005124877850297)
        ·
          refine ⟨11020330743753843658387723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14693774325005124877850297 11020330743753843658387723)
          ·
            refine ⟨16530496115630765487581585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11020330743753843658387723 16530496115630765487581585)
            ·
              refine ⟨12397872086723074115686189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16530496115630765487581585 12397872086723074115686189)
              ·
                refine ⟨4649202032521152793382321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12397872086723074115686189 4649202032521152793382321)
                ·
                  refine ⟨3486901524390864595036741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4649202032521152793382321 3486901524390864595036741)
                  ·
                    refine ⟨653794035823287111569389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3486901524390864595036741 653794035823287111569389)
                    ·
                      rfl

theorem cell23_3819778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_3819778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819778 prefixEnd_3819778 := by exact prefixLift 3819778
  have htrace : WordTrace (prefixWord ++ tailWord_3819778) baseStart_3819778 baseEnd_3819778 := by
    simpa [prefixWord, tailWord_3819778, baseEnd_3819778] using wordTrace_append hprefix tailTrace_3819778
  have hstable : (prefixWord ++ tailWord_3819778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819778).length < 2 ^ (prefixWord ++ tailWord_3819778).sum := by decide
  have hdescent : baseEnd_3819778 < baseStart_3819778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819787 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 2, 7]
def baseStart_3819787 : Nat := 118140960795 + 3819787 * 2 ^ 59
def prefixEnd_3819787 : Nat := 4983230072969 + 3 ^ 40 * 3819787 * 2
def baseEnd_3819787 : Nat := 653795576265250599831875

theorem tailTrace_3819787 : CollatzResearch.WordTrace tailWord_3819787 prefixEnd_3819787 653795576265250599831875 := by
  unfold tailWord_3819787
  simp only [CollatzResearch.WordTrace]
  refine ⟨139319077412571541527065615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92879384941714361018043743 139319077412571541527065615)
  ·
    refine ⟨208978616118857312290598423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139319077412571541527065615 208978616118857312290598423)
    ·
      refine ⟨313467924178285968435897635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208978616118857312290598423 313467924178285968435897635)
      ·
        refine ⟨470201886267428952653846453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313467924178285968435897635 470201886267428952653846453)
        ·
          refine ⟨44081426837571464311298105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 470201886267428952653846453 44081426837571464311298105)
          ·
            refine ⟨33061070128178598233473579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44081426837571464311298105 33061070128178598233473579)
            ·
              refine ⟨49591605192267897350210369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33061070128178598233473579 49591605192267897350210369)
              ·
                refine ⟨37193703894200923012657777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49591605192267897350210369 37193703894200923012657777)
                ·
                  refine ⟨27895277920650692259493333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37193703894200923012657777 27895277920650692259493333)
                  ·
                    refine ⟨653795576265250599831875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27895277920650692259493333 653795576265250599831875)
                    ·
                      rfl

theorem cell23_3819787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 7].length) (baseStart_3819787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819787 prefixEnd_3819787 := by exact prefixLift 3819787
  have htrace : WordTrace (prefixWord ++ tailWord_3819787) baseStart_3819787 baseEnd_3819787 := by
    simpa [prefixWord, tailWord_3819787, baseEnd_3819787] using wordTrace_append hprefix tailTrace_3819787
  have hstable : (prefixWord ++ tailWord_3819787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819787).length < 2 ^ (prefixWord ++ tailWord_3819787).sum := by decide
  have hdescent : baseEnd_3819787 < baseStart_3819787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819802 : List Nat := [3, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2]
def baseStart_3819802 : Nat := 118140960795 + 3819802 * 2 ^ 59
def prefixEnd_3819802 : Nat := 4983230072969 + 3 ^ 40 * 3819802 * 2
def baseEnd_3819802 : Nat := 1961394431005569240808057

theorem tailTrace_3819802 : CollatzResearch.WordTrace tailWord_3819802 prefixEnd_3819802 1961394431005569240808057 := by
  unfold tailWord_3819802
  simp only [CollatzResearch.WordTrace]
  refine ⟨34829906126879299772215415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92879749671678132725907773 34829906126879299772215415)
  ·
    refine ⟨52244859190318949658323123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34829906126879299772215415 52244859190318949658323123)
    ·
      refine ⟨78367288785478424487484685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52244859190318949658323123 78367288785478424487484685)
      ·
        refine ⟨29387733294554409182806757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78367288785478424487484685 29387733294554409182806757)
        ·
          refine ⟨5510199992728951721776267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29387733294554409182806757 5510199992728951721776267)
          ·
            refine ⟨8265299989093427582664401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5510199992728951721776267 8265299989093427582664401)
            ·
              refine ⟨6198974991820070686998301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8265299989093427582664401 6198974991820070686998301)
              ·
                refine ⟨2324615621932526507624363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6198974991820070686998301 2324615621932526507624363)
                ·
                  refine ⟨3486923432898789761436545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324615621932526507624363 3486923432898789761436545)
                  ·
                    refine ⟨2615192574674092321077409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3486923432898789761436545 2615192574674092321077409)
                    ·
                      refine ⟨1961394431005569240808057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2615192574674092321077409 1961394431005569240808057)
                      ·
                        rfl

theorem cell23_3819802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_3819802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819802 prefixEnd_3819802 := by exact prefixLift 3819802
  have htrace : WordTrace (prefixWord ++ tailWord_3819802) baseStart_3819802 baseEnd_3819802 := by
    simpa [prefixWord, tailWord_3819802, baseEnd_3819802] using wordTrace_append hprefix tailTrace_3819802
  have hstable : (prefixWord ++ tailWord_3819802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819802).length < 2 ^ (prefixWord ++ tailWord_3819802).sum := by decide
  have hdescent : baseEnd_3819802 < baseStart_3819802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819834 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 2, 6]
def baseStart_3819834 : Nat := 118140960795 + 3819834 * 2 ^ 59
def prefixEnd_3819834 : Nat := 4983230072969 + 3 ^ 40 * 3819834 * 2
def baseEnd_3819834 : Nat := 653803620795504371869303

theorem tailTrace_3819834 : CollatzResearch.WordTrace tailWord_3819834 prefixEnd_3819834 653803620795504371869303 := by
  unfold tailWord_3819834
  simp only [CollatzResearch.WordTrace]
  refine ⟨34830197910850317138506639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92880527762267512369351037 34830197910850317138506639)
  ·
    refine ⟨52245296866275475707759959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34830197910850317138506639 52245296866275475707759959)
    ·
      refine ⟨78367945299413213561639939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52245296866275475707759959 78367945299413213561639939)
      ·
        refine ⟨117551917949119820342459909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78367945299413213561639939 117551917949119820342459909)
        ·
          refine ⟨22040984615459966314211233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117551917949119820342459909 22040984615459966314211233)
          ·
            refine ⟨16530738461594974735658425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22040984615459966314211233 16530738461594974735658425)
            ·
              refine ⟨12398053846196231051743819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16530738461594974735658425 12398053846196231051743819)
              ·
                refine ⟨18597080769294346577615729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12398053846196231051743819 18597080769294346577615729)
                ·
                  refine ⟨13947810576970759933211797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18597080769294346577615729 13947810576970759933211797)
                  ·
                    refine ⟨653803620795504371869303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13947810576970759933211797 653803620795504371869303)
                    ·
                      rfl

theorem cell23_3819834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_3819834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819834 prefixEnd_3819834 := by exact prefixLift 3819834
  have htrace : WordTrace (prefixWord ++ tailWord_3819834) baseStart_3819834 baseEnd_3819834 := by
    simpa [prefixWord, tailWord_3819834, baseEnd_3819834] using wordTrace_append hprefix tailTrace_3819834
  have hstable : (prefixWord ++ tailWord_3819834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819834).length < 2 ^ (prefixWord ++ tailWord_3819834).sum := by decide
  have hdescent : baseEnd_3819834 < baseStart_3819834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
