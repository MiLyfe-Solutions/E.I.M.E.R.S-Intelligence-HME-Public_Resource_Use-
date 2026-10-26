import V185TrunkScan23Chunk1031

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6109313 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_6109313 : Nat := 118140960795 + 6109313 * 2 ^ 59
def prefixEnd_6109313 : Nat := 4983230072969 + 3 ^ 40 * 6109313 * 2
def baseEnd_6109313 : Nat := 3137014037761561018491287

theorem tailTrace_6109313 : CollatzResearch.WordTrace tailWord_6109313 prefixEnd_6109313 3137014037761561018491287 := by
  unfold tailWord_6109313
  simp only [CollatzResearch.WordTrace]
  refine ⟨222824950916009863437180593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148549967277339908958120395 222824950916009863437180593)
  ·
    refine ⟨167118713187007397577885445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222824950916009863437180593 167118713187007397577885445)
    ·
      refine ⟨31334758722563887045853521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167118713187007397577885445 31334758722563887045853521)
      ·
        refine ⟨23501069041922915284390141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31334758722563887045853521 23501069041922915284390141)
        ·
          refine ⟨8812900890721093231646303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23501069041922915284390141 8812900890721093231646303)
          ·
            refine ⟨13219351336081639847469455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8812900890721093231646303 13219351336081639847469455)
            ·
              refine ⟨19829027004122459771204183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13219351336081639847469455 19829027004122459771204183)
              ·
                refine ⟨29743540506183689656806275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19829027004122459771204183 29743540506183689656806275)
                ·
                  refine ⟨44615310759275534485209413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29743540506183689656806275 44615310759275534485209413)
                  ·
                    refine ⟨8365370767364162715976765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44615310759275534485209413 8365370767364162715976765)
                    ·
                      refine ⟨3137014037761561018491287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8365370767364162715976765 3137014037761561018491287)
                      ·
                        rfl

theorem cell23_6109313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_6109313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109313 prefixEnd_6109313 := by exact prefixLift 6109313
  have htrace : WordTrace (prefixWord ++ tailWord_6109313) baseStart_6109313 baseEnd_6109313 := by
    simpa [prefixWord, tailWord_6109313, baseEnd_6109313] using wordTrace_append hprefix tailTrace_6109313
  have hstable : (prefixWord ++ tailWord_6109313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109313).length < 2 ^ (prefixWord ++ tailWord_6109313).sum := by decide
  have hdescent : baseEnd_6109313 < baseStart_6109313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109320 : List Nat := [2, 1, 3, 4, 1, 1, 1, 5, 1, 4]
def baseStart_6109320 : Nat := 118140960795 + 6109320 * 2 ^ 59
def prefixEnd_6109320 : Nat := 4983230072969 + 3 ^ 40 * 6109320 * 2
def baseEnd_6109320 : Nat := 1045672544042047497034585

theorem tailTrace_6109320 : CollatzResearch.WordTrace tailWord_6109320 prefixEnd_6109320 1045672544042047497034585 := by
  unfold tailWord_6109320
  simp only [CollatzResearch.WordTrace]
  refine ⟨111412603113492251816342707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148550137484656335755123609 111412603113492251816342707)
  ·
    refine ⟨167118904670238377724514061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111412603113492251816342707 167118904670238377724514061)
    ·
      refine ⟨62669589251339391646692773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167118904670238377724514061 62669589251339391646692773)
      ·
        refine ⟨11750547984626135933754895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62669589251339391646692773 11750547984626135933754895)
        ·
          refine ⟨17625821976939203900632343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11750547984626135933754895 17625821976939203900632343)
          ·
            refine ⟨26438732965408805850948515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17625821976939203900632343 26438732965408805850948515)
            ·
              refine ⟨39658099448113208776422773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26438732965408805850948515 39658099448113208776422773)
              ·
                refine ⟨3717946823260613322789635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39658099448113208776422773 3717946823260613322789635)
                ·
                  refine ⟨5576920234890919984184453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717946823260613322789635 5576920234890919984184453)
                  ·
                    refine ⟨1045672544042047497034585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5576920234890919984184453 1045672544042047497034585)
                    ·
                      rfl

theorem cell23_6109320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_6109320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109320 prefixEnd_6109320 := by exact prefixLift 6109320
  have htrace : WordTrace (prefixWord ++ tailWord_6109320) baseStart_6109320 baseEnd_6109320 := by
    simpa [prefixWord, tailWord_6109320, baseEnd_6109320] using wordTrace_append hprefix tailTrace_6109320
  have hstable : (prefixWord ++ tailWord_6109320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109320).length < 2 ^ (prefixWord ++ tailWord_6109320).sum := by decide
  have hdescent : baseEnd_6109320 < baseStart_6109320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109394 : List Nat := [3, 2, 2, 2, 1, 3, 3, 2, 1, 1, 3]
def baseStart_6109394 : Nat := 118140960795 + 6109394 * 2 ^ 59
def prefixEnd_6109394 : Nat := 4983230072969 + 3 ^ 40 * 6109394 * 2
def baseEnd_6109394 : Nat := 3137055629694575201578415

theorem tailTrace_6109394 : CollatzResearch.WordTrace tailWord_6109394 prefixEnd_6109394 3137055629694575201578415 := by
  unfold tailWord_6109394
  simp only [CollatzResearch.WordTrace]
  refine ⟨55706976307179103567719809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148551936819144276180586157 55706976307179103567719809)
  ·
    refine ⟨41780232230384327675789857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55706976307179103567719809 41780232230384327675789857)
    ·
      refine ⟨31335174172788245756842393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41780232230384327675789857 31335174172788245756842393)
      ·
        refine ⟨23501380629591184317631795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31335174172788245756842393 23501380629591184317631795)
        ·
          refine ⟨35252070944386776476447693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23501380629591184317631795 35252070944386776476447693)
          ·
            refine ⟨13219526604145041178667885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35252070944386776476447693 13219526604145041178667885)
            ·
              refine ⟨4957322476554390442000457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13219526604145041178667885 4957322476554390442000457)
              ·
                refine ⟨3717991857415792831500343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4957322476554390442000457 3717991857415792831500343)
                ·
                  refine ⟨5576987786123689247250515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717991857415792831500343 5576987786123689247250515)
                  ·
                    refine ⟨8365481679185533870875773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5576987786123689247250515 8365481679185533870875773)
                    ·
                      refine ⟨3137055629694575201578415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8365481679185533870875773 3137055629694575201578415)
                      ·
                        rfl

theorem cell23_6109394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_6109394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109394 prefixEnd_6109394 := by exact prefixLift 6109394
  have htrace : WordTrace (prefixWord ++ tailWord_6109394) baseStart_6109394 baseEnd_6109394 := by
    simpa [prefixWord, tailWord_6109394, baseEnd_6109394] using wordTrace_append hprefix tailTrace_6109394
  have hstable : (prefixWord ++ tailWord_6109394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109394).length < 2 ^ (prefixWord ++ tailWord_6109394).sum := by decide
  have hdescent : baseEnd_6109394 < baseStart_6109394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109433 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 4, 1, 3]
def baseStart_6109433 : Nat := 118140960795 + 6109433 * 2 ^ 59
def prefixEnd_6109433 : Nat := 4983230072969 + 3 ^ 40 * 6109433 * 2
def baseEnd_6109433 : Nat := 3137075655440100548990735

theorem tailTrace_6109433 : CollatzResearch.WordTrace tailWord_6109433 prefixEnd_6109433 3137075655440100548990735 := by
  unfold tailWord_6109433
  simp only [CollatzResearch.WordTrace]
  refine ⟨222829327675575123931548953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148552885117050082621032635 222829327675575123931548953)
  ·
    refine ⟨167121995756681342948661715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222829327675575123931548953 167121995756681342948661715)
    ·
      refine ⟨250682993635022014422992573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167121995756681342948661715 250682993635022014422992573)
      ·
        refine ⟨94006122613133255408622215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250682993635022014422992573 94006122613133255408622215)
        ·
          refine ⟨141009183919699883112933323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94006122613133255408622215 141009183919699883112933323)
          ·
            refine ⟨211513775879549824669399985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141009183919699883112933323 211513775879549824669399985)
            ·
              refine ⟨158635331909662368502049989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211513775879549824669399985 158635331909662368502049989)
              ·
                refine ⟨29744124733061694094134373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158635331909662368502049989 29744124733061694094134373)
                ·
                  refine ⟨5577023387449067642650195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29744124733061694094134373 5577023387449067642650195)
                  ·
                    refine ⟨8365535081173601463975293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5577023387449067642650195 8365535081173601463975293)
                    ·
                      refine ⟨3137075655440100548990735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8365535081173601463975293 3137075655440100548990735)
                      ·
                        rfl

theorem cell23_6109433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_6109433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109433 prefixEnd_6109433 := by exact prefixLift 6109433
  have htrace : WordTrace (prefixWord ++ tailWord_6109433) baseStart_6109433 baseEnd_6109433 := by
    simpa [prefixWord, tailWord_6109433, baseEnd_6109433] using wordTrace_append hprefix tailTrace_6109433
  have hstable : (prefixWord ++ tailWord_6109433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109433).length < 2 ^ (prefixWord ++ tailWord_6109433).sum := by decide
  have hdescent : baseEnd_6109433 < baseStart_6109433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109450 : List Nat := [3, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3]
def baseStart_6109450 : Nat := 118140960795 + 6109450 * 2 ^ 59
def prefixEnd_6109450 : Nat := 4983230072969 + 3 ^ 40 * 6109450 * 2
def baseEnd_6109450 : Nat := 3137084384611226982478157

theorem tailTrace_6109450 : CollatzResearch.WordTrace tailWord_6109450 prefixEnd_6109450 3137084384611226982478157 := by
  unfold tailWord_6109450
  simp only [CollatzResearch.WordTrace]
  refine ⟨55707486929128383958729451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148553298477675690556611869 55707486929128383958729451)
  ·
    refine ⟨83561230393692575938094177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55707486929128383958729451 83561230393692575938094177)
    ·
      refine ⟨62670922795269431953570633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83561230393692575938094177 62670922795269431953570633)
      ·
        refine ⟨47003192096452073965177975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62670922795269431953570633 47003192096452073965177975)
        ·
          refine ⟨70504788144678110947766963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47003192096452073965177975 70504788144678110947766963)
          ·
            refine ⟨105757182217017166421650445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70504788144678110947766963 105757182217017166421650445)
            ·
              refine ⟨39658943331381437408118917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105757182217017166421650445 39658943331381437408118917)
              ·
                refine ⟨7436051874634019514022297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39658943331381437408118917 7436051874634019514022297)
                ·
                  refine ⟨5577038905975514635516723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7436051874634019514022297 5577038905975514635516723)
                  ·
                    refine ⟨8365558358963271953275085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5577038905975514635516723 8365558358963271953275085)
                    ·
                      refine ⟨3137084384611226982478157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8365558358963271953275085 3137084384611226982478157)
                      ·
                        rfl

theorem cell23_6109450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_6109450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109450 prefixEnd_6109450 := by exact prefixLift 6109450
  have htrace : WordTrace (prefixWord ++ tailWord_6109450) baseStart_6109450 baseEnd_6109450 := by
    simpa [prefixWord, tailWord_6109450, baseEnd_6109450] using wordTrace_append hprefix tailTrace_6109450
  have hstable : (prefixWord ++ tailWord_6109450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109450).length < 2 ^ (prefixWord ++ tailWord_6109450).sum := by decide
  have hdescent : baseEnd_6109450 < baseStart_6109450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109507 : List Nat := [1, 1, 1, 3, 1, 3, 5, 2, 2, 2, 2]
def baseStart_6109507 : Nat := 118140960795 + 6109507 * 2 ^ 59
def prefixEnd_6109507 : Nat := 4983230072969 + 3 ^ 40 * 6109507 * 2
def baseEnd_6109507 : Nat := 3137113653008533259465395

theorem tailTrace_6109507 : CollatzResearch.WordTrace tailWord_6109507 prefixEnd_6109507 3137113653008533259465395 := by
  unfold tailWord_6109507
  simp only [CollatzResearch.WordTrace]
  refine ⟨222832026677307034569742775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148554684451538023046495183 222832026677307034569742775)
  ·
    refine ⟨334248040015960551854614163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222832026677307034569742775 334248040015960551854614163)
    ·
      refine ⟨501372060023940827781921245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334248040015960551854614163 501372060023940827781921245)
      ·
        refine ⟨188014522508977810418220467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 501372060023940827781921245 188014522508977810418220467)
        ·
          refine ⟨282021783763466715627330701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188014522508977810418220467 282021783763466715627330701)
          ·
            refine ⟨105758168911300018360249013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282021783763466715627330701 105758168911300018360249013)
            ·
              refine ⟨9914828335434376721273345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105758168911300018360249013 9914828335434376721273345)
              ·
                refine ⟨7436121251575782540955009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9914828335434376721273345 7436121251575782540955009)
                ·
                  refine ⟨5577090938681836905716257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7436121251575782540955009 5577090938681836905716257)
                  ·
                    refine ⟨4182818204011377679287193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5577090938681836905716257 4182818204011377679287193)
                    ·
                      refine ⟨3137113653008533259465395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4182818204011377679287193 3137113653008533259465395)
                      ·
                        rfl

theorem cell23_6109507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 2, 2].length) (baseStart_6109507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109507 prefixEnd_6109507 := by exact prefixLift 6109507
  have htrace : WordTrace (prefixWord ++ tailWord_6109507) baseStart_6109507 baseEnd_6109507 := by
    simpa [prefixWord, tailWord_6109507, baseEnd_6109507] using wordTrace_append hprefix tailTrace_6109507
  have hstable : (prefixWord ++ tailWord_6109507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109507).length < 2 ^ (prefixWord ++ tailWord_6109507).sum := by decide
  have hdescent : baseEnd_6109507 < baseStart_6109507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109543 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 1, 7]
def baseStart_6109543 : Nat := 118140960795 + 6109543 * 2 ^ 59
def prefixEnd_6109543 : Nat := 4983230072969 + 3 ^ 40 * 6109543 * 2
def baseEnd_6109543 : Nat := 1045710712770698372871743

theorem tailTrace_6109543 : CollatzResearch.WordTrace tailWord_6109543 prefixEnd_6109543 1045710712770698372871743 := by
  unfold tailWord_6109543
  simp only [CollatzResearch.WordTrace]
  refine ⟨222833339705176612718053283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148555559803451075145368855 222833339705176612718053283)
  ·
    refine ⟨334250009557764919077079925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222833339705176612718053283 334250009557764919077079925)
    ·
      refine ⟨31335938396040461163476243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 334250009557764919077079925 31335938396040461163476243)
      ·
        refine ⟨47003907594060691745214365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31335938396040461163476243 47003907594060691745214365)
        ·
          refine ⟨17626465347772759404455387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47003907594060691745214365 17626465347772759404455387)
          ·
            refine ⟨26439698021659139106683081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17626465347772759404455387 26439698021659139106683081)
            ·
              refine ⟨19829773516244354330012311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26439698021659139106683081 19829773516244354330012311)
              ·
                refine ⟨29744660274366531495018467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19829773516244354330012311 29744660274366531495018467)
                ·
                  refine ⟨44616990411549797242527701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29744660274366531495018467 44616990411549797242527701)
                  ·
                    refine ⟨1045710712770698372871743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44616990411549797242527701 1045710712770698372871743)
                    ·
                      rfl

theorem cell23_6109543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_6109543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109543 prefixEnd_6109543 := by exact prefixLift 6109543
  have htrace : WordTrace (prefixWord ++ tailWord_6109543) baseStart_6109543 baseEnd_6109543 := by
    simpa [prefixWord, tailWord_6109543, baseEnd_6109543] using wordTrace_append hprefix tailTrace_6109543
  have hstable : (prefixWord ++ tailWord_6109543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109543).length < 2 ^ (prefixWord ++ tailWord_6109543).sum := by decide
  have hdescent : baseEnd_6109543 < baseStart_6109543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109563 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 4]
def baseStart_6109563 : Nat := 118140960795 + 6109563 * 2 ^ 59
def prefixEnd_6109563 : Nat := 4983230072969 + 3 ^ 40 * 6109563 * 2
def baseEnd_6109563 : Nat := 3137142407925185040365137

theorem tailTrace_6109563 : CollatzResearch.WordTrace tailWord_6109563 prefixEnd_6109563 3137142407925185040365137 := by
  unfold tailWord_6109563
  simp only [CollatzResearch.WordTrace]
  refine ⟨222834069165104156133781343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148556046110069437422520895 222834069165104156133781343)
  ·
    refine ⟨334251103747656234200672015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222834069165104156133781343 334251103747656234200672015)
    ·
      refine ⟨501376655621484351301008023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334251103747656234200672015 501376655621484351301008023)
      ·
        refine ⟨752064983432226526951512035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501376655621484351301008023 752064983432226526951512035)
        ·
          refine ⟨1128097475148339790427268053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752064983432226526951512035 1128097475148339790427268053)
          ·
            refine ⟨26439784573789213838139095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1128097475148339790427268053 26439784573789213838139095)
            ·
              refine ⟨39659676860683820757208643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26439784573789213838139095 39659676860683820757208643)
              ·
                refine ⟨59489515291025731135812965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39659676860683820757208643 59489515291025731135812965)
                ·
                  refine ⟨11154284117067324587964931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59489515291025731135812965 11154284117067324587964931)
                  ·
                    refine ⟨16731426175600986881947397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11154284117067324587964931 16731426175600986881947397)
                    ·
                      refine ⟨3137142407925185040365137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16731426175600986881947397 3137142407925185040365137)
                      ·
                        rfl

theorem cell23_6109563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 4].length) (baseStart_6109563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109563 prefixEnd_6109563 := by exact prefixLift 6109563
  have htrace : WordTrace (prefixWord ++ tailWord_6109563) baseStart_6109563 baseEnd_6109563 := by
    simpa [prefixWord, tailWord_6109563, baseEnd_6109563] using wordTrace_append hprefix tailTrace_6109563
  have hstable : (prefixWord ++ tailWord_6109563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109563).length < 2 ^ (prefixWord ++ tailWord_6109563).sum := by decide
  have hdescent : baseEnd_6109563 < baseStart_6109563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109597 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_6109597 : Nat := 118140960795 + 6109597 * 2 ^ 59
def prefixEnd_6109597 : Nat := 4983230072969 + 3 ^ 40 * 6109597 * 2
def baseEnd_6109597 : Nat := 3137159866267437907339981

theorem tailTrace_6109597 : CollatzResearch.WordTrace tailWord_6109597 prefixEnd_6109597 3137159866267437907339981 := by
  unfold tailWord_6109597
  simp only [CollatzResearch.WordTrace]
  refine ⟨222835309246980979940519045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148556872831320653293679363 222835309246980979940519045)
  ·
    refine ⟨41781620483808933738847321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222835309246980979940519045 41781620483808933738847321)
    ·
      refine ⟨31336215362856700304135491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41781620483808933738847321 31336215362856700304135491)
      ·
        refine ⟨47004323044285050456203237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31336215362856700304135491 47004323044285050456203237)
        ·
          refine ⟨8813310570803446960538107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47004323044285050456203237 8813310570803446960538107)
          ·
            refine ⟨13219965856205170440807161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8813310570803446960538107 13219965856205170440807161)
            ·
              refine ⟨9914974392153877830605371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13219965856205170440807161 9914974392153877830605371)
              ·
                refine ⟨14872461588230816745908057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9914974392153877830605371 14872461588230816745908057)
                ·
                  refine ⟨11154346191173112559431043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14872461588230816745908057 11154346191173112559431043)
                  ·
                    refine ⟨16731519286759668839146565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11154346191173112559431043 16731519286759668839146565)
                    ·
                      refine ⟨3137159866267437907339981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16731519286759668839146565 3137159866267437907339981)
                      ·
                        rfl

theorem cell23_6109597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_6109597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109597 prefixEnd_6109597 := by exact prefixLift 6109597
  have htrace : WordTrace (prefixWord ++ tailWord_6109597) baseStart_6109597 baseEnd_6109597 := by
    simpa [prefixWord, tailWord_6109597, baseEnd_6109597] using wordTrace_append hprefix tailTrace_6109597
  have hstable : (prefixWord ++ tailWord_6109597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109597).length < 2 ^ (prefixWord ++ tailWord_6109597).sum := by decide
  have hdescent : baseEnd_6109597 < baseStart_6109597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109600 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 3]
def baseStart_6109600 : Nat := 118140960795 + 6109600 * 2 ^ 59
def prefixEnd_6109600 : Nat := 4983230072969 + 3 ^ 40 * 6109600 * 2
def baseEnd_6109600 : Nat := 3137161406709401395602467

theorem tailTrace_6109600 : CollatzResearch.WordTrace tailWord_6109600 prefixEnd_6109600 3137161406709401395602467 := by
  unfold tailWord_6109600
  simp only [CollatzResearch.WordTrace]
  refine ⟨111417709332985055726439127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148556945777313407635252169 111417709332985055726439127)
  ·
    refine ⟨167126563999477583589658691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111417709332985055726439127 167126563999477583589658691)
    ·
      refine ⟨250689845999216375384488037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167126563999477583589658691 250689845999216375384488037)
      ·
        refine ⟨47004346124853070384591507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250689845999216375384488037 47004346124853070384591507)
        ·
          refine ⟨70506519187279605576887261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47004346124853070384591507 70506519187279605576887261)
          ·
            refine ⟨26439944695229852091332723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70506519187279605576887261 26439944695229852091332723)
            ·
              refine ⟨39659917042844778136999085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26439944695229852091332723 39659917042844778136999085)
              ·
                refine ⟨14872468891066791801374657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39659917042844778136999085 14872468891066791801374657)
                ·
                  refine ⟨11154351668300093851030993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14872468891066791801374657 11154351668300093851030993)
                  ·
                    refine ⟨8365763751225070388273245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11154351668300093851030993 8365763751225070388273245)
                    ·
                      refine ⟨3137161406709401395602467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8365763751225070388273245 3137161406709401395602467)
                      ·
                        rfl

theorem cell23_6109600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_6109600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109600 prefixEnd_6109600 := by exact prefixLift 6109600
  have htrace : WordTrace (prefixWord ++ tailWord_6109600) baseStart_6109600 baseEnd_6109600 := by
    simpa [prefixWord, tailWord_6109600, baseEnd_6109600] using wordTrace_append hprefix tailTrace_6109600
  have hstable : (prefixWord ++ tailWord_6109600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109600).length < 2 ^ (prefixWord ++ tailWord_6109600).sum := by decide
  have hdescent : baseEnd_6109600 < baseStart_6109600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109664 : List Nat := [2, 1, 1, 3, 1, 1, 6, 3, 1, 1, 3]
def baseStart_6109664 : Nat := 118140960795 + 6109664 * 2 ^ 59
def prefixEnd_6109664 : Nat := 4983230072969 + 3 ^ 40 * 6109664 * 2
def baseEnd_6109664 : Nat := 3137194269471289145202173

theorem tailTrace_6109664 : CollatzResearch.WordTrace tailWord_6109664 prefixEnd_6109664 3137194269471289145202173 := by
  unfold tailWord_6109664
  simp only [CollatzResearch.WordTrace]
  refine ⟨111418876468869125191604023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148558501958492166922138697 111418876468869125191604023)
  ·
    refine ⟨167128314703303687787406035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111418876468869125191604023 167128314703303687787406035)
    ·
      refine ⟨250692472054955531681109053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167128314703303687787406035 250692472054955531681109053)
      ·
        refine ⟨94009677020608324380415895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250692472054955531681109053 94009677020608324380415895)
        ·
          refine ⟨141014515530912486570623843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94009677020608324380415895 141014515530912486570623843)
          ·
            refine ⟨211521773296368729855935765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141014515530912486570623843 211521773296368729855935765)
            ·
              refine ⟨9915083123267284211996989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 211521773296368729855935765 9915083123267284211996989)
              ·
                refine ⟨3718156171225231579498871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9915083123267284211996989 3718156171225231579498871)
                ·
                  refine ⟨5577234256837847369248307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3718156171225231579498871 5577234256837847369248307)
                  ·
                    refine ⟨8365851385256771053872461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5577234256837847369248307 8365851385256771053872461)
                    ·
                      refine ⟨3137194269471289145202173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8365851385256771053872461 3137194269471289145202173)
                      ·
                        rfl

theorem cell23_6109664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_6109664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109664 prefixEnd_6109664 := by exact prefixLift 6109664
  have htrace : WordTrace (prefixWord ++ tailWord_6109664) baseStart_6109664 baseEnd_6109664 := by
    simpa [prefixWord, tailWord_6109664, baseEnd_6109664] using wordTrace_append hprefix tailTrace_6109664
  have hstable : (prefixWord ++ tailWord_6109664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109664).length < 2 ^ (prefixWord ++ tailWord_6109664).sum := by decide
  have hdescent : baseEnd_6109664 < baseStart_6109664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109667 : List Nat := [1, 1, 1, 6, 3, 1, 1, 3, 1, 5]
def baseStart_6109667 : Nat := 118140960795 + 6109667 * 2 ^ 59
def prefixEnd_6109667 : Nat := 4983230072969 + 3 ^ 40 * 6109667 * 2
def baseEnd_6109667 : Nat := 1045731936637750877821553

theorem tailTrace_6109667 : CollatzResearch.WordTrace tailWord_6109667 prefixEnd_6109667 1045731936637750877821553 := by
  unfold tailWord_6109667
  simp only [CollatzResearch.WordTrace]
  refine ⟨222837862356727381895567255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148558574904484921263711503 222837862356727381895567255)
  ·
    refine ⟨334256793535091072843350883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222837862356727381895567255 334256793535091072843350883)
    ·
      refine ⟨501385190302636609265026325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334256793535091072843350883 501385190302636609265026325)
      ·
        refine ⟨23502430795436091059298109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 501385190302636609265026325 23502430795436091059298109)
        ·
          refine ⟨8813411548288534147236791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23502430795436091059298109 8813411548288534147236791)
          ·
            refine ⟨13220117322432801220855187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8813411548288534147236791 13220117322432801220855187)
            ·
              refine ⟨19830175983649201831282781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13220117322432801220855187 19830175983649201831282781)
              ·
                refine ⟨7436315993868450686731043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19830175983649201831282781 7436315993868450686731043)
                ·
                  refine ⟨11154473990802676030096565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7436315993868450686731043 11154473990802676030096565)
                  ·
                    refine ⟨1045731936637750877821553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11154473990802676030096565 1045731936637750877821553)
                    ·
                      rfl

theorem cell23_6109667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 5].length) (baseStart_6109667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109667 prefixEnd_6109667 := by exact prefixLift 6109667
  have htrace : WordTrace (prefixWord ++ tailWord_6109667) baseStart_6109667 baseEnd_6109667 := by
    simpa [prefixWord, tailWord_6109667, baseEnd_6109667] using wordTrace_append hprefix tailTrace_6109667
  have hstable : (prefixWord ++ tailWord_6109667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109667).length < 2 ^ (prefixWord ++ tailWord_6109667).sum := by decide
  have hdescent : baseEnd_6109667 < baseStart_6109667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109680 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 4, 4]
def baseStart_6109680 : Nat := 118140960795 + 6109680 * 2 ^ 59
def prefixEnd_6109680 : Nat := 4983230072969 + 3 ^ 40 * 6109680 * 2
def baseEnd_6109680 : Nat := 1045734161720587027534033

theorem tailTrace_6109680 : CollatzResearch.WordTrace tailWord_6109680 prefixEnd_6109680 1045734161720587027534033 := by
  unfold tailWord_6109680
  simp only [CollatzResearch.WordTrace]
  refine ⟨111419168252840142557895247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148558891003786856743860329 111419168252840142557895247)
  ·
    refine ⟨167128752379260213836842871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111419168252840142557895247 167128752379260213836842871)
    ·
      refine ⟨250693128568890320755264307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167128752379260213836842871 250693128568890320755264307)
      ·
        refine ⟨376039692853335481132896461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250693128568890320755264307 376039692853335481132896461)
        ·
          refine ⟨141014884820000805424836173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376039692853335481132896461 141014884820000805424836173)
          ·
            refine ⟨52880581807500302034313565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141014884820000805424836173 52880581807500302034313565)
            ·
              refine ⟨19830218177812613262867587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52880581807500302034313565 19830218177812613262867587)
              ·
                refine ⟨29745327266718919894301381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19830218177812613262867587 29745327266718919894301381)
                ·
                  refine ⟨5577248862509797480181509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29745327266718919894301381 5577248862509797480181509)
                  ·
                    refine ⟨1045734161720587027534033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5577248862509797480181509 1045734161720587027534033)
                    ·
                      rfl

theorem cell23_6109680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 4, 4].length) (baseStart_6109680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109680 prefixEnd_6109680 := by exact prefixLift 6109680
  have htrace : WordTrace (prefixWord ++ tailWord_6109680) baseStart_6109680 baseEnd_6109680 := by
    simpa [prefixWord, tailWord_6109680, baseEnd_6109680] using wordTrace_append hprefix tailTrace_6109680
  have hstable : (prefixWord ++ tailWord_6109680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109680).length < 2 ^ (prefixWord ++ tailWord_6109680).sum := by decide
  have hdescent : baseEnd_6109680 < baseStart_6109680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109683 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 6]
def baseStart_6109683 : Nat := 118140960795 + 6109683 * 2 ^ 59
def prefixEnd_6109683 : Nat := 4983230072969 + 3 ^ 40 * 6109683 * 2
def baseEnd_6109683 : Nat := 3137204025603724570864585

theorem tailTrace_6109683 : CollatzResearch.WordTrace tailWord_6109683 prefixEnd_6109683 3137204025603724570864585 := by
  unfold tailWord_6109683
  simp only [CollatzResearch.WordTrace]
  refine ⟨222838445924669416628149703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148558963949779611085433135 222838445924669416628149703)
  ·
    refine ⟨334257668887004124942224555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222838445924669416628149703 334257668887004124942224555)
    ·
      refine ⟨501386503330506187413336833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334257668887004124942224555 501386503330506187413336833)
      ·
        refine ⟨376039877497879640560002625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501386503330506187413336833 376039877497879640560002625)
        ·
          refine ⟨282029908123409730420001969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376039877497879640560002625 282029908123409730420001969)
          ·
            refine ⟨211522431092557297815001477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282029908123409730420001969 211522431092557297815001477)
            ·
              refine ⟨39660455829854493340312777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211522431092557297815001477 39660455829854493340312777)
              ·
                refine ⟨29745341872390870005234583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39660455829854493340312777 29745341872390870005234583)
                ·
                  refine ⟨44618012808586305007851875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29745341872390870005234583 44618012808586305007851875)
                  ·
                    refine ⟨66927019212879457511777813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44618012808586305007851875 66927019212879457511777813)
                    ·
                      refine ⟨3137204025603724570864585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66927019212879457511777813 3137204025603724570864585)
                      ·
                        rfl

theorem cell23_6109683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_6109683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109683 prefixEnd_6109683 := by exact prefixLift 6109683
  have htrace : WordTrace (prefixWord ++ tailWord_6109683) baseStart_6109683 baseEnd_6109683 := by
    simpa [prefixWord, tailWord_6109683, baseEnd_6109683] using wordTrace_append hprefix tailTrace_6109683
  have hstable : (prefixWord ++ tailWord_6109683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109683).length < 2 ^ (prefixWord ++ tailWord_6109683).sum := by decide
  have hdescent : baseEnd_6109683 < baseStart_6109683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109690 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3]
def baseStart_6109690 : Nat := 118140960795 + 6109690 * 2 ^ 59
def prefixEnd_6109690 : Nat := 4983230072969 + 3 ^ 40 * 6109690 * 2
def baseEnd_6109690 : Nat := 3137207619968306043477053

theorem tailTrace_6109690 : CollatzResearch.WordTrace tailWord_6109690 prefixEnd_6109690 3137207619968306043477053 := by
  unfold tailWord_6109690
  simp only [CollatzResearch.WordTrace]
  refine ⟨55709675308911014205913631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148559134157096037882436349 55709675308911014205913631)
  ·
    refine ⟨83564512963366521308870447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55709675308911014205913631 83564512963366521308870447)
    ·
      refine ⟨125346769445049781963305671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83564512963366521308870447 125346769445049781963305671)
      ·
        refine ⟨188020154167574672944958507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125346769445049781963305671 188020154167574672944958507)
        ·
          refine ⟨282030231251362009417437761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188020154167574672944958507 282030231251362009417437761)
          ·
            refine ⟨211522673438521507063078321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282030231251362009417437761 211522673438521507063078321)
            ·
              refine ⟨158642005078891130297308741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211522673438521507063078321 158642005078891130297308741)
              ·
                refine ⟨29745375952292086930745389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158642005078891130297308741 29745375952292086930745389)
                ·
                  refine ⟨11154515982109532599029521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29745375952292086930745389 11154515982109532599029521)
                  ·
                    refine ⟨8365886986582149449272141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11154515982109532599029521 8365886986582149449272141)
                    ·
                      refine ⟨3137207619968306043477053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8365886986582149449272141 3137207619968306043477053)
                      ·
                        rfl

theorem cell23_6109690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_6109690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109690 prefixEnd_6109690 := by exact prefixLift 6109690
  have htrace : WordTrace (prefixWord ++ tailWord_6109690) baseStart_6109690 baseEnd_6109690 := by
    simpa [prefixWord, tailWord_6109690, baseEnd_6109690] using wordTrace_append hprefix tailTrace_6109690
  have hstable : (prefixWord ++ tailWord_6109690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109690).length < 2 ^ (prefixWord ++ tailWord_6109690).sum := by decide
  have hdescent : baseEnd_6109690 < baseStart_6109690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109693 : List Nat := [1, 4, 1, 1, 1, 3, 2, 10]
def baseStart_6109693 : Nat := 118140960795 + 6109693 * 2 ^ 59
def prefixEnd_6109693 : Nat := 4983230072969 + 3 ^ 40 * 6109693 * 2
def baseEnd_6109693 : Nat := 116192931867047019694057

theorem tailTrace_6109693 : CollatzResearch.WordTrace tailWord_6109693 prefixEnd_6109693 116192931867047019694057 := by
  unfold tailWord_6109693
  simp only [CollatzResearch.WordTrace]
  refine ⟨222838810654633188336013733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148559207103088792224009155 222838810654633188336013733)
  ·
    refine ⟨41782276997743722813002575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222838810654633188336013733 41782276997743722813002575)
    ·
      refine ⟨62673415496615584219503863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41782276997743722813002575 62673415496615584219503863)
      ·
        refine ⟨94010123244923376329255795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62673415496615584219503863 94010123244923376329255795)
        ·
          refine ⟨141015184867385064493883693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94010123244923376329255795 141015184867385064493883693)
          ·
            refine ⟨52880694325269399185206385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141015184867385064493883693 52880694325269399185206385)
            ·
              refine ⟨39660520743952049388904789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52880694325269399185206385 39660520743952049388904789)
              ·
                refine ⟨116192931867047019694057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39660520743952049388904789 116192931867047019694057)
                ·
                  rfl

theorem cell23_6109693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 10].length) (baseStart_6109693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109693 prefixEnd_6109693 := by exact prefixLift 6109693
  have htrace : WordTrace (prefixWord ++ tailWord_6109693) baseStart_6109693 baseEnd_6109693 := by
    simpa [prefixWord, tailWord_6109693, baseEnd_6109693] using wordTrace_append hprefix tailTrace_6109693
  have hstable : (prefixWord ++ tailWord_6109693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109693).length < 2 ^ (prefixWord ++ tailWord_6109693).sum := by decide
  have hdescent : baseEnd_6109693 < baseStart_6109693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109697 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 1, 6]
def baseStart_6109697 : Nat := 118140960795 + 6109697 * 2 ^ 59
def prefixEnd_6109697 : Nat := 4983230072969 + 3 ^ 40 * 6109697 * 2
def baseEnd_6109697 : Nat := 1045737071444295838696507

theorem tailTrace_6109697 : CollatzResearch.WordTrace tailWord_6109697 prefixEnd_6109697 1045737071444295838696507 := by
  unfold tailWord_6109697
  simp only [CollatzResearch.WordTrace]
  refine ⟨222838956546618697019159345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148559304364412464679439563 222838956546618697019159345)
  ·
    refine ⟨167129217409964022764369509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222838956546618697019159345 167129217409964022764369509)
    ·
      refine ⟨31336728264368254268319283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167129217409964022764369509 31336728264368254268319283)
      ·
        refine ⟨47005092396552381402478925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31336728264368254268319283 47005092396552381402478925)
        ·
          refine ⟨17626909648707143025929597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47005092396552381402478925 17626909648707143025929597)
          ·
            refine ⟨6610091118265178634723599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17626909648707143025929597 6610091118265178634723599)
            ·
              refine ⟨9915136677397767952085399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6610091118265178634723599 9915136677397767952085399)
              ·
                refine ⟨14872705016096651928128099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9915136677397767952085399 14872705016096651928128099)
                ·
                  refine ⟨22309057524144977892192149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14872705016096651928128099 22309057524144977892192149)
                  ·
                    refine ⟨1045737071444295838696507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22309057524144977892192149 1045737071444295838696507)
                    ·
                      rfl

theorem cell23_6109697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_6109697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109697 prefixEnd_6109697 := by exact prefixLift 6109697
  have htrace : WordTrace (prefixWord ++ tailWord_6109697) baseStart_6109697 baseEnd_6109697 := by
    simpa [prefixWord, tailWord_6109697, baseEnd_6109697] using wordTrace_append hprefix tailTrace_6109697
  have hstable : (prefixWord ++ tailWord_6109697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109697).length < 2 ^ (prefixWord ++ tailWord_6109697).sum := by decide
  have hdescent : baseEnd_6109697 < baseStart_6109697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109707 : List Nat := [1, 1, 1, 1, 7, 1, 1, 4, 1, 2, 3]
def baseStart_6109707 : Nat := 118140960795 + 6109707 * 2 ^ 59
def prefixEnd_6109707 : Nat := 4983230072969 + 3 ^ 40 * 6109707 * 2
def baseEnd_6109707 : Nat := 3137216349139432476964475

theorem tailTrace_6109707 : CollatzResearch.WordTrace tailWord_6109707 prefixEnd_6109707 3137216349139432476964475 := by
  unfold tailWord_6109707
  simp only [CollatzResearch.WordTrace]
  refine ⟨222839321276582468727023375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148559547517721645818015583 222839321276582468727023375)
  ·
    refine ⟨334258981914873703090535063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222839321276582468727023375 334258981914873703090535063)
    ·
      refine ⟨501388472872310554635802595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334258981914873703090535063 501388472872310554635802595)
      ·
        refine ⟨752082709308465831953703893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501388472872310554635802595 752082709308465831953703893)
        ·
          refine ⟨17626938499417167936414935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 752082709308465831953703893 17626938499417167936414935)
          ·
            refine ⟨26440407749125751904622403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17626938499417167936414935 26440407749125751904622403)
            ·
              refine ⟨39660611623688627856933605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26440407749125751904622403 39660611623688627856933605)
              ·
                refine ⟨7436364679441617723175051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39660611623688627856933605 7436364679441617723175051)
                ·
                  refine ⟨11154547019162426584762577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7436364679441617723175051 11154547019162426584762577)
                  ·
                    refine ⟨8365910264371819938571933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11154547019162426584762577 8365910264371819938571933)
                    ·
                      refine ⟨3137216349139432476964475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8365910264371819938571933 3137216349139432476964475)
                      ·
                        rfl

theorem cell23_6109707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 2, 3].length) (baseStart_6109707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109707 prefixEnd_6109707 := by exact prefixLift 6109707
  have htrace : WordTrace (prefixWord ++ tailWord_6109707) baseStart_6109707 baseEnd_6109707 := by
    simpa [prefixWord, tailWord_6109707, baseEnd_6109707] using wordTrace_append hprefix tailTrace_6109707
  have hstable : (prefixWord ++ tailWord_6109707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109707).length < 2 ^ (prefixWord ++ tailWord_6109707).sum := by decide
  have hdescent : baseEnd_6109707 < baseStart_6109707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109710 : List Nat := [4, 1, 1, 2, 3, 2, 1, 9]
def baseStart_6109710 : Nat := 118140960795 + 6109710 * 2 ^ 59
def prefixEnd_6109710 : Nat := 4983230072969 + 3 ^ 40 * 6109710 * 2
def baseEnd_6109710 : Nat := 116193255169681332045443

theorem tailTrace_6109710 : CollatzResearch.WordTrace tailWord_6109710 prefixEnd_6109710 116193255169681332045443 := by
  unfold tailWord_6109710
  simp only [CollatzResearch.WordTrace]
  refine ⟨27854928836946450029922823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148559620463714400159588389 27854928836946450029922823)
  ·
    refine ⟨41782393255419675044884235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27854928836946450029922823 41782393255419675044884235)
    ·
      refine ⟨62673589883129512567326353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41782393255419675044884235 62673589883129512567326353)
      ·
        refine ⟨47005192412347134425494765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62673589883129512567326353 47005192412347134425494765)
        ·
          refine ⟨17626947154630175409560537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47005192412347134425494765 17626947154630175409560537)
          ·
            refine ⟨13220210365972631557170403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17626947154630175409560537 13220210365972631557170403)
            ·
              refine ⟨19830315548958947335755605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13220210365972631557170403 19830315548958947335755605)
              ·
                refine ⟨116193255169681332045443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19830315548958947335755605 116193255169681332045443)
                ·
                  rfl

theorem cell23_6109710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 9].length) (baseStart_6109710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109710 prefixEnd_6109710 := by exact prefixLift 6109710
  have htrace : WordTrace (prefixWord ++ tailWord_6109710) baseStart_6109710 baseEnd_6109710 := by
    simpa [prefixWord, tailWord_6109710, baseEnd_6109710] using wordTrace_append hprefix tailTrace_6109710
  have hstable : (prefixWord ++ tailWord_6109710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109710).length < 2 ^ (prefixWord ++ tailWord_6109710).sum := by decide
  have hdescent : baseEnd_6109710 < baseStart_6109710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109747 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 3, 3, 2]
def baseStart_6109747 : Nat := 118140960795 + 6109747 * 2 ^ 59
def prefixEnd_6109747 : Nat := 4983230072969 + 3 ^ 40 * 6109747 * 2
def baseEnd_6109747 : Nat := 3137236888365612320464291

theorem tailTrace_6109747 : CollatzResearch.WordTrace tailWord_6109747 prefixEnd_6109747 3137236888365612320464291 := by
  unfold tailWord_6109747
  simp only [CollatzResearch.WordTrace]
  refine ⟨222840780196437555558479495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148560520130958370372319663 222840780196437555558479495)
  ·
    refine ⟨334261170294656333337719243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222840780196437555558479495 334261170294656333337719243)
    ·
      refine ⟨501391755441984500006578865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334261170294656333337719243 501391755441984500006578865)
      ·
        refine ⟨376043816581488375004934149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501391755441984500006578865 376043816581488375004934149)
        ·
          refine ⟨70508215609029070313425153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 376043816581488375004934149 70508215609029070313425153)
          ·
            refine ⟨52881161706771802735068865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70508215609029070313425153 52881161706771802735068865)
            ·
              refine ⟨39660871280078852051301649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52881161706771802735068865 39660871280078852051301649)
              ·
                refine ⟨29745653460059139038476237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39660871280078852051301649 29745653460059139038476237)
                ·
                  refine ⟨11154620047522177139428589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29745653460059139038476237 11154620047522177139428589)
                  ·
                    refine ⟨4182982517820816427285721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11154620047522177139428589 4182982517820816427285721)
                    ·
                      refine ⟨3137236888365612320464291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4182982517820816427285721 3137236888365612320464291)
                      ·
                        rfl

theorem cell23_6109747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 3, 2].length) (baseStart_6109747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109747 prefixEnd_6109747 := by exact prefixLift 6109747
  have htrace : WordTrace (prefixWord ++ tailWord_6109747) baseStart_6109747 baseEnd_6109747 := by
    simpa [prefixWord, tailWord_6109747, baseEnd_6109747] using wordTrace_append hprefix tailTrace_6109747
  have hstable : (prefixWord ++ tailWord_6109747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109747).length < 2 ^ (prefixWord ++ tailWord_6109747).sum := by decide
  have hdescent : baseEnd_6109747 < baseStart_6109747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109754 : List Nat := [3, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3]
def baseStart_6109754 : Nat := 118140960795 + 6109754 * 2 ^ 59
def prefixEnd_6109754 : Nat := 4983230072969 + 3 ^ 40 * 6109754 * 2
def baseEnd_6109754 : Nat := 3137240482730193793076759

theorem tailTrace_6109754 : CollatzResearch.WordTrace tailWord_6109754 prefixEnd_6109754 3137240482730193793076759 := by
  unfold tailWord_6109754
  simp only [CollatzResearch.WordTrace]
  refine ⟨55710258876853048938496079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148560690338274797169322877 55710258876853048938496079)
  ·
    refine ⟨83565388315279573407744119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55710258876853048938496079 83565388315279573407744119)
    ·
      refine ⟨125348082472919360111616179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83565388315279573407744119 125348082472919360111616179)
      ·
        refine ⟨188022123709379040167424269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125348082472919360111616179 188022123709379040167424269)
        ·
          refine ⟨70508296391017140062784101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188022123709379040167424269 70508296391017140062784101)
          ·
            refine ⟨13220305573315713761772019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70508296391017140062784101 13220305573315713761772019)
            ·
              refine ⟨19830458359973570642658029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13220305573315713761772019 19830458359973570642658029)
              ·
                refine ⟨7436421884990088990996761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19830458359973570642658029 7436421884990088990996761)
                ·
                  refine ⟨5577316413742566743247571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7436421884990088990996761 5577316413742566743247571)
                  ·
                    refine ⟨8365974620613850114871357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5577316413742566743247571 8365974620613850114871357)
                    ·
                      refine ⟨3137240482730193793076759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8365974620613850114871357 3137240482730193793076759)
                      ·
                        rfl

theorem cell23_6109754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_6109754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109754 prefixEnd_6109754 := by exact prefixLift 6109754
  have htrace : WordTrace (prefixWord ++ tailWord_6109754) baseStart_6109754 baseEnd_6109754 := by
    simpa [prefixWord, tailWord_6109754, baseEnd_6109754] using wordTrace_append hprefix tailTrace_6109754
  have hstable : (prefixWord ++ tailWord_6109754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109754).length < 2 ^ (prefixWord ++ tailWord_6109754).sum := by decide
  have hdescent : baseEnd_6109754 < baseStart_6109754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109758 : List Nat := [4, 2, 1, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_6109758 : Nat := 118140960795 + 6109758 * 2 ^ 59
def prefixEnd_6109758 : Nat := 4983230072969 + 3 ^ 40 * 6109758 * 2
def baseEnd_6109758 : Nat := 3137242536652811777426741

theorem tailTrace_6109758 : CollatzResearch.WordTrace tailWord_6109758 prefixEnd_6109758 3137242536652811777426741 := by
  unfold tailWord_6109758
  simp only [CollatzResearch.WordTrace]
  refine ⟨27855147674924713054641241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148560787599598469624753285 27855147674924713054641241)
  ·
    refine ⟨20891360756193534790980931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27855147674924713054641241 20891360756193534790980931)
    ·
      refine ⟨31337041134290302186471397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20891360756193534790980931 31337041134290302186471397)
      ·
        refine ⟨5875695212679431659963387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31337041134290302186471397 5875695212679431659963387)
        ·
          refine ⟨8813542819019147489945081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5875695212679431659963387 8813542819019147489945081)
          ·
            refine ⟨6610157114264360617458811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8813542819019147489945081 6610157114264360617458811)
            ·
              refine ⟨9915235671396540926188217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6610157114264360617458811 9915235671396540926188217)
              ·
                refine ⟨7436426753547405694641163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9915235671396540926188217 7436426753547405694641163)
                ·
                  refine ⟨11154640130321108541961745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7436426753547405694641163 11154640130321108541961745)
                  ·
                    refine ⟨8365980097740831406471309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11154640130321108541961745 8365980097740831406471309)
                    ·
                      refine ⟨3137242536652811777426741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8365980097740831406471309 3137242536652811777426741)
                      ·
                        rfl

theorem cell23_6109758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_6109758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109758 prefixEnd_6109758 := by exact prefixLift 6109758
  have htrace : WordTrace (prefixWord ++ tailWord_6109758) baseStart_6109758 baseEnd_6109758 := by
    simpa [prefixWord, tailWord_6109758, baseEnd_6109758] using wordTrace_append hprefix tailTrace_6109758
  have hstable : (prefixWord ++ tailWord_6109758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109758).length < 2 ^ (prefixWord ++ tailWord_6109758).sum := by decide
  have hdescent : baseEnd_6109758 < baseStart_6109758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109777 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 3, 4, 2]
def baseStart_6109777 : Nat := 118140960795 + 6109777 * 2 ^ 59
def prefixEnd_6109777 : Nat := 4983230072969 + 3 ^ 40 * 6109777 * 2
def baseEnd_6109777 : Nat := 3137252292785247203089153

theorem tailTrace_6109777 : CollatzResearch.WordTrace tailWord_6109777 prefixEnd_6109777 3137252292785247203089153 := by
  unfold tailWord_6109777
  simp only [CollatzResearch.WordTrace]
  refine ⟨222841874386328870682071585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148561249590885913788047723 222841874386328870682071585)
  ·
    refine ⟨167131405789746653011553689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222841874386328870682071585 167131405789746653011553689)
    ·
      refine ⟨125348554342309989758665267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167131405789746653011553689 125348554342309989758665267)
      ·
        refine ⟨188022831513464984637997901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125348554342309989758665267 188022831513464984637997901)
        ·
          refine ⟨70508561817549369239249213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188022831513464984637997901 70508561817549369239249213)
          ·
            refine ⟨26440710681581013464718455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70508561817549369239249213 26440710681581013464718455)
            ·
              refine ⟨39661066022371520197077683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26440710681581013464718455 39661066022371520197077683)
              ·
                refine ⟨59491599033557280295616525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39661066022371520197077683 59491599033557280295616525)
                ·
                  refine ⟨22309349637583980110856197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59491599033557280295616525 22309349637583980110856197)
                  ·
                    refine ⟨4183003057046996270785537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22309349637583980110856197 4183003057046996270785537)
                    ·
                      refine ⟨3137252292785247203089153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4183003057046996270785537 3137252292785247203089153)
                      ·
                        rfl

theorem cell23_6109777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 4, 2].length) (baseStart_6109777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109777 prefixEnd_6109777 := by exact prefixLift 6109777
  have htrace : WordTrace (prefixWord ++ tailWord_6109777) baseStart_6109777 baseEnd_6109777 := by
    simpa [prefixWord, tailWord_6109777, baseEnd_6109777] using wordTrace_append hprefix tailTrace_6109777
  have hstable : (prefixWord ++ tailWord_6109777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109777).length < 2 ^ (prefixWord ++ tailWord_6109777).sum := by decide
  have hdescent : baseEnd_6109777 < baseStart_6109777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109844 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_6109844 : Nat := 118140960795 + 6109844 * 2 ^ 59
def prefixEnd_6109844 : Nat := 4983230072969 + 3 ^ 40 * 6109844 * 2
def baseEnd_6109844 : Nat := 3137286695989098440951345

theorem tailTrace_6109844 : CollatzResearch.WordTrace tailWord_6109844 prefixEnd_6109844 3137286695989098440951345 := by
  unfold tailWord_6109844
  simp only [CollatzResearch.WordTrace]
  refine ⟨111422159038543070562380293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148562878718057427416507057 111422159038543070562380293)
  ·
    refine ⟨20891654819726825730446305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111422159038543070562380293 20891654819726825730446305)
    ·
      refine ⟨15668741114795119297834729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20891654819726825730446305 15668741114795119297834729)
      ·
        refine ⟨11751555836096339473376047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15668741114795119297834729 11751555836096339473376047)
        ·
          refine ⟨17627333754144509210064071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11751555836096339473376047 17627333754144509210064071)
          ·
            refine ⟨26441000631216763815096107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17627333754144509210064071 26441000631216763815096107)
            ·
              refine ⟨39661500946825145722644161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26441000631216763815096107 39661500946825145722644161)
              ·
                refine ⟨29746125710118859291983121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39661500946825145722644161 29746125710118859291983121)
                ·
                  refine ⟨22309594282589144468987341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29746125710118859291983121 22309594282589144468987341)
                  ·
                    refine ⟨8366097855970929175870253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22309594282589144468987341 8366097855970929175870253)
                    ·
                      refine ⟨3137286695989098440951345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8366097855970929175870253 3137286695989098440951345)
                      ·
                        rfl

theorem cell23_6109844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_6109844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109844 prefixEnd_6109844 := by exact prefixLift 6109844
  have htrace : WordTrace (prefixWord ++ tailWord_6109844) baseStart_6109844 baseEnd_6109844 := by
    simpa [prefixWord, tailWord_6109844, baseEnd_6109844] using wordTrace_append hprefix tailTrace_6109844
  have hstable : (prefixWord ++ tailWord_6109844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109844).length < 2 ^ (prefixWord ++ tailWord_6109844).sum := by decide
  have hdescent : baseEnd_6109844 < baseStart_6109844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109887 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 3]
def baseStart_6109887 : Nat := 118140960795 + 6109887 * 2 ^ 59
def prefixEnd_6109887 : Nat := 4983230072969 + 3 ^ 40 * 6109887 * 2
def baseEnd_6109887 : Nat := 3137308775657241772713647

theorem tailTrace_6109887 : CollatzResearch.WordTrace tailWord_6109887 prefixEnd_6109887 3137308775657241772713647 := by
  unfold tailWord_6109887
  simp only [CollatzResearch.WordTrace]
  refine ⟨222845886415930359468575915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148563924277286906312383943 222845886415930359468575915)
  ·
    refine ⟨334268829623895539202863873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222845886415930359468575915 334268829623895539202863873)
    ·
      refine ⟨250701622217921654402147905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334268829623895539202863873 250701622217921654402147905)
      ·
        refine ⟨188026216663441240801610929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250701622217921654402147905 188026216663441240801610929)
        ·
          refine ⟨141019662497580930601208197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188026216663441240801610929 141019662497580930601208197)
          ·
            refine ⟨26441186718296424487726537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141019662497580930601208197 26441186718296424487726537)
            ·
              refine ⟨19830890038722318365794903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26441186718296424487726537 19830890038722318365794903)
              ·
                refine ⟨29746335058083477548692355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19830890038722318365794903 29746335058083477548692355)
                ·
                  refine ⟨44619502587125216323038533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29746335058083477548692355 44619502587125216323038533)
                  ·
                    refine ⟨8366156735085978060569725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44619502587125216323038533 8366156735085978060569725)
                    ·
                      refine ⟨3137308775657241772713647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8366156735085978060569725 3137308775657241772713647)
                      ·
                        rfl

theorem cell23_6109887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_6109887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109887 prefixEnd_6109887 := by exact prefixLift 6109887
  have htrace : WordTrace (prefixWord ++ tailWord_6109887) baseStart_6109887 baseEnd_6109887 := by
    simpa [prefixWord, tailWord_6109887, baseEnd_6109887] using wordTrace_append hprefix tailTrace_6109887
  have hstable : (prefixWord ++ tailWord_6109887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109887).length < 2 ^ (prefixWord ++ tailWord_6109887).sum := by decide
  have hdescent : baseEnd_6109887 < baseStart_6109887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109920 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 2, 9]
def baseStart_6109920 : Nat := 118140960795 + 6109920 * 2 ^ 59
def prefixEnd_6109920 : Nat := 4983230072969 + 3 ^ 40 * 6109920 * 2
def baseEnd_6109920 : Nat := 1045775240172946714533665

theorem tailTrace_6109920 : CollatzResearch.WordTrace tailWord_6109920 prefixEnd_6109920 1045775240172946714533665 := by
  unfold tailWord_6109920
  simp only [CollatzResearch.WordTrace]
  refine ⟨111423545012405403052263607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148564726683207204069684809 111423545012405403052263607)
  ·
    refine ⟨167135317518608104578395411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111423545012405403052263607 167135317518608104578395411)
    ·
      refine ⟨250702976277912156867593117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167135317518608104578395411 250702976277912156867593117)
      ·
        refine ⟨94013616104217058825347419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250702976277912156867593117 94013616104217058825347419)
        ·
          refine ⟨141020424156325588238021129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94013616104217058825347419 141020424156325588238021129)
          ·
            refine ⟨105765318117244191178515847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141020424156325588238021129 105765318117244191178515847)
            ·
              refine ⟨158647977175866286767773771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105765318117244191178515847 158647977175866286767773771)
              ·
                refine ⟨237971965763799430151660657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158647977175866286767773771 237971965763799430151660657)
                ·
                  refine ⟨178478974322849572613745493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237971965763799430151660657 178478974322849572613745493)
                  ·
                    refine ⟨1045775240172946714533665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 178478974322849572613745493 1045775240172946714533665)
                    ·
                      rfl

theorem cell23_6109920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 9].length) (baseStart_6109920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109920 prefixEnd_6109920 := by exact prefixLift 6109920
  have htrace : WordTrace (prefixWord ++ tailWord_6109920) baseStart_6109920 baseEnd_6109920 := by
    simpa [prefixWord, tailWord_6109920, baseEnd_6109920] using wordTrace_append hprefix tailTrace_6109920
  have hstable : (prefixWord ++ tailWord_6109920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109920).length < 2 ^ (prefixWord ++ tailWord_6109920).sum := by decide
  have hdescent : baseEnd_6109920 < baseStart_6109920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109924 : List Nat := [2, 3, 1, 1, 1, 4, 4, 1, 6]
def baseStart_6109924 : Nat := 118140960795 + 6109924 * 2 ^ 59
def prefixEnd_6109924 : Nat := 4983230072969 + 3 ^ 40 * 6109924 * 2
def baseEnd_6109924 : Nat := 348591974937939791994553

theorem tailTrace_6109924 : CollatzResearch.WordTrace tailWord_6109924 prefixEnd_6109924 348591974937939791994553 := by
  unfold tailWord_6109924
  simp only [CollatzResearch.WordTrace]
  refine ⟨111423617958398157393836413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148564823944530876525115217 111423617958398157393836413)
  ·
    refine ⟨41783856734399309022688655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111423617958398157393836413 41783856734399309022688655)
    ·
      refine ⟨62675785101598963534032983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41783856734399309022688655 62675785101598963534032983)
      ·
        refine ⟨94013677652398445301049475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62675785101598963534032983 94013677652398445301049475)
        ·
          refine ⟨141020516478597667951574213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94013677652398445301049475 141020516478597667951574213)
          ·
            refine ⟨26441346839737062740920165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141020516478597667951574213 26441346839737062740920165)
            ·
              refine ⟨4957752532450699263922531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26441346839737062740920165 4957752532450699263922531)
              ·
                refine ⟨7436628798676048895883797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4957752532450699263922531 7436628798676048895883797)
                ·
                  refine ⟨348591974937939791994553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7436628798676048895883797 348591974937939791994553)
                  ·
                    rfl

theorem cell23_6109924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_6109924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109924 prefixEnd_6109924 := by exact prefixLift 6109924
  have htrace : WordTrace (prefixWord ++ tailWord_6109924) baseStart_6109924 baseEnd_6109924 := by
    simpa [prefixWord, tailWord_6109924, baseEnd_6109924] using wordTrace_append hprefix tailTrace_6109924
  have hstable : (prefixWord ++ tailWord_6109924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109924).length < 2 ^ (prefixWord ++ tailWord_6109924).sum := by decide
  have hdescent : baseEnd_6109924 < baseStart_6109924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109937 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 3, 5]
def baseStart_6109937 : Nat := 118140960795 + 6109937 * 2 ^ 59
def prefixEnd_6109937 : Nat := 4983230072969 + 3 ^ 40 * 6109937 * 2
def baseEnd_6109937 : Nat := 1045778149896655525696139

theorem tailTrace_6109937 : CollatzResearch.WordTrace tailWord_6109937 prefixEnd_6109937 1045778149896655525696139 := by
  unfold tailWord_6109937
  simp only [CollatzResearch.WordTrace]
  refine ⟨222847710065749218007896065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148565140043832812005264043 222847710065749218007896065)
  ·
    refine ⟨167135782549311913505922049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222847710065749218007896065 167135782549311913505922049)
    ·
      refine ⟨125351836911983935129441537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167135782549311913505922049 125351836911983935129441537)
      ·
        refine ⟨94013877683987951347081153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125351836911983935129441537 94013877683987951347081153)
        ·
          refine ⟨70510408262990963510310865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94013877683987951347081153 70510408262990963510310865)
          ·
            refine ⟨52882806197243222632733149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70510408262990963510310865 52882806197243222632733149)
            ·
              refine ⟨19831052323966208487274931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52882806197243222632733149 19831052323966208487274931)
              ·
                refine ⟨29746578485949312730912397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19831052323966208487274931 29746578485949312730912397)
                ·
                  refine ⟨11154966932230992274092149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29746578485949312730912397 11154966932230992274092149)
                  ·
                    refine ⟨1045778149896655525696139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11154966932230992274092149 1045778149896655525696139)
                    ·
                      rfl

theorem cell23_6109937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_6109937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109937 prefixEnd_6109937 := by exact prefixLift 6109937
  have htrace : WordTrace (prefixWord ++ tailWord_6109937) baseStart_6109937 baseEnd_6109937 := by
    simpa [prefixWord, tailWord_6109937, baseEnd_6109937] using wordTrace_append hprefix tailTrace_6109937
  have hstable : (prefixWord ++ tailWord_6109937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109937).length < 2 ^ (prefixWord ++ tailWord_6109937).sum := by decide
  have hdescent : baseEnd_6109937 < baseStart_6109937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109951 : List Nat := [1, 1, 2, 2, 1, 3, 1, 7, 1, 1, 3]
def baseStart_6109951 : Nat := 118140960795 + 6109951 * 2 ^ 59
def prefixEnd_6109951 : Nat := 4983230072969 + 3 ^ 40 * 6109951 * 2
def baseEnd_6109951 : Nat := 3137341638419129522313353

theorem tailTrace_6109951 : CollatzResearch.WordTrace tailWord_6109951 prefixEnd_6109951 3137341638419129522313353 := by
  unfold tailWord_6109951
  simp only [CollatzResearch.WordTrace]
  refine ⟨222848220687698498398905707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148565480458465665599270471 222848220687698498398905707)
  ·
    refine ⟨334272331031547747598358561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222848220687698498398905707 334272331031547747598358561)
    ·
      refine ⟨250704248273660810698768921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334272331031547747598358561 250704248273660810698768921)
      ·
        refine ⟨188028186205245608024076691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250704248273660810698768921 188028186205245608024076691)
        ·
          refine ⟨282042279307868412036115037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188028186205245608024076691 282042279307868412036115037)
          ·
            refine ⟨105765854740450654513543139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282042279307868412036115037 105765854740450654513543139)
            ·
              refine ⟨158648782110675981770314709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105765854740450654513543139 158648782110675981770314709)
              ·
                refine ⟨3718330830718968322741751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 158648782110675981770314709 3718330830718968322741751)
                ·
                  refine ⟨5577496246078452484112627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3718330830718968322741751 5577496246078452484112627)
                  ·
                    refine ⟨8366244369117678726168941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5577496246078452484112627 8366244369117678726168941)
                    ·
                      refine ⟨3137341638419129522313353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8366244369117678726168941 3137341638419129522313353)
                      ·
                        rfl

theorem cell23_6109951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 1, 1, 3].length) (baseStart_6109951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109951 prefixEnd_6109951 := by exact prefixLift 6109951
  have htrace : WordTrace (prefixWord ++ tailWord_6109951) baseStart_6109951 baseEnd_6109951 := by
    simpa [prefixWord, tailWord_6109951, baseEnd_6109951] using wordTrace_append hprefix tailTrace_6109951
  have hstable : (prefixWord ++ tailWord_6109951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109951).length < 2 ^ (prefixWord ++ tailWord_6109951).sum := by decide
  have hdescent : baseEnd_6109951 < baseStart_6109951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109984 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 1, 6]
def baseStart_6109984 : Nat := 118140960795 + 6109984 * 2 ^ 59
def prefixEnd_6109984 : Nat := 4983230072969 + 3 ^ 40 * 6109984 * 2
def baseEnd_6109984 : Nat := 1045786194426909297733567

theorem tailTrace_6109984 : CollatzResearch.WordTrace tailWord_6109984 prefixEnd_6109984 1045786194426909297733567 := by
  unfold tailWord_6109984
  simp only [CollatzResearch.WordTrace]
  refine ⟨111424712148289472517428503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148566282864385963356571337 111424712148289472517428503)
  ·
    refine ⟨167137068222434208776142755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111424712148289472517428503 167137068222434208776142755)
    ·
      refine ⟨250705602333651313164214133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167137068222434208776142755 250705602333651313164214133)
      ·
        refine ⟨23503650218779810609145075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 250705602333651313164214133 23503650218779810609145075)
        ·
          refine ⟨35255475328169715913717613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23503650218779810609145075 35255475328169715913717613)
          ·
            refine ⟨13220803248063643467644105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35255475328169715913717613 13220803248063643467644105)
            ·
              refine ⟨9915602436047732600733079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13220803248063643467644105 9915602436047732600733079)
              ·
                refine ⟨14873403654071598901099619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9915602436047732600733079 14873403654071598901099619)
                ·
                  refine ⟨22310105481107398351649429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14873403654071598901099619 22310105481107398351649429)
                  ·
                    refine ⟨1045786194426909297733567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22310105481107398351649429 1045786194426909297733567)
                    ·
                      rfl

theorem cell23_6109984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 1, 6].length) (baseStart_6109984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109984 prefixEnd_6109984 := by exact prefixLift 6109984
  have htrace : WordTrace (prefixWord ++ tailWord_6109984) baseStart_6109984 baseEnd_6109984 := by
    simpa [prefixWord, tailWord_6109984, baseEnd_6109984] using wordTrace_append hprefix tailTrace_6109984
  have hstable : (prefixWord ++ tailWord_6109984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109984).length < 2 ^ (prefixWord ++ tailWord_6109984).sum := by decide
  have hdescent : baseEnd_6109984 < baseStart_6109984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110014 : List Nat := [4, 2, 1, 2, 3, 1, 10]
def baseStart_6110014 : Nat := 118140960795 + 6110014 * 2 ^ 59
def prefixEnd_6110014 : Nat := 4983230072969 + 3 ^ 40 * 6110014 * 2
def baseEnd_6110014 : Nat := 38733012193831639207723

theorem tailTrace_6110014 : CollatzResearch.WordTrace tailWord_6110014 prefixEnd_6110014 38733012193831639207723 := by
  unfold tailWord_6110014
  simp only [CollatzResearch.WordTrace]
  refine ⟨27856314810808782519806137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148567012324313506772299397 27856314810808782519806137)
  ·
    refine ⟨20892236108106586889854603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27856314810808782519806137 20892236108106586889854603)
    ·
      refine ⟨31338354162159880334781905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20892236108106586889854603 31338354162159880334781905)
      ·
        refine ⟨23503765621619910251086429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31338354162159880334781905 23503765621619910251086429)
        ·
          refine ⟨8813912108107466344157411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23503765621619910251086429 8813912108107466344157411)
          ·
            refine ⟨13220868162161199516236117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8813912108107466344157411 13220868162161199516236117)
            ·
              refine ⟨38733012193831639207723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13220868162161199516236117 38733012193831639207723)
              ·
                rfl

theorem cell23_6110014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 10].length) (baseStart_6110014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110014 prefixEnd_6110014 := by exact prefixLift 6110014
  have htrace : WordTrace (prefixWord ++ tailWord_6110014) baseStart_6110014 baseEnd_6110014 := by
    simpa [prefixWord, tailWord_6110014, baseEnd_6110014] using wordTrace_append hprefix tailTrace_6110014
  have hstable : (prefixWord ++ tailWord_6110014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110014).length < 2 ^ (prefixWord ++ tailWord_6110014).sum := by decide
  have hdescent : baseEnd_6110014 < baseStart_6110014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110041 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 1, 3, 3]
def baseStart_6110041 : Nat := 118140960795 + 6110041 * 2 ^ 59
def prefixEnd_6110041 : Nat := 4983230072969 + 3 ^ 40 * 6110041 * 2
def baseEnd_6110041 : Nat := 3137387851678034170187939

theorem tailTrace_6110041 : CollatzResearch.WordTrace tailWord_6110041 prefixEnd_6110041 3137387851678034170187939 := by
  unfold tailWord_6110041
  simp only [CollatzResearch.WordTrace]
  refine ⟨222851503257372443769681977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148567668838248295846454651 222851503257372443769681977)
  ·
    refine ⟨167138627443029332827261483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222851503257372443769681977 167138627443029332827261483)
    ·
      refine ⟨250707941164543999240892225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167138627443029332827261483 250707941164543999240892225)
      ·
        refine ⟨188030955873407999430669169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250707941164543999240892225 188030955873407999430669169)
        ·
          refine ⟨141023216905055999573001877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188030955873407999430669169 141023216905055999573001877)
          ·
            refine ⟨6610463292424499979984463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 141023216905055999573001877 6610463292424499979984463)
            ·
              refine ⟨9915694938636749969976695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6610463292424499979984463 9915694938636749969976695)
              ·
                refine ⟨14873542407955124954965043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9915694938636749969976695 14873542407955124954965043)
                ·
                  refine ⟨22310313611932687432447565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14873542407955124954965043 22310313611932687432447565)
                  ·
                    refine ⟨8366367604474757787167837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22310313611932687432447565 8366367604474757787167837)
                    ·
                      refine ⟨3137387851678034170187939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8366367604474757787167837 3137387851678034170187939)
                      ·
                        rfl

theorem cell23_6110041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_6110041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110041 prefixEnd_6110041 := by exact prefixLift 6110041
  have htrace : WordTrace (prefixWord ++ tailWord_6110041) baseStart_6110041 baseEnd_6110041 := by
    simpa [prefixWord, tailWord_6110041, baseEnd_6110041] using wordTrace_append hprefix tailTrace_6110041
  have hstable : (prefixWord ++ tailWord_6110041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110041).length < 2 ^ (prefixWord ++ tailWord_6110041).sum := by decide
  have hdescent : baseEnd_6110041 < baseStart_6110041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110067 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 5]
def baseStart_6110067 : Nat := 118140960795 + 6110067 * 2 ^ 59
def prefixEnd_6110067 : Nat := 4983230072969 + 3 ^ 40 * 6110067 * 2
def baseEnd_6110067 : Nat := 3137401202175051068462819

theorem tailTrace_6110067 : CollatzResearch.WordTrace tailWord_6110067 prefixEnd_6110067 3137401202175051068462819 := by
  unfold tailWord_6110067
  simp only [CollatzResearch.WordTrace]
  refine ⟨222852451555278250210128455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148568301036852166806752303 222852451555278250210128455)
  ·
    refine ⟨334278677332917375315192683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222852451555278250210128455 334278677332917375315192683)
    ·
      refine ⟨501418015999376062972789025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334278677332917375315192683 501418015999376062972789025)
      ·
        refine ⟨376063511999532047229591769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501418015999376062972789025 376063511999532047229591769)
        ·
          refine ⟨282047633999649035422193827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376063511999532047229591769 282047633999649035422193827)
          ·
            refine ⟨423071450999473553133290741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282047633999649035422193827 423071450999473553133290741)
            ·
              refine ⟨39662948531200645606246007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 423071450999473553133290741 39662948531200645606246007)
              ·
                refine ⟨59494422796800968409369011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39662948531200645606246007 59494422796800968409369011)
                ·
                  refine ⟨89241634195201452614053517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59494422796800968409369011 89241634195201452614053517)
                  ·
                    refine ⟨33465612823200544730270069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89241634195201452614053517 33465612823200544730270069)
                    ·
                      refine ⟨3137401202175051068462819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33465612823200544730270069 3137401202175051068462819)
                      ·
                        rfl

theorem cell23_6110067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_6110067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110067 prefixEnd_6110067 := by exact prefixLift 6110067
  have htrace : WordTrace (prefixWord ++ tailWord_6110067) baseStart_6110067 baseEnd_6110067 := by
    simpa [prefixWord, tailWord_6110067, baseEnd_6110067] using wordTrace_append hprefix tailTrace_6110067
  have hstable : (prefixWord ++ tailWord_6110067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110067).length < 2 ^ (prefixWord ++ tailWord_6110067).sum := by decide
  have hdescent : baseEnd_6110067 < baseStart_6110067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110084 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_6110084 : Nat := 118140960795 + 6110084 * 2 ^ 59
def prefixEnd_6110084 : Nat := 4983230072969 + 3 ^ 40 * 6110084 * 2
def baseEnd_6110084 : Nat := 3137409931346177501950241

theorem tailTrace_6110084 : CollatzResearch.WordTrace tailWord_6110084 prefixEnd_6110084 3137409931346177501950241 := by
  unfold tailWord_6110084
  simp only [CollatzResearch.WordTrace]
  refine ⟨111426535798108331056748653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148568714397477774742331537 111426535798108331056748653)
  ·
    refine ⟨41784950924290624146280745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111426535798108331056748653 41784950924290624146280745)
    ·
      refine ⟨31338713193217968109710559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41784950924290624146280745 31338713193217968109710559)
      ·
        refine ⟨47008069789826952164565839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31338713193217968109710559 47008069789826952164565839)
        ·
          refine ⟨70512104684740428246848759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47008069789826952164565839 70512104684740428246848759)
          ·
            refine ⟨105768157027110642370273139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70512104684740428246848759 105768157027110642370273139)
            ·
              refine ⟨158652235540665963555409709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105768157027110642370273139 158652235540665963555409709)
              ·
                refine ⟨59494588327749736333278641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158652235540665963555409709 59494588327749736333278641)
                ·
                  refine ⟨44620941245812302249958981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59494588327749736333278641 44620941245812302249958981)
                  ·
                    refine ⟨8366426483589806671867309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44620941245812302249958981 8366426483589806671867309)
                    ·
                      refine ⟨3137409931346177501950241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8366426483589806671867309 3137409931346177501950241)
                      ·
                        rfl

theorem cell23_6110084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_6110084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110084 prefixEnd_6110084 := by exact prefixLift 6110084
  have htrace : WordTrace (prefixWord ++ tailWord_6110084) baseStart_6110084 baseEnd_6110084 := by
    simpa [prefixWord, tailWord_6110084, baseEnd_6110084] using wordTrace_append hprefix tailTrace_6110084
  have hstable : (prefixWord ++ tailWord_6110084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110084).length < 2 ^ (prefixWord ++ tailWord_6110084).sum := by decide
  have hdescent : baseEnd_6110084 < baseStart_6110084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110102 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_6110102 : Nat := 118140960795 + 6110102 * 2 ^ 59
def prefixEnd_6110102 : Nat := 4983230072969 + 3 ^ 40 * 6110102 * 2
def baseEnd_6110102 : Nat := 3137419173997958431525159

theorem tailTrace_6110102 : CollatzResearch.WordTrace tailWord_6110102 prefixEnd_6110102 3137419173997958431525159 := by
  unfold tailWord_6110102
  simp only [CollatzResearch.WordTrace]
  refine ⟨13928358006884465699228285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148569152073434300791768373 13928358006884465699228285)
  ·
    refine ⟨5223134252581674637210607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13928358006884465699228285 5223134252581674637210607)
    ·
      refine ⟨7834701378872511955815911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5223134252581674637210607 7834701378872511955815911)
      ·
        refine ⟨11752052068308767933723867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7834701378872511955815911 11752052068308767933723867)
        ·
          refine ⟨17628078102463151900585801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11752052068308767933723867 17628078102463151900585801)
          ·
            refine ⟨13221058576847363925439351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17628078102463151900585801 13221058576847363925439351)
            ·
              refine ⟨19831587865271045888159027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13221058576847363925439351 19831587865271045888159027)
              ·
                refine ⟨29747381797906568832238541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19831587865271045888159027 29747381797906568832238541)
                ·
                  refine ⟨11155268174214963312089453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29747381797906568832238541 11155268174214963312089453)
                  ·
                    refine ⟨4183225565330611242033545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11155268174214963312089453 4183225565330611242033545)
                    ·
                      refine ⟨3137419173997958431525159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4183225565330611242033545 3137419173997958431525159)
                      ·
                        rfl

theorem cell23_6110102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_6110102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110102 prefixEnd_6110102 := by exact prefixLift 6110102
  have htrace : WordTrace (prefixWord ++ tailWord_6110102) baseStart_6110102 baseEnd_6110102 := by
    simpa [prefixWord, tailWord_6110102, baseEnd_6110102] using wordTrace_append hprefix tailTrace_6110102
  have hstable : (prefixWord ++ tailWord_6110102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110102).length < 2 ^ (prefixWord ++ tailWord_6110102).sum := by decide
  have hdescent : baseEnd_6110102 < baseStart_6110102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110132 : List Nat := [2, 5, 2, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_6110132 : Nat := 118140960795 + 6110132 * 2 ^ 59
def prefixEnd_6110132 : Nat := 4983230072969 + 3 ^ 40 * 6110132 * 2
def baseEnd_6110132 : Nat := 3137434578417593314150021

theorem tailTrace_6110132 : CollatzResearch.WordTrace tailWord_6110132 prefixEnd_6110132 3137434578417593314150021 := by
  unfold tailWord_6110132
  simp only [CollatzResearch.WordTrace]
  refine ⟨111427411150021383155622325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148569881533361844207496433 111427411150021383155622325)
  ·
    refine ⟨10446319795314504670839593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111427411150021383155622325 10446319795314504670839593)
    ·
      refine ⟨7834739846485878503129695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10446319795314504670839593 7834739846485878503129695)
      ·
        refine ⟨11752109769728817754694543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7834739846485878503129695 11752109769728817754694543)
        ·
          refine ⟨17628164654593226632041815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11752109769728817754694543 17628164654593226632041815)
          ·
            refine ⟨26442246981889839948062723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17628164654593226632041815 26442246981889839948062723)
            ·
              refine ⟨39663370472834759922094085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26442246981889839948062723 39663370472834759922094085)
              ·
                refine ⟨7436881963656517485392641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39663370472834759922094085 7436881963656517485392641)
                ·
                  refine ⟨5577661472742388114044481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7436881963656517485392641 5577661472742388114044481)
                  ·
                    refine ⟨4183246104556791085533361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5577661472742388114044481 4183246104556791085533361)
                    ·
                      refine ⟨3137434578417593314150021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4183246104556791085533361 3137434578417593314150021)
                      ·
                        rfl

theorem cell23_6110132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_6110132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110132 prefixEnd_6110132 := by exact prefixLift 6110132
  have htrace : WordTrace (prefixWord ++ tailWord_6110132) baseStart_6110132 baseEnd_6110132 := by
    simpa [prefixWord, tailWord_6110132, baseEnd_6110132] using wordTrace_append hprefix tailTrace_6110132
  have hstable : (prefixWord ++ tailWord_6110132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110132).length < 2 ^ (prefixWord ++ tailWord_6110132).sum := by decide
  have hdescent : baseEnd_6110132 < baseStart_6110132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110144 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 5]
def baseStart_6110144 : Nat := 118140960795 + 6110144 * 2 ^ 59
def prefixEnd_6110144 : Nat := 4983230072969 + 3 ^ 40 * 6110144 * 2
def baseEnd_6110144 : Nat := 3137440740185447267199965

theorem tailTrace_6110144 : CollatzResearch.WordTrace tailWord_6110144 prefixEnd_6110144 3137440740185447267199965 := by
  unfold tailWord_6110144
  simp only [CollatzResearch.WordTrace]
  refine ⟨111427629987999646180340743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148570173317332861573787657 111427629987999646180340743)
  ·
    refine ⟨167141444981999469270511115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111427629987999646180340743 167141444981999469270511115)
    ·
      refine ⟨250712167472999203905766673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167141444981999469270511115 250712167472999203905766673)
      ·
        refine ⟨188034125604749402929325005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250712167472999203905766673 188034125604749402929325005)
        ·
          refine ⟨70512797101781026098496877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188034125604749402929325005 70512797101781026098496877)
          ·
            refine ⟨26442298913167884786936329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70512797101781026098496877 26442298913167884786936329)
            ·
              refine ⟨19831724184875913590202247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26442298913167884786936329 19831724184875913590202247)
              ·
                refine ⟨29747586277313870385303371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19831724184875913590202247 29747586277313870385303371)
                ·
                  refine ⟨44621379415970805577955057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29747586277313870385303371 44621379415970805577955057)
                  ·
                    refine ⟨33466034561978104183466293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44621379415970805577955057 33466034561978104183466293)
                    ·
                      refine ⟨3137440740185447267199965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33466034561978104183466293 3137440740185447267199965)
                      ·
                        rfl

theorem cell23_6110144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_6110144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110144 prefixEnd_6110144 := by exact prefixLift 6110144
  have htrace : WordTrace (prefixWord ++ tailWord_6110144) baseStart_6110144 baseEnd_6110144 := by
    simpa [prefixWord, tailWord_6110144, baseEnd_6110144] using wordTrace_append hprefix tailTrace_6110144
  have hstable : (prefixWord ++ tailWord_6110144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110144).length < 2 ^ (prefixWord ++ tailWord_6110144).sum := by decide
  have hdescent : baseEnd_6110144 < baseStart_6110144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110154 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_6110154 : Nat := 118140960795 + 6110154 * 2 ^ 59
def prefixEnd_6110154 : Nat := 4983230072969 + 3 ^ 40 * 6110154 * 2
def baseEnd_6110154 : Nat := 3137445874991992228074919

theorem tailTrace_6110154 : CollatzResearch.WordTrace tailWord_6110154 prefixEnd_6110154 3137445874991992228074919 := by
  unfold tailWord_6110154
  simp only [CollatzResearch.WordTrace]
  refine ⟨55713906176490766017136379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148570416470642042712363677 55713906176490766017136379)
  ·
    refine ⟨83570859264736149025704569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55713906176490766017136379 83570859264736149025704569)
    ·
      refine ⟨62678144448552111769278427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83570859264736149025704569 62678144448552111769278427)
      ·
        refine ⟨94017216672828167653917641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62678144448552111769278427 94017216672828167653917641)
        ·
          refine ⟨70512912504621125740438231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94017216672828167653917641 70512912504621125740438231)
          ·
            refine ⟨105769368756931688610657347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70512912504621125740438231 105769368756931688610657347)
            ·
              refine ⟨158654053135397532915986021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105769368756931688610657347 158654053135397532915986021)
              ·
                refine ⟨29747634962887037421747379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158654053135397532915986021 29747634962887037421747379)
                ·
                  refine ⟨44621452444330556132621069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29747634962887037421747379 44621452444330556132621069)
                  ·
                    refine ⟨16733044666623958549732901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44621452444330556132621069 16733044666623958549732901)
                    ·
                      refine ⟨3137445874991992228074919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16733044666623958549732901 3137445874991992228074919)
                      ·
                        rfl

theorem cell23_6110154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_6110154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110154 prefixEnd_6110154 := by exact prefixLift 6110154
  have htrace : WordTrace (prefixWord ++ tailWord_6110154) baseStart_6110154 baseEnd_6110154 := by
    simpa [prefixWord, tailWord_6110154, baseEnd_6110154] using wordTrace_append hprefix tailTrace_6110154
  have hstable : (prefixWord ++ tailWord_6110154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110154).length < 2 ^ (prefixWord ++ tailWord_6110154).sum := by decide
  have hdescent : baseEnd_6110154 < baseStart_6110154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110184 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_6110184 : Nat := 118140960795 + 6110184 * 2 ^ 59
def prefixEnd_6110184 : Nat := 4983230072969 + 3 ^ 40 * 6110184 * 2
def baseEnd_6110184 : Nat := 3137461279411627110699781

theorem tailTrace_6110184 : CollatzResearch.WordTrace tailWord_6110184 prefixEnd_6110184 3137461279411627110699781 := by
  unfold tailWord_6110184
  simp only [CollatzResearch.WordTrace]
  refine ⟨111428359447927189596068803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148571145930569586128091737 111428359447927189596068803)
  ·
    refine ⟨167142539171890784394103205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111428359447927189596068803 167142539171890784394103205)
    ·
      refine ⟨31339226094729522073894351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167142539171890784394103205 31339226094729522073894351)
      ·
        refine ⟨47008839142094283110841527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31339226094729522073894351 47008839142094283110841527)
        ·
          refine ⟨70513258713141424666262291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47008839142094283110841527 70513258713141424666262291)
          ·
            refine ⟨105769888069712136999393437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70513258713141424666262291 105769888069712136999393437)
            ·
              refine ⟨39663708026142051374772539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105769888069712136999393437 39663708026142051374772539)
              ·
                refine ⟨59495562039213077062158809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39663708026142051374772539 59495562039213077062158809)
                ·
                  refine ⟨44621671529409807796619107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59495562039213077062158809 44621671529409807796619107)
                  ·
                    refine ⟨66932507294114711694928661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44621671529409807796619107 66932507294114711694928661)
                    ·
                      refine ⟨3137461279411627110699781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66932507294114711694928661 3137461279411627110699781)
                      ·
                        rfl

theorem cell23_6110184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_6110184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110184 prefixEnd_6110184 := by exact prefixLift 6110184
  have htrace : WordTrace (prefixWord ++ tailWord_6110184) baseStart_6110184 baseEnd_6110184 := by
    simpa [prefixWord, tailWord_6110184, baseEnd_6110184] using wordTrace_append hprefix tailTrace_6110184
  have hstable : (prefixWord ++ tailWord_6110184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110184).length < 2 ^ (prefixWord ++ tailWord_6110184).sum := by decide
  have hdescent : baseEnd_6110184 < baseStart_6110184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110198 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_6110198 : Nat := 118140960795 + 6110198 * 2 ^ 59
def prefixEnd_6110198 : Nat := 4983230072969 + 3 ^ 40 * 6110198 * 2
def baseEnd_6110198 : Nat := 1045822822713596685308239

theorem tailTrace_6110198 : CollatzResearch.WordTrace tailWord_6110198 prefixEnd_6110198 1045822822713596685308239 := by
  unfold tailWord_6110198
  simp only [CollatzResearch.WordTrace]
  refine ⟨13928576844862728723946703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148571486345202439722098165 13928576844862728723946703)
  ·
    refine ⟨20892865267294093085920055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13928576844862728723946703 20892865267294093085920055)
    ·
      refine ⟨31339297900941139628880083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20892865267294093085920055 31339297900941139628880083)
      ·
        refine ⟨47008946851411709443320125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31339297900941139628880083 47008946851411709443320125)
        ·
          refine ⟨17628355069279391041245047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47008946851411709443320125 17628355069279391041245047)
          ·
            refine ⟨26442532603919086561867571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17628355069279391041245047 26442532603919086561867571)
            ·
              refine ⟨39663798905878629842801357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26442532603919086561867571 39663798905878629842801357)
              ·
                refine ⟨14873924589704486191050509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39663798905878629842801357 14873924589704486191050509)
                ·
                  refine ⟨5577721721139182321643941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14873924589704486191050509 5577721721139182321643941)
                  ·
                    refine ⟨1045822822713596685308239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5577721721139182321643941 1045822822713596685308239)
                    ·
                      rfl

theorem cell23_6110198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_6110198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110198 prefixEnd_6110198 := by exact prefixLift 6110198
  have htrace : WordTrace (prefixWord ++ tailWord_6110198) baseStart_6110198 baseEnd_6110198 := by
    simpa [prefixWord, tailWord_6110198, baseEnd_6110198] using wordTrace_append hprefix tailTrace_6110198
  have hstable : (prefixWord ++ tailWord_6110198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110198).length < 2 ^ (prefixWord ++ tailWord_6110198).sum := by decide
  have hdescent : baseEnd_6110198 < baseStart_6110198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110261 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_6110261 : Nat := 118140960795 + 6110261 * 2 ^ 59
def prefixEnd_6110261 : Nat := 4983230072969 + 3 ^ 40 * 6110261 * 2
def baseEnd_6110261 : Nat := 3137500817422023309436927

theorem tailTrace_6110261 : CollatzResearch.WordTrace tailWord_6110261 prefixEnd_6110261 3137500817422023309436927 := by
  unfold tailWord_6110261
  simp only [CollatzResearch.WordTrace]
  refine ⟨222859527316575421342690637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148573018211050280895127091 222859527316575421342690637)
  ·
    refine ⟨83572322743715783003508989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222859527316575421342690637 83572322743715783003508989)
    ·
      refine ⟨31339621028893418626315871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83572322743715783003508989 31339621028893418626315871)
      ·
        refine ⟨47009431543340127939473807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31339621028893418626315871 47009431543340127939473807)
        ·
          refine ⟨70514147315010191909210711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47009431543340127939473807 70514147315010191909210711)
          ·
            refine ⟨105771220972515287863816067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70514147315010191909210711 105771220972515287863816067)
            ·
              refine ⟨158656831458772931795724101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105771220972515287863816067 158656831458772931795724101)
              ·
                refine ⟨29748155898519924711698269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158656831458772931795724101 29748155898519924711698269)
                ·
                  refine ⟨11155558461944971766886851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29748155898519924711698269 11155558461944971766886851)
                  ·
                    refine ⟨16733337692917457650330277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11155558461944971766886851 16733337692917457650330277)
                    ·
                      refine ⟨3137500817422023309436927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16733337692917457650330277 3137500817422023309436927)
                      ·
                        rfl

theorem cell23_6110261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_6110261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110261 prefixEnd_6110261 := by exact prefixLift 6110261
  have htrace : WordTrace (prefixWord ++ tailWord_6110261) baseStart_6110261 baseEnd_6110261 := by
    simpa [prefixWord, tailWord_6110261, baseEnd_6110261] using wordTrace_append hprefix tailTrace_6110261
  have hstable : (prefixWord ++ tailWord_6110261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110261).length < 2 ^ (prefixWord ++ tailWord_6110261).sum := by decide
  have hdescent : baseEnd_6110261 < baseStart_6110261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110301 : List Nat := [1, 4, 4, 1, 13]
def baseStart_6110301 : Nat := 118140960795 + 6110301 * 2 ^ 59
def prefixEnd_6110301 : Nat := 4983230072969 + 3 ^ 40 * 6110301 * 2
def baseEnd_6110301 : Nat := 4303870173728673735167

theorem tailTrace_6110301 : CollatzResearch.WordTrace tailWord_6110301 prefixEnd_6110301 4303870173728673735167 := by
  unfold tailWord_6110301
  simp only [CollatzResearch.WordTrace]
  refine ⟨222860986236430508174146757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148573990824287005449431171 222860986236430508174146757)
  ·
    refine ⟨41786434919330720282652517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222860986236430508174146757 41786434919330720282652517)
    ·
      refine ⟨7834956547374510052997347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41786434919330720282652517 7834956547374510052997347)
      ·
        refine ⟨11752434821061765079496021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7834956547374510052997347 11752434821061765079496021)
        ·
          refine ⟨4303870173728673735167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 11752434821061765079496021 4303870173728673735167)
          ·
            rfl

theorem cell23_6110301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 13].length) (baseStart_6110301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110301 prefixEnd_6110301 := by exact prefixLift 6110301
  have htrace : WordTrace (prefixWord ++ tailWord_6110301) baseStart_6110301 baseEnd_6110301 := by
    simpa [prefixWord, tailWord_6110301, baseEnd_6110301] using wordTrace_append hprefix tailTrace_6110301
  have hstable : (prefixWord ++ tailWord_6110301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110301).length < 2 ^ (prefixWord ++ tailWord_6110301).sum := by decide
  have hdescent : baseEnd_6110301 < baseStart_6110301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110306 : List Nat := [3, 3, 2, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_6110306 : Nat := 118140960795 + 6110306 * 2 ^ 59
def prefixEnd_6110306 : Nat := 4983230072969 + 3 ^ 40 * 6110306 * 2
def baseEnd_6110306 : Nat := 3137523924051475633374221

theorem tailTrace_6110306 : CollatzResearch.WordTrace tailWord_6110306 prefixEnd_6110306 3137523924051475633374221 := by
  unfold tailWord_6110306
  simp only [CollatzResearch.WordTrace]
  refine ⟨55715292150353098507019693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148574112400941596018719181 55715292150353098507019693)
  ·
    refine ⟨20893234556382411940132385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55715292150353098507019693 20893234556382411940132385)
    ·
      refine ⟨15669925917286808955099289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20893234556382411940132385 15669925917286808955099289)
      ·
        refine ⟨11752444437965106716324467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15669925917286808955099289 11752444437965106716324467)
        ·
          refine ⟨17628666656947660074486701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11752444437965106716324467 17628666656947660074486701)
          ·
            refine ⟨6610749996355372527932513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17628666656947660074486701 6610749996355372527932513)
            ·
              refine ⟨4958062497266529395949385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6610749996355372527932513 4958062497266529395949385)
              ·
                refine ⟨3718546872949897046962039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4958062497266529395949385 3718546872949897046962039)
                ·
                  refine ⟨5577820309424845570443059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3718546872949897046962039 5577820309424845570443059)
                  ·
                    refine ⟨8366730464137268355664589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5577820309424845570443059 8366730464137268355664589)
                    ·
                      refine ⟨3137523924051475633374221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8366730464137268355664589 3137523924051475633374221)
                      ·
                        rfl

theorem cell23_6110306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_6110306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110306 prefixEnd_6110306 := by exact prefixLift 6110306
  have htrace : WordTrace (prefixWord ++ tailWord_6110306) baseStart_6110306 baseEnd_6110306 := by
    simpa [prefixWord, tailWord_6110306, baseEnd_6110306] using wordTrace_append hprefix tailTrace_6110306
  have hstable : (prefixWord ++ tailWord_6110306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110306).length < 2 ^ (prefixWord ++ tailWord_6110306).sum := by decide
  have hdescent : baseEnd_6110306 < baseStart_6110306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110318 : List Nat := [4, 1, 2, 2, 1, 4, 1, 8]
def baseStart_6110318 : Nat := 118140960795 + 6110318 * 2 ^ 59
def prefixEnd_6110318 : Nat := 4983230072969 + 3 ^ 40 * 6110318 * 2
def baseEnd_6110318 : Nat := 116204817993308503200895

theorem tailTrace_6110318 : CollatzResearch.WordTrace tailWord_6110318 prefixEnd_6110318 116204817993308503200895 := by
  unfold tailWord_6110318
  simp only [CollatzResearch.WordTrace]
  refine ⟨27857700784671115009689451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148574404184912613385010405 27857700784671115009689451)
  ·
    refine ⟨41786551177006672514534177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27857700784671115009689451 41786551177006672514534177)
    ·
      refine ⟨31339913382755004385900633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41786551177006672514534177 31339913382755004385900633)
      ·
        refine ⟨23504935037066253289425475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31339913382755004385900633 23504935037066253289425475)
        ·
          refine ⟨35257402555599379934138213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23504935037066253289425475 35257402555599379934138213)
          ·
            refine ⟨6610762979174883737650915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35257402555599379934138213 6610762979174883737650915)
            ·
              refine ⟨9916144468762325606476373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6610762979174883737650915 9916144468762325606476373)
              ·
                refine ⟨116204817993308503200895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9916144468762325606476373 116204817993308503200895)
                ·
                  rfl

theorem cell23_6110318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 8].length) (baseStart_6110318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110318 prefixEnd_6110318 := by exact prefixLift 6110318
  have htrace : WordTrace (prefixWord ++ tailWord_6110318) baseStart_6110318 baseEnd_6110318 := by
    simpa [prefixWord, tailWord_6110318, baseEnd_6110318] using wordTrace_append hprefix tailTrace_6110318
  have hstable : (prefixWord ++ tailWord_6110318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110318).length < 2 ^ (prefixWord ++ tailWord_6110318).sum := by decide
  have hdescent : baseEnd_6110318 < baseStart_6110318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110362 : List Nat := [3, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3]
def baseStart_6110362 : Nat := 118140960795 + 6110362 * 2 ^ 59
def prefixEnd_6110362 : Nat := 4983230072969 + 3 ^ 40 * 6110362 * 2
def baseEnd_6110362 : Nat := 3137552678968127414273963

theorem tailTrace_6110362 : CollatzResearch.WordTrace tailWord_6110362 prefixEnd_6110362 3137552678968127414273963 := by
  unfold tailWord_6110362
  simp only [CollatzResearch.WordTrace]
  refine ⟨55715802772302378898029335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148575474059473010394744893 55715802772302378898029335)
  ·
    refine ⟨83573704158453568347044003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55715802772302378898029335 83573704158453568347044003)
    ·
      refine ⟨125360556237680352520566005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83573704158453568347044003 125360556237680352520566005)
      ·
        refine ⟨11752552147282533048803063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125360556237680352520566005 11752552147282533048803063)
        ·
          refine ⟨17628828220923799573204595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11752552147282533048803063 17628828220923799573204595)
          ·
            refine ⟨26443242331385699359806893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17628828220923799573204595 26443242331385699359806893)
            ·
              refine ⟨9916215874269637259927585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26443242331385699359806893 9916215874269637259927585)
              ·
                refine ⟨7437161905702227944945689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9916215874269637259927585 7437161905702227944945689)
                ·
                  refine ⟨5577871429276670958709267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7437161905702227944945689 5577871429276670958709267)
                  ·
                    refine ⟨8366807143915006438063901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5577871429276670958709267 8366807143915006438063901)
                    ·
                      refine ⟨3137552678968127414273963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8366807143915006438063901 3137552678968127414273963)
                      ·
                        rfl

theorem cell23_6110362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_6110362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110362 prefixEnd_6110362 := by exact prefixLift 6110362
  have htrace : WordTrace (prefixWord ++ tailWord_6110362) baseStart_6110362 baseEnd_6110362 := by
    simpa [prefixWord, tailWord_6110362, baseEnd_6110362] using wordTrace_append hprefix tailTrace_6110362
  have hstable : (prefixWord ++ tailWord_6110362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110362).length < 2 ^ (prefixWord ++ tailWord_6110362).sum := by decide
  have hdescent : baseEnd_6110362 < baseStart_6110362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110371 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 3]
def baseStart_6110371 : Nat := 118140960795 + 6110371 * 2 ^ 59
def prefixEnd_6110371 : Nat := 4983230072969 + 3 ^ 40 * 6110371 * 2
def baseEnd_6110371 : Nat := 3137557300294017879061421

theorem tailTrace_6110371 : CollatzResearch.WordTrace tailWord_6110371 prefixEnd_6110371 3137557300294017879061421 := by
  unfold tailWord_6110371
  simp only [CollatzResearch.WordTrace]
  refine ⟨222863539346176910129194967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148575692897451273419463311 222863539346176910129194967)
  ·
    refine ⟨334295309019265365193792451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222863539346176910129194967 334295309019265365193792451)
    ·
      refine ⟨501442963528898047790688677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334295309019265365193792451 501442963528898047790688677)
      ·
        refine ⟨94020555661668383960754127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 501442963528898047790688677 94020555661668383960754127)
        ·
          refine ⟨141030833492502575941131191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94020555661668383960754127 141030833492502575941131191)
          ·
            refine ⟨211546250238753863911696787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141030833492502575941131191 211546250238753863911696787)
            ·
              refine ⟨317319375358130795867545181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211546250238753863911696787 317319375358130795867545181)
              ·
                refine ⟨118994765759299048450329443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317319375358130795867545181 118994765759299048450329443)
                ·
                  refine ⟨178492148638948572675494165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118994765759299048450329443 178492148638948572675494165)
                  ·
                    refine ⟨8366819467450714344163789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 178492148638948572675494165 8366819467450714344163789)
                    ·
                      refine ⟨3137557300294017879061421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8366819467450714344163789 3137557300294017879061421)
                      ·
                        rfl

theorem cell23_6110371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_6110371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110371 prefixEnd_6110371 := by exact prefixLift 6110371
  have htrace : WordTrace (prefixWord ++ tailWord_6110371) baseStart_6110371 baseEnd_6110371 := by
    simpa [prefixWord, tailWord_6110371, baseEnd_6110371] using wordTrace_append hprefix tailTrace_6110371
  have hstable : (prefixWord ++ tailWord_6110371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110371).length < 2 ^ (prefixWord ++ tailWord_6110371).sum := by decide
  have hdescent : baseEnd_6110371 < baseStart_6110371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110391 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 7]
def baseStart_6110391 : Nat := 118140960795 + 6110391 * 2 ^ 59
def prefixEnd_6110391 : Nat := 4983230072969 + 3 ^ 40 * 6110391 * 2
def baseEnd_6110391 : Nat := 348618618878567533423481

theorem tailTrace_6110391 : CollatzResearch.WordTrace tailWord_6110391 prefixEnd_6110391 348618618878567533423481 := by
  unfold tailWord_6110391
  simp only [CollatzResearch.WordTrace]
  refine ⟨222864268806104453544923027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148576179204069635696615351 222864268806104453544923027)
  ·
    refine ⟨334296403209156680317384541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222864268806104453544923027 334296403209156680317384541)
    ·
      refine ⟨125361151203433755119019203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334296403209156680317384541 125361151203433755119019203)
      ·
        refine ⟨188041726805150632678528805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125361151203433755119019203 188041726805150632678528805)
        ·
          refine ⟨35257823775965743627224151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188041726805150632678528805 35257823775965743627224151)
          ·
            refine ⟨52886735663948615440836227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35257823775965743627224151 52886735663948615440836227)
            ·
              refine ⟨79330103495922923161254341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52886735663948615440836227 79330103495922923161254341)
              ·
                refine ⟨14874394405485548092735189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79330103495922923161254341 14874394405485548092735189)
                ·
                  refine ⟨348618618878567533423481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14874394405485548092735189 348618618878567533423481)
                  ·
                    rfl

theorem cell23_6110391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 7].length) (baseStart_6110391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110391 prefixEnd_6110391 := by exact prefixLift 6110391
  have htrace : WordTrace (prefixWord ++ tailWord_6110391) baseStart_6110391 baseEnd_6110391 := by
    simpa [prefixWord, tailWord_6110391, baseEnd_6110391] using wordTrace_append hprefix tailTrace_6110391
  have hstable : (prefixWord ++ tailWord_6110391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110391).length < 2 ^ (prefixWord ++ tailWord_6110391).sum := by decide
  have hdescent : baseEnd_6110391 < baseStart_6110391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110431 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 7]
def baseStart_6110431 : Nat := 118140960795 + 6110431 * 2 ^ 59
def prefixEnd_6110431 : Nat := 4983230072969 + 3 ^ 40 * 6110431 * 2
def baseEnd_6110431 : Nat := 3137588109133287644311145

theorem tailTrace_6110431 : CollatzResearch.WordTrace tailWord_6110431 prefixEnd_6110431 3137588109133287644311145 := by
  unfold tailWord_6110431
  simp only [CollatzResearch.WordTrace]
  refine ⟨222865727725959540376379147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148577151817306360250919431 222865727725959540376379147)
  ·
    refine ⟨334298591588939310564568721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222865727725959540376379147 334298591588939310564568721)
    ·
      refine ⟨250723943691704482923426541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334298591588939310564568721 250723943691704482923426541)
      ·
        refine ⟨94021478884389181096284953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250723943691704482923426541 94021478884389181096284953)
        ·
          refine ⟨70516109163291885822213715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94021478884389181096284953 70516109163291885822213715)
          ·
            refine ⟨105774163744937828733320573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70516109163291885822213715 105774163744937828733320573)
            ·
              refine ⟨39665311404351685774995215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105774163744937828733320573 39665311404351685774995215)
              ·
                refine ⟨59497967106527528662492823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39665311404351685774995215 59497967106527528662492823)
                ·
                  refine ⟨89246950659791292993739235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59497967106527528662492823 89246950659791292993739235)
                  ·
                    refine ⟨133870425989686939490608853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89246950659791292993739235 133870425989686939490608853)
                    ·
                      refine ⟨3137588109133287644311145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133870425989686939490608853 3137588109133287644311145)
                      ·
                        rfl

theorem cell23_6110431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_6110431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110431 prefixEnd_6110431 := by exact prefixLift 6110431
  have htrace : WordTrace (prefixWord ++ tailWord_6110431) baseStart_6110431 baseEnd_6110431 := by
    simpa [prefixWord, tailWord_6110431, baseEnd_6110431] using wordTrace_append hprefix tailTrace_6110431
  have hstable : (prefixWord ++ tailWord_6110431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110431).length < 2 ^ (prefixWord ++ tailWord_6110431).sum := by decide
  have hdescent : baseEnd_6110431 < baseStart_6110431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110461 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_6110461 : Nat := 118140960795 + 6110461 * 2 ^ 59
def prefixEnd_6110461 : Nat := 4983230072969 + 3 ^ 40 * 6110461 * 2
def baseEnd_6110461 : Nat := 3137603513552922526936007

theorem tailTrace_6110461 : CollatzResearch.WordTrace tailWord_6110461 prefixEnd_6110461 3137603513552922526936007 := by
  unfold tailWord_6110461
  simp only [CollatzResearch.WordTrace]
  refine ⟨222866821915850855499971237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148577881277233903666647491 222866821915850855499971237)
  ·
    refine ⟨41787529109222035406244607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222866821915850855499971237 41787529109222035406244607)
    ·
      refine ⟨62681293663833053109366911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41787529109222035406244607 62681293663833053109366911)
      ·
        refine ⟨94021940495749579664050367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62681293663833053109366911 94021940495749579664050367)
        ·
          refine ⟨141032910743624369496075551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94021940495749579664050367 141032910743624369496075551)
          ·
            refine ⟨211549366115436554244113327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141032910743624369496075551 211549366115436554244113327)
            ·
              refine ⟨317324049173154831366169991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211549366115436554244113327 317324049173154831366169991)
              ·
                refine ⟨475986073759732247049254987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317324049173154831366169991 475986073759732247049254987)
                ·
                  refine ⟨713979110639598370573882481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475986073759732247049254987 713979110639598370573882481)
                  ·
                    refine ⟨535484332979698777930411861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 713979110639598370573882481 535484332979698777930411861)
                    ·
                      refine ⟨3137603513552922526936007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 535484332979698777930411861 3137603513552922526936007)
                      ·
                        rfl

theorem cell23_6110461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_6110461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110461 prefixEnd_6110461 := by exact prefixLift 6110461
  have htrace : WordTrace (prefixWord ++ tailWord_6110461) baseStart_6110461 baseEnd_6110461 := by
    simpa [prefixWord, tailWord_6110461, baseEnd_6110461] using wordTrace_append hprefix tailTrace_6110461
  have hstable : (prefixWord ++ tailWord_6110461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110461).length < 2 ^ (prefixWord ++ tailWord_6110461).sum := by decide
  have hdescent : baseEnd_6110461 < baseStart_6110461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110509 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_6110509 : Nat := 118140960795 + 6110509 * 2 ^ 59
def prefixEnd_6110509 : Nat := 4983230072969 + 3 ^ 40 * 6110509 * 2
def baseEnd_6110509 : Nat := 3137628160624338339135787

theorem tailTrace_6110509 : CollatzResearch.WordTrace tailWord_6110509 prefixEnd_6110509 3137628160624338339135787 := by
  unfold tailWord_6110509
  simp only [CollatzResearch.WordTrace]
  refine ⟨222868572619676959697718581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148579048413117973131812387 222868572619676959697718581)
  ·
    refine ⟨20893928683094714971661117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222868572619676959697718581 20893928683094714971661117)
    ·
      refine ⟨7835223256160518114372919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20893928683094714971661117 7835223256160518114372919)
      ·
        refine ⟨11752834884240777171559379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7835223256160518114372919 11752834884240777171559379)
        ·
          refine ⟨17629252326361165757339069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11752834884240777171559379 17629252326361165757339069)
          ·
            refine ⟨6610969622385437159002151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17629252326361165757339069 6610969622385437159002151)
            ·
              refine ⟨9916454433578155738503227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6610969622385437159002151 9916454433578155738503227)
              ·
                refine ⟨14874681650367233607754841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9916454433578155738503227 14874681650367233607754841)
                ·
                  refine ⟨11156011237775425205816131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14874681650367233607754841 11156011237775425205816131)
                  ·
                    refine ⟨16734016856663137808724197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11156011237775425205816131 16734016856663137808724197)
                    ·
                      refine ⟨3137628160624338339135787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16734016856663137808724197 3137628160624338339135787)
                      ·
                        rfl

theorem cell23_6110509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_6110509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110509 prefixEnd_6110509 := by exact prefixLift 6110509
  have htrace : WordTrace (prefixWord ++ tailWord_6110509) baseStart_6110509 baseEnd_6110509 := by
    simpa [prefixWord, tailWord_6110509, baseEnd_6110509] using wordTrace_append hprefix tailTrace_6110509
  have hstable : (prefixWord ++ tailWord_6110509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110509).length < 2 ^ (prefixWord ++ tailWord_6110509).sum := by decide
  have hdescent : baseEnd_6110509 < baseStart_6110509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110532 : List Nat := [2, 3, 4, 1, 1, 1, 3, 2, 6]
def baseStart_6110532 : Nat := 118140960795 + 6110532 * 2 ^ 59
def prefixEnd_6110532 : Nat := 4983230072969 + 3 ^ 40 * 6110532 * 2
def baseEnd_6110532 : Nat := 348626663408821305460909

theorem tailTrace_6110532 : CollatzResearch.WordTrace tailWord_6110532 prefixEnd_6110532 348626663408821305460909 := by
  unfold tailWord_6110532
  simp only [CollatzResearch.WordTrace]
  refine ⟨111434705749296817312902925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148579607665729089750537233 111434705749296817312902925)
  ·
    refine ⟨41788014655986306492338597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111434705749296817312902925 41788014655986306492338597)
    ·
      refine ⟨7835252747997432467313487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41788014655986306492338597 7835252747997432467313487)
      ·
        refine ⟨11752879121996148700970231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7835252747997432467313487 11752879121996148700970231)
        ·
          refine ⟨17629318682994223051455347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11752879121996148700970231 17629318682994223051455347)
          ·
            refine ⟨26443978024491334577183021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17629318682994223051455347 26443978024491334577183021)
            ·
              refine ⟨9916491759184250466443633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26443978024491334577183021 9916491759184250466443633)
              ·
                refine ⟨7437368819388187849832725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9916491759184250466443633 7437368819388187849832725)
                ·
                  refine ⟨348626663408821305460909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7437368819388187849832725 348626663408821305460909)
                  ·
                    rfl

theorem cell23_6110532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_6110532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110532 prefixEnd_6110532 := by exact prefixLift 6110532
  have htrace : WordTrace (prefixWord ++ tailWord_6110532) baseStart_6110532 baseEnd_6110532 := by
    simpa [prefixWord, tailWord_6110532, baseEnd_6110532] using wordTrace_append hprefix tailTrace_6110532
  have hstable : (prefixWord ++ tailWord_6110532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110532).length < 2 ^ (prefixWord ++ tailWord_6110532).sum := by decide
  have hdescent : baseEnd_6110532 < baseStart_6110532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110542 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3]
def baseStart_6110542 : Nat := 118140960795 + 6110542 * 2 ^ 59
def prefixEnd_6110542 : Nat := 4983230072969 + 3 ^ 40 * 6110542 * 2
def baseEnd_6110542 : Nat := 3137645105485936710023135

theorem tailTrace_6110542 : CollatzResearch.WordTrace tailWord_6110542 prefixEnd_6110542 3137645105485936710023135 := by
  unfold tailWord_6110542
  simp only [CollatzResearch.WordTrace]
  refine ⟨27858722028569675791708735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148579850819038270889113253 27858722028569675791708735)
  ·
    refine ⟨41788083042854513687563103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27858722028569675791708735 41788083042854513687563103)
    ·
      refine ⟨62682124564281770531344655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41788083042854513687563103 62682124564281770531344655)
      ·
        refine ⟨94023186846422655797016983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62682124564281770531344655 94023186846422655797016983)
        ·
          refine ⟨141034780269633983695525475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94023186846422655797016983 141034780269633983695525475)
          ·
            refine ⟨211552170404450975543288213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141034780269633983695525475 211552170404450975543288213)
            ·
              refine ⟨9916507987708639478591635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 211552170404450975543288213 9916507987708639478591635)
              ·
                refine ⟨14874761981562959217887453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9916507987708639478591635 14874761981562959217887453)
                ·
                  refine ⟨5578035743086109706707795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14874761981562959217887453 5578035743086109706707795)
                  ·
                    refine ⟨8367053614629164560061693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5578035743086109706707795 8367053614629164560061693)
                    ·
                      refine ⟨3137645105485936710023135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8367053614629164560061693 3137645105485936710023135)
                      ·
                        rfl

theorem cell23_6110542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_6110542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110542 prefixEnd_6110542 := by exact prefixLift 6110542
  have htrace : WordTrace (prefixWord ++ tailWord_6110542) baseStart_6110542 baseEnd_6110542 := by
    simpa [prefixWord, tailWord_6110542, baseEnd_6110542] using wordTrace_append hprefix tailTrace_6110542
  have hstable : (prefixWord ++ tailWord_6110542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110542).length < 2 ^ (prefixWord ++ tailWord_6110542).sum := by decide
  have hdescent : baseEnd_6110542 < baseStart_6110542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110562 : List Nat := [3, 3, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_6110562 : Nat := 118140960795 + 6110562 * 2 ^ 59
def prefixEnd_6110562 : Nat := 4983230072969 + 3 ^ 40 * 6110562 * 2
def baseEnd_6110562 : Nat := 1045885125033008877257681

theorem tailTrace_6110562 : CollatzResearch.WordTrace tailWord_6110562 prefixEnd_6110562 1045885125033008877257681 := by
  unfold tailWord_6110562
  simp only [CollatzResearch.WordTrace]
  refine ⟨55717626422121237437349485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148580337125656633166265293 55717626422121237437349485)
  ·
    refine ⟨20894109908295464039006057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55717626422121237437349485 20894109908295464039006057)
    ·
      refine ⟨15670582431221598029254543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20894109908295464039006057 15670582431221598029254543)
      ·
        refine ⟨23505873646832397043881815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15670582431221598029254543 23505873646832397043881815)
        ·
          refine ⟨35258810470248595565822723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23505873646832397043881815 35258810470248595565822723)
          ·
            refine ⟨52888215705372893348734085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35258810470248595565822723 52888215705372893348734085)
            ·
              refine ⟨9916540444757417502887641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52888215705372893348734085 9916540444757417502887641)
              ·
                refine ⟨7437405333568063127165731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9916540444757417502887641 7437405333568063127165731)
                ·
                  refine ⟨11156108000352094690748597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7437405333568063127165731 11156108000352094690748597)
                  ·
                    refine ⟨1045885125033008877257681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11156108000352094690748597 1045885125033008877257681)
                    ·
                      rfl

theorem cell23_6110562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_6110562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110562 prefixEnd_6110562 := by exact prefixLift 6110562
  have htrace : WordTrace (prefixWord ++ tailWord_6110562) baseStart_6110562 baseEnd_6110562 := by
    simpa [prefixWord, tailWord_6110562, baseEnd_6110562] using wordTrace_append hprefix tailTrace_6110562
  have hstable : (prefixWord ++ tailWord_6110562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110562).length < 2 ^ (prefixWord ++ tailWord_6110562).sum := by decide
  have hdescent : baseEnd_6110562 < baseStart_6110562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110565 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 2, 6, 2]
def baseStart_6110565 : Nat := 118140960795 + 6110565 * 2 ^ 59
def prefixEnd_6110565 : Nat := 4983230072969 + 3 ^ 40 * 6110565 * 2
def baseEnd_6110565 : Nat := 3137656915540990120035529

theorem tailTrace_6110565 : CollatzResearch.WordTrace tailWord_6110565 prefixEnd_6110565 3137656915540990120035529 := by
  unfold tailWord_6110565
  simp only [CollatzResearch.WordTrace]
  refine ⟨222870615107474081261757149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148580410071649387507838099 222870615107474081261757149)
  ·
    refine ⟨83576480665302780473158931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222870615107474081261757149 83576480665302780473158931)
    ·
      refine ⟨125364720997954170709738397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83576480665302780473158931 125364720997954170709738397)
      ·
        refine ⟨47011770374232814016151899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125364720997954170709738397 47011770374232814016151899)
        ·
          refine ⟨70517655561349221024227849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47011770374232814016151899 70517655561349221024227849)
          ·
            refine ⟨52888241671011915768170887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70517655561349221024227849 52888241671011915768170887)
            ·
              refine ⟨79332362506517873652256331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52888241671011915768170887 79332362506517873652256331)
              ·
                refine ⟨118998543759776810478384497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79332362506517873652256331 118998543759776810478384497)
                ·
                  refine ⟨89248907819832607858788373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118998543759776810478384497 89248907819832607858788373)
                  ·
                    refine ⟨4183542554054653493380705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89248907819832607858788373 4183542554054653493380705)
                    ·
                      refine ⟨3137656915540990120035529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4183542554054653493380705 3137656915540990120035529)
                      ·
                        rfl

theorem cell23_6110565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_6110565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110565 prefixEnd_6110565 := by exact prefixLift 6110565
  have htrace : WordTrace (prefixWord ++ tailWord_6110565) baseStart_6110565 baseEnd_6110565 := by
    simpa [prefixWord, tailWord_6110565, baseEnd_6110565] using wordTrace_append hprefix tailTrace_6110565
  have hstable : (prefixWord ++ tailWord_6110565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110565).length < 2 ^ (prefixWord ++ tailWord_6110565).sum := by decide
  have hdescent : baseEnd_6110565 < baseStart_6110565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110593 : List Nat := [1, 2, 4, 3, 2, 1, 3, 2, 1, 1, 3]
def baseStart_6110593 : Nat := 118140960795 + 6110593 * 2 ^ 59
def prefixEnd_6110593 : Nat := 4983230072969 + 3 ^ 40 * 6110593 * 2
def baseEnd_6110593 : Nat := 3137671292999316010485401

theorem tailTrace_6110593 : CollatzResearch.WordTrace tailWord_6110593 prefixEnd_6110593 3137671292999316010485401 := by
  unfold tailWord_6110593
  simp only [CollatzResearch.WordTrace]
  refine ⟨222871636351372642043776433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148581090900915094695850955 222871636351372642043776433)
  ·
    refine ⟨167153727263529481532832325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222871636351372642043776433 167153727263529481532832325)
    ·
      refine ⟨31341323861911777787406061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167153727263529481532832325 31341323861911777787406061)
      ·
        refine ⟨11752996448216916670277273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31341323861911777787406061 11752996448216916670277273)
        ·
          refine ⟨8814747336162687502707955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11752996448216916670277273 8814747336162687502707955)
          ·
            refine ⟨13222121004244031254061933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8814747336162687502707955 13222121004244031254061933)
            ·
              refine ⟨4958295376591511720273225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13222121004244031254061933 4958295376591511720273225)
              ·
                refine ⟨3718721532443633790204919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4958295376591511720273225 3718721532443633790204919)
                ·
                  refine ⟨5578082298665450685307379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3718721532443633790204919 5578082298665450685307379)
                  ·
                    refine ⟨8367123447998176027961069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5578082298665450685307379 8367123447998176027961069)
                    ·
                      refine ⟨3137671292999316010485401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8367123447998176027961069 3137671292999316010485401)
                      ·
                        rfl

theorem cell23_6110593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_6110593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110593 prefixEnd_6110593 := by exact prefixLift 6110593
  have htrace : WordTrace (prefixWord ++ tailWord_6110593) baseStart_6110593 baseEnd_6110593 := by
    simpa [prefixWord, tailWord_6110593, baseEnd_6110593] using wordTrace_append hprefix tailTrace_6110593
  have hstable : (prefixWord ++ tailWord_6110593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110593).length < 2 ^ (prefixWord ++ tailWord_6110593).sum := by decide
  have hdescent : baseEnd_6110593 < baseStart_6110593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110599 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 3, 2, 2]
def baseStart_6110599 : Nat := 118140960795 + 6110599 * 2 ^ 59
def prefixEnd_6110599 : Nat := 4983230072969 + 3 ^ 40 * 6110599 * 2
def baseEnd_6110599 : Nat := 3137674373883242987010373

theorem tailTrace_6110599 : CollatzResearch.WordTrace tailWord_6110599 prefixEnd_6110599 3137674373883242987010373 := by
  unfold tailWord_6110599
  simp only [CollatzResearch.WordTrace]
  refine ⟨222871855189350905068494851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148581236792900603378996567 222871855189350905068494851)
  ·
    refine ⟨334307782784026357602742277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222871855189350905068494851 334307782784026357602742277)
    ·
      refine ⟨62682709272004942050514177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 334307782784026357602742277 62682709272004942050514177)
      ·
        refine ⟨47012031954003706537885633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62682709272004942050514177 47012031954003706537885633)
        ·
          refine ⟨35259023965502779903414225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47012031954003706537885633 35259023965502779903414225)
          ·
            refine ⟨26444267974127084927560669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35259023965502779903414225 26444267974127084927560669)
            ·
              refine ⟨9916600490297656847835251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26444267974127084927560669 9916600490297656847835251)
              ·
                refine ⟨14874900735446485271752877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9916600490297656847835251 14874900735446485271752877)
                ·
                  refine ⟨5578087775792431976907329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14874900735446485271752877 5578087775792431976907329)
                  ·
                    refine ⟨4183565831844323982680497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5578087775792431976907329 4183565831844323982680497)
                    ·
                      refine ⟨3137674373883242987010373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4183565831844323982680497 3137674373883242987010373)
                      ·
                        rfl

theorem cell23_6110599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_6110599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110599 prefixEnd_6110599 := by exact prefixLift 6110599
  have htrace : WordTrace (prefixWord ++ tailWord_6110599) baseStart_6110599 baseEnd_6110599 := by
    simpa [prefixWord, tailWord_6110599, baseEnd_6110599] using wordTrace_append hprefix tailTrace_6110599
  have hstable : (prefixWord ++ tailWord_6110599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110599).length < 2 ^ (prefixWord ++ tailWord_6110599).sum := by decide
  have hdescent : baseEnd_6110599 < baseStart_6110599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110615 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 3]
def baseStart_6110615 : Nat := 118140960795 + 6110615 * 2 ^ 59
def prefixEnd_6110615 : Nat := 4983230072969 + 3 ^ 40 * 6110615 * 2
def baseEnd_6110615 : Nat := 3137682589573714924410299

theorem tailTrace_6110615 : CollatzResearch.WordTrace tailWord_6110615 prefixEnd_6110615 3137682589573714924410299 := by
  unfold tailWord_6110615
  simp only [CollatzResearch.WordTrace]
  refine ⟨222872438757292939801077299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148581625838195293200718199 222872438757292939801077299)
  ·
    refine ⟨334308658135939409701615949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222872438757292939801077299 334308658135939409701615949)
    ·
      refine ⟨125365746800977278638105981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334308658135939409701615949 125365746800977278638105981)
      ·
        refine ⟨47012155050366479489289743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125365746800977278638105981 47012155050366479489289743)
        ·
          refine ⟨70518232575549719233934615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47012155050366479489289743 70518232575549719233934615)
          ·
            refine ⟨105777348863324578850901923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70518232575549719233934615 105777348863324578850901923)
            ·
              refine ⟨158666023294986868276352885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105777348863324578850901923 158666023294986868276352885)
              ·
                refine ⟨14874939683905018900908083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158666023294986868276352885 14874939683905018900908083)
                ·
                  refine ⟨22312409525857528351362125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14874939683905018900908083 22312409525857528351362125)
                  ·
                    refine ⟨8367153572196573131760797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22312409525857528351362125 8367153572196573131760797)
                    ·
                      refine ⟨3137682589573714924410299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8367153572196573131760797 3137682589573714924410299)
                      ·
                        rfl

theorem cell23_6110615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_6110615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110615 prefixEnd_6110615 := by exact prefixLift 6110615
  have htrace : WordTrace (prefixWord ++ tailWord_6110615) baseStart_6110615 baseEnd_6110615 := by
    simpa [prefixWord, tailWord_6110615, baseEnd_6110615] using wordTrace_append hprefix tailTrace_6110615
  have hstable : (prefixWord ++ tailWord_6110615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110615).length < 2 ^ (prefixWord ++ tailWord_6110615).sum := by decide
  have hdescent : baseEnd_6110615 < baseStart_6110615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110616 : List Nat := [2, 1, 2, 5, 3, 1, 1, 2, 1, 1, 4]
def baseStart_6110616 : Nat := 118140960795 + 6110616 * 2 ^ 59
def prefixEnd_6110616 : Nat := 4983230072969 + 3 ^ 40 * 6110616 * 2
def baseEnd_6110616 : Nat := 3137683103054369420497795

theorem tailTrace_6110616 : CollatzResearch.WordTrace tailWord_6110616 prefixEnd_6110616 3137683103054369420497795 := by
  unfold tailWord_6110616
  simp only [CollatzResearch.WordTrace]
  refine ⟨111436237615144658485931851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148581650153526211314575801 111436237615144658485931851)
  ·
    refine ⟨167154356422716987728897777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111436237615144658485931851 167154356422716987728897777)
    ·
      refine ⟨125365767317037740796673333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167154356422716987728897777 125365767317037740796673333)
      ·
        refine ⟨11753040685972288199688125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125365767317037740796673333 11753040685972288199688125)
        ·
          refine ⟨4407390257239608074883047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11753040685972288199688125 4407390257239608074883047)
          ·
            refine ⟨6611085385859412112324571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4407390257239608074883047 6611085385859412112324571)
            ·
              refine ⟨9916628078789118168486857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6611085385859412112324571 9916628078789118168486857)
              ·
                refine ⟨7437471059091838626365143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9916628078789118168486857 7437471059091838626365143)
                ·
                  refine ⟨11156206588637757939547715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7437471059091838626365143 11156206588637757939547715)
                  ·
                    refine ⟨16734309882956636909321573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11156206588637757939547715 16734309882956636909321573)
                    ·
                      refine ⟨3137683103054369420497795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16734309882956636909321573 3137683103054369420497795)
                      ·
                        rfl

theorem cell23_6110616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_6110616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110616 prefixEnd_6110616 := by exact prefixLift 6110616
  have htrace : WordTrace (prefixWord ++ tailWord_6110616) baseStart_6110616 baseEnd_6110616 := by
    simpa [prefixWord, tailWord_6110616, baseEnd_6110616] using wordTrace_append hprefix tailTrace_6110616
  have hstable : (prefixWord ++ tailWord_6110616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110616).length < 2 ^ (prefixWord ++ tailWord_6110616).sum := by decide
  have hdescent : baseEnd_6110616 < baseStart_6110616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110693 : List Nat := [1, 3, 1, 5, 1, 3, 2, 1, 1, 3, 2]
def baseStart_6110693 : Nat := 118140960795 + 6110693 * 2 ^ 59
def prefixEnd_6110693 : Nat := 4983230072969 + 3 ^ 40 * 6110693 * 2
def baseEnd_6110693 : Nat := 3137722641064765619234941

theorem tailTrace_6110693 : CollatzResearch.WordTrace tailWord_6110693 prefixEnd_6110693 3137722641064765619234941 := by
  unfold tailWord_6110693
  simp only [CollatzResearch.WordTrace]
  refine ⟨222875283651010359122416733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148583522434006906081611155 222875283651010359122416733)
  ·
    refine ⟨83578231369128884670906275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222875283651010359122416733 83578231369128884670906275)
    ·
      refine ⟨125367347053693327006359413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83578231369128884670906275 125367347053693327006359413)
      ·
        refine ⟨11753188786283749406846195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125367347053693327006359413 11753188786283749406846195)
        ·
          refine ⟨17629783179425624110269293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11753188786283749406846195 17629783179425624110269293)
          ·
            refine ⟨6611168692284609041350985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17629783179425624110269293 6611168692284609041350985)
            ·
              refine ⟨4958376519213456781013239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6611168692284609041350985 4958376519213456781013239)
              ·
                refine ⟨7437564778820185171519859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4958376519213456781013239 7437564778820185171519859)
                ·
                  refine ⟨11156347168230277757279789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7437564778820185171519859 11156347168230277757279789)
                  ·
                    refine ⟨4183630188086354158979921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11156347168230277757279789 4183630188086354158979921)
                    ·
                      refine ⟨3137722641064765619234941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4183630188086354158979921 3137722641064765619234941)
                      ·
                        rfl

theorem cell23_6110693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_6110693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110693 prefixEnd_6110693 := by exact prefixLift 6110693
  have htrace : WordTrace (prefixWord ++ tailWord_6110693) baseStart_6110693 baseEnd_6110693 := by
    simpa [prefixWord, tailWord_6110693, baseEnd_6110693] using wordTrace_append hprefix tailTrace_6110693
  have hstable : (prefixWord ++ tailWord_6110693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110693).length < 2 ^ (prefixWord ++ tailWord_6110693).sum := by decide
  have hdescent : baseEnd_6110693 < baseStart_6110693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110706 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 4, 2, 2]
def baseStart_6110706 : Nat := 118140960795 + 6110706 * 2 ^ 59
def prefixEnd_6110706 : Nat := 4983230072969 + 3 ^ 40 * 6110706 * 2
def baseEnd_6110706 : Nat := 3137729316313274068372381

theorem tailTrace_6110706 : CollatzResearch.WordTrace tailWord_6110706 prefixEnd_6110706 3137729316313274068372381 := by
  unfold tailWord_6110706
  simp only [CollatzResearch.WordTrace]
  refine ⟨55718939449990815585659993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148583838533308841561759981 55718939449990815585659993)
  ·
    refine ⟨41789204587493111689244995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55718939449990815585659993 41789204587493111689244995)
    ·
      refine ⟨62683806881239667533867493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41789204587493111689244995 62683806881239667533867493)
      ·
        refine ⟨11753213790232437662600155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62683806881239667533867493 11753213790232437662600155)
        ·
          refine ⟨17629820685348656493900233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11753213790232437662600155 17629820685348656493900233)
          ·
            refine ⟨13222365514011492370425175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17629820685348656493900233 13222365514011492370425175)
            ·
              refine ⟨19833548271017238555637763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13222365514011492370425175 19833548271017238555637763)
              ·
                refine ⟨29750322406525857833456645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19833548271017238555637763 29750322406525857833456645)
                ·
                  refine ⟨5578185451223598343773121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29750322406525857833456645 5578185451223598343773121)
                  ·
                    refine ⟨4183639088417698757829841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5578185451223598343773121 4183639088417698757829841)
                    ·
                      refine ⟨3137729316313274068372381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4183639088417698757829841 3137729316313274068372381)
                      ·
                        rfl

theorem cell23_6110706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_6110706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110706 prefixEnd_6110706 := by exact prefixLift 6110706
  have htrace : WordTrace (prefixWord ++ tailWord_6110706) baseStart_6110706 baseEnd_6110706 := by
    simpa [prefixWord, tailWord_6110706, baseEnd_6110706] using wordTrace_append hprefix tailTrace_6110706
  have hstable : (prefixWord ++ tailWord_6110706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110706).length < 2 ^ (prefixWord ++ tailWord_6110706).sum := by decide
  have hdescent : baseEnd_6110706 < baseStart_6110706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110712 : List Nat := [2, 1, 2, 1, 1, 5, 2, 4, 5]
def baseStart_6110712 : Nat := 118140960795 + 6110712 * 2 ^ 59
def prefixEnd_6110712 : Nat := 4983230072969 + 3 ^ 40 * 6110712 * 2
def baseEnd_6110712 : Nat := 348636933021911227210817

theorem tailTrace_6110712 : CollatzResearch.WordTrace tailWord_6110712 prefixEnd_6110712 348636933021911227210817 := by
  unfold tailWord_6110712
  simp only [CollatzResearch.WordTrace]
  refine ⟨111437988318970762683679195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148583984425294350244905593 111437988318970762683679195)
  ·
    refine ⟨167156982478456144025518793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111437988318970762683679195 167156982478456144025518793)
    ·
      refine ⟨125367736858842108019139095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167156982478456144025518793 125367736858842108019139095)
      ·
        refine ⟨188051605288263162028708643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125367736858842108019139095 188051605288263162028708643)
        ·
          refine ⟨282077407932394743043062965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188051605288263162028708643 282077407932394743043062965)
          ·
            refine ⟨26444756993662007160287153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 282077407932394743043062965 26444756993662007160287153)
            ·
              refine ⟨19833567745246505370215365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26444756993662007160287153 19833567745246505370215365)
              ·
                refine ⟨3718793952233719756915381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19833567745246505370215365 3718793952233719756915381)
                ·
                  refine ⟨348636933021911227210817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3718793952233719756915381 348636933021911227210817)
                  ·
                    rfl

theorem cell23_6110712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 5].length) (baseStart_6110712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110712 prefixEnd_6110712 := by exact prefixLift 6110712
  have htrace : WordTrace (prefixWord ++ tailWord_6110712) baseStart_6110712 baseEnd_6110712 := by
    simpa [prefixWord, tailWord_6110712, baseEnd_6110712] using wordTrace_append hprefix tailTrace_6110712
  have hstable : (prefixWord ++ tailWord_6110712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110712).length < 2 ^ (prefixWord ++ tailWord_6110712).sum := by decide
  have hdescent : baseEnd_6110712 < baseStart_6110712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110805 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_6110805 : Nat := 118140960795 + 6110805 * 2 ^ 59
def prefixEnd_6110805 : Nat := 4983230072969 + 3 ^ 40 * 6110805 * 2
def baseEnd_6110805 : Nat := 3137780150898069181034425

theorem tailTrace_6110805 : CollatzResearch.WordTrace tailWord_6110805 prefixEnd_6110805 3137780150898069181034425 := by
  unfold tailWord_6110805
  simp only [CollatzResearch.WordTrace]
  refine ⟨222879368626604602250493869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148586245751069734833662579 222879368626604602250493869)
  ·
    refine ⟨83579763234976725843935201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222879368626604602250493869 83579763234976725843935201)
    ·
      refine ⟨62684822426232544382951401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83579763234976725843935201 62684822426232544382951401)
      ·
        refine ⟨47013616819674408287213551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62684822426232544382951401 47013616819674408287213551)
        ·
          refine ⟨70520425229511612430820327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47013616819674408287213551 70520425229511612430820327)
          ·
            refine ⟨105780637844267418646230491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70520425229511612430820327 105780637844267418646230491)
            ·
              refine ⟨158670956766401127969345737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105780637844267418646230491 158670956766401127969345737)
              ·
                refine ⟨119003217574800845977009303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158670956766401127969345737 119003217574800845977009303)
                ·
                  refine ⟨178504826362201268965513955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119003217574800845977009303 178504826362201268965513955)
                  ·
                    refine ⟨267757239543301903448270933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 178504826362201268965513955 267757239543301903448270933)
                    ·
                      refine ⟨3137780150898069181034425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 267757239543301903448270933 3137780150898069181034425)
                      ·
                        rfl

theorem cell23_6110805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_6110805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110805 prefixEnd_6110805 := by exact prefixLift 6110805
  have htrace : WordTrace (prefixWord ++ tailWord_6110805) baseStart_6110805 baseEnd_6110805 := by
    simpa [prefixWord, tailWord_6110805, baseEnd_6110805] using wordTrace_append hprefix tailTrace_6110805
  have hstable : (prefixWord ++ tailWord_6110805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110805).length < 2 ^ (prefixWord ++ tailWord_6110805).sum := by decide
  have hdescent : baseEnd_6110805 < baseStart_6110805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110832 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 3, 5]
def baseStart_6110832 : Nat := 118140960795 + 6110832 * 2 ^ 59
def prefixEnd_6110832 : Nat := 4983230072969 + 3 ^ 40 * 6110832 * 2
def baseEnd_6110832 : Nat := 1045931338291913525132267

theorem tailTrace_6110832 : CollatzResearch.WordTrace tailWord_6110832 prefixEnd_6110832 1045931338291913525132267 := by
  unfold tailWord_6110832
  simp only [CollatzResearch.WordTrace]
  refine ⟨111440176698753392930863375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148586902265004523907817833 111440176698753392930863375)
  ·
    refine ⟨167160265048130089396295063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111440176698753392930863375 167160265048130089396295063)
    ·
      refine ⟨250740397572195134094442595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167160265048130089396295063 250740397572195134094442595)
      ·
        refine ⟨376110596358292701141663893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250740397572195134094442595 376110596358292701141663893)
        ·
          refine ⟨17630184204294970366015495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 376110596358292701141663893 17630184204294970366015495)
          ·
            refine ⟨26445276306442455549023243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17630184204294970366015495 26445276306442455549023243)
            ·
              refine ⟨39667914459663683323534865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26445276306442455549023243 39667914459663683323534865)
              ·
                refine ⟨29750935844747762492651149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39667914459663683323534865 29750935844747762492651149)
                ·
                  refine ⟨11156600941780410934744181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29750935844747762492651149 11156600941780410934744181)
                  ·
                    refine ⟨1045931338291913525132267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11156600941780410934744181 1045931338291913525132267)
                    ·
                      rfl

theorem cell23_6110832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 3, 5].length) (baseStart_6110832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110832 prefixEnd_6110832 := by exact prefixLift 6110832
  have htrace : WordTrace (prefixWord ++ tailWord_6110832) baseStart_6110832 baseEnd_6110832 := by
    simpa [prefixWord, tailWord_6110832, baseEnd_6110832] using wordTrace_append hprefix tailTrace_6110832
  have hstable : (prefixWord ++ tailWord_6110832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110832).length < 2 ^ (prefixWord ++ tailWord_6110832).sum := by decide
  have hdescent : baseEnd_6110832 < baseStart_6110832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110866 : List Nat := [3, 2, 3, 1, 3, 1, 1, 3, 1, 5]
def baseStart_6110866 : Nat := 118140960795 + 6110866 * 2 ^ 59
def prefixEnd_6110866 : Nat := 4983230072969 + 3 ^ 40 * 6110866 * 2
def baseEnd_6110866 : Nat := 1045937157739331147457215

theorem tailTrace_6110866 : CollatzResearch.WordTrace tailWord_6110866 prefixEnd_6110866 1045937157739331147457215 := by
  unfold tailWord_6110866
  simp only [CollatzResearch.WordTrace]
  refine ⟨55720398369845902417116113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148587728986255739778976301 55720398369845902417116113)
  ·
    refine ⟨41790298777384426812837085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55720398369845902417116113 41790298777384426812837085)
    ·
      refine ⟨15671362041519160054813907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41790298777384426812837085 15671362041519160054813907)
      ·
        refine ⟨23507043062278740082220861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15671362041519160054813907 23507043062278740082220861)
        ·
          refine ⟨8815141148354527530832823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23507043062278740082220861 8815141148354527530832823)
          ·
            refine ⟨13222711722531791296249235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8815141148354527530832823 13222711722531791296249235)
            ·
              refine ⟨19834067583797686944373853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13222711722531791296249235 19834067583797686944373853)
              ·
                refine ⟨7437775343924132604140195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19834067583797686944373853 7437775343924132604140195)
                ·
                  refine ⟨11156663015886198906210293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7437775343924132604140195 11156663015886198906210293)
                  ·
                    refine ⟨1045937157739331147457215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11156663015886198906210293 1045937157739331147457215)
                    ·
                      rfl

theorem cell23_6110866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_6110866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110866 prefixEnd_6110866 := by exact prefixLift 6110866
  have htrace : WordTrace (prefixWord ++ tailWord_6110866) baseStart_6110866 baseEnd_6110866 := by
    simpa [prefixWord, tailWord_6110866, baseEnd_6110866] using wordTrace_append hprefix tailTrace_6110866
  have hstable : (prefixWord ++ tailWord_6110866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110866).length < 2 ^ (prefixWord ++ tailWord_6110866).sum := by decide
  have hdescent : baseEnd_6110866 < baseStart_6110866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110906 : List Nat := [3, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3]
def baseStart_6110906 : Nat := 118140960795 + 6110906 * 2 ^ 59
def prefixEnd_6110906 : Nat := 4983230072969 + 3 ^ 40 * 6110906 * 2
def baseEnd_6110906 : Nat := 3137832012444173285871461

theorem tailTrace_6110906 : CollatzResearch.WordTrace tailWord_6110906 prefixEnd_6110906 3137832012444173285871461 := by
  unfold tailWord_6110906
  simp only [CollatzResearch.WordTrace]
  refine ⟨55720763099809674124980143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148588701599492464333280381 55720763099809674124980143)
  ·
    refine ⟨83581144649714511187470215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55720763099809674124980143 83581144649714511187470215)
    ·
      refine ⟨125371716974571766781205323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83581144649714511187470215 125371716974571766781205323)
      ·
        refine ⟨188057575461857650171807985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125371716974571766781205323 188057575461857650171807985)
        ·
          refine ⟨141043181596393237628855989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188057575461857650171807985 141043181596393237628855989)
          ·
            refine ⟨13222798274661866027705249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141043181596393237628855989 13222798274661866027705249)
            ·
              refine ⟨9917098705996399520778937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13222798274661866027705249 9917098705996399520778937)
              ·
                refine ⟨7437824029497299640584203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9917098705996399520778937 7437824029497299640584203)
                ·
                  refine ⟨11156736044245949460876305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7437824029497299640584203 11156736044245949460876305)
                  ·
                    refine ⟨8367552033184462095657229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11156736044245949460876305 8367552033184462095657229)
                    ·
                      refine ⟨3137832012444173285871461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8367552033184462095657229 3137832012444173285871461)
                      ·
                        rfl

theorem cell23_6110906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_6110906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110906 prefixEnd_6110906 := by exact prefixLift 6110906
  have htrace : WordTrace (prefixWord ++ tailWord_6110906) baseStart_6110906 baseEnd_6110906 := by
    simpa [prefixWord, tailWord_6110906, baseEnd_6110906] using wordTrace_append hprefix tailTrace_6110906
  have hstable : (prefixWord ++ tailWord_6110906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110906).length < 2 ^ (prefixWord ++ tailWord_6110906).sum := by decide
  have hdescent : baseEnd_6110906 < baseStart_6110906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110919 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 6, 1, 3]
def baseStart_6110919 : Nat := 118140960795 + 6110919 * 2 ^ 59
def prefixEnd_6110919 : Nat := 4983230072969 + 3 ^ 40 * 6110919 * 2
def baseEnd_6110919 : Nat := 3137838687692681735008901

theorem tailTrace_6110919 : CollatzResearch.WordTrace tailWord_6110919 prefixEnd_6110919 3137838687692681735008901 := by
  unfold tailWord_6110919
  simp only [CollatzResearch.WordTrace]
  refine ⟨222883526548191599720143811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148589017698794399813429207 222883526548191599720143811)
  ·
    refine ⟨334325289822287399580215717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222883526548191599720143811 334325289822287399580215717)
    ·
      refine ⟨62685991841678887421290447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 334325289822287399580215717 62685991841678887421290447)
      ·
        refine ⟨94028987762518331131935671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62685991841678887421290447 94028987762518331131935671)
        ·
          refine ⟨141043481643777496697903507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94028987762518331131935671 141043481643777496697903507)
          ·
            refine ⟨211565222465666245046855261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141043481643777496697903507 211565222465666245046855261)
            ·
              refine ⟨79336958424624841892570723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211565222465666245046855261 79336958424624841892570723)
              ·
                refine ⟨119005437636937262838856085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79336958424624841892570723 119005437636937262838856085)
                ·
                  refine ⟨5578379889231434195571379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119005437636937262838856085 5578379889231434195571379)
                  ·
                    refine ⟨8367569833847151293357069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5578379889231434195571379 8367569833847151293357069)
                    ·
                      refine ⟨3137838687692681735008901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8367569833847151293357069 3137838687692681735008901)
                      ·
                        rfl

theorem cell23_6110919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_6110919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110919 prefixEnd_6110919 := by exact prefixLift 6110919
  have htrace : WordTrace (prefixWord ++ tailWord_6110919) baseStart_6110919 baseEnd_6110919 := by
    simpa [prefixWord, tailWord_6110919, baseEnd_6110919] using wordTrace_append hprefix tailTrace_6110919
  have hstable : (prefixWord ++ tailWord_6110919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110919).length < 2 ^ (prefixWord ++ tailWord_6110919).sum := by decide
  have hdescent : baseEnd_6110919 < baseStart_6110919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110936 : List Nat := [2, 1, 2, 2, 3, 1, 2, 4, 2, 1, 3]
def baseStart_6110936 : Nat := 118140960795 + 6110936 * 2 ^ 59
def prefixEnd_6110936 : Nat := 4983230072969 + 3 ^ 40 * 6110936 * 2
def baseEnd_6110936 : Nat := 3137847416863808168496323

theorem tailTrace_6110936 : CollatzResearch.WordTrace tailWord_6110936 prefixEnd_6110936 3137847416863808168496323 := by
  unfold tailWord_6110936
  simp only [CollatzResearch.WordTrace]
  refine ⟨111442073294565005811756331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148589431059420007749008441 111442073294565005811756331)
  ·
    refine ⟨167163109941847508717634497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111442073294565005811756331 167163109941847508717634497)
    ·
      refine ⟨125372332456385631538225873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167163109941847508717634497 125372332456385631538225873)
      ·
        refine ⟨94029249342289223653669405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125372332456385631538225873 94029249342289223653669405)
        ·
          refine ⟨35260968503358458870126027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94029249342289223653669405 35260968503358458870126027)
          ·
            refine ⟨52891452755037688305189041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35260968503358458870126027 52891452755037688305189041)
            ·
              refine ⟨39668589566278266228891781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52891452755037688305189041 39668589566278266228891781)
              ·
                refine ⟨7437860543677174917917209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39668589566278266228891781 7437860543677174917917209)
                ·
                  refine ⟨5578395407757881188437907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7437860543677174917917209 5578395407757881188437907)
                  ·
                    refine ⟨8367593111636821782656861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5578395407757881188437907 8367593111636821782656861)
                    ·
                      refine ⟨3137847416863808168496323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8367593111636821782656861 3137847416863808168496323)
                      ·
                        rfl

theorem cell23_6110936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_6110936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110936 prefixEnd_6110936 := by exact prefixLift 6110936
  have htrace : WordTrace (prefixWord ++ tailWord_6110936) baseStart_6110936 baseEnd_6110936 := by
    simpa [prefixWord, tailWord_6110936, baseEnd_6110936] using wordTrace_append hprefix tailTrace_6110936
  have hstable : (prefixWord ++ tailWord_6110936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110936).length < 2 ^ (prefixWord ++ tailWord_6110936).sum := by decide
  have hdescent : baseEnd_6110936 < baseStart_6110936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6110980 : List Nat := [2, 3, 2, 2, 1, 3, 3, 1, 1, 3, 2]
def baseStart_6110980 : Nat := 118140960795 + 6110980 * 2 ^ 59
def prefixEnd_6110980 : Nat := 4983230072969 + 3 ^ 40 * 6110980 * 2
def baseEnd_6110980 : Nat := 3137870010012605996346121

theorem tailTrace_6110980 : CollatzResearch.WordTrace tailWord_6110980 prefixEnd_6110980 3137870010012605996346121 := by
  unfold tailWord_6110980
  simp only [CollatzResearch.WordTrace]
  refine ⟨111442875700485303569057197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148590500933980404758742929 111442875700485303569057197)
  ·
    refine ⟨41791078387681988838396449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111442875700485303569057197 41791078387681988838396449)
    ·
      refine ⟨31343308790761491628797337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41791078387681988838396449 31343308790761491628797337)
      ·
        refine ⟨23507481593071118721598003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31343308790761491628797337 23507481593071118721598003)
        ·
          refine ⟨35261222389606678082397005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23507481593071118721598003 35261222389606678082397005)
          ·
            refine ⟨13222958396102504280898877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35261222389606678082397005 13222958396102504280898877)
            ·
              refine ⟨4958609398538439105337079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13222958396102504280898877 4958609398538439105337079)
              ·
                refine ⟨7437914097807658658005619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4958609398538439105337079 7437914097807658658005619)
                ·
                  refine ⟨11156871146711487987008429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7437914097807658658005619 11156871146711487987008429)
                  ·
                    refine ⟨4183826680016807995128161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11156871146711487987008429 4183826680016807995128161)
                    ·
                      refine ⟨3137870010012605996346121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4183826680016807995128161 3137870010012605996346121)
                      ·
                        rfl

theorem cell23_6110980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_6110980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6110980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6110980 prefixEnd_6110980 := by exact prefixLift 6110980
  have htrace : WordTrace (prefixWord ++ tailWord_6110980) baseStart_6110980 baseEnd_6110980 := by
    simpa [prefixWord, tailWord_6110980, baseEnd_6110980] using wordTrace_append hprefix tailTrace_6110980
  have hstable : (prefixWord ++ tailWord_6110980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6110980).length < 2 ^ (prefixWord ++ tailWord_6110980).sum := by decide
  have hdescent : baseEnd_6110980 < baseStart_6110980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6110980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111009 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 1, 5, 3]
def baseStart_6111009 : Nat := 118140960795 + 6111009 * 2 ^ 59
def prefixEnd_6111009 : Nat := 4983230072969 + 3 ^ 40 * 6111009 * 2
def baseEnd_6111009 : Nat := 3137884900951586382883487

theorem tailTrace_6111009 : CollatzResearch.WordTrace tailWord_6111009 prefixEnd_6111009 3137884900951586382883487 := by
  unfold tailWord_6111009
  simp only [CollatzResearch.WordTrace]
  refine ⟨222886809117865545090920081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148591206078577030060613387 222886809117865545090920081)
  ·
    refine ⟨167165106838399158818190061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222886809117865545090920081 167165106838399158818190061)
    ·
      refine ⟨62686915064399684556821273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167165106838399158818190061 62686915064399684556821273)
      ·
        refine ⟨47015186298299763417615955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62686915064399684556821273 47015186298299763417615955)
        ·
          refine ⟨70522779447449645126423933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47015186298299763417615955 70522779447449645126423933)
          ·
            refine ⟨26446042292793616922408975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70522779447449645126423933 26446042292793616922408975)
            ·
              refine ⟨39669063439190425383613463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26446042292793616922408975 39669063439190425383613463)
              ·
                refine ⟨59503595158785638075420195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39669063439190425383613463 59503595158785638075420195)
                ·
                  refine ⟨89255392738178457113130293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59503595158785638075420195 89255392738178457113130293)
                  ·
                    refine ⟨8367693069204230354355965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89255392738178457113130293 8367693069204230354355965)
                    ·
                      refine ⟨3137884900951586382883487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8367693069204230354355965 3137884900951586382883487)
                      ·
                        rfl

theorem cell23_6111009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_6111009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111009 prefixEnd_6111009 := by exact prefixLift 6111009
  have htrace : WordTrace (prefixWord ++ tailWord_6111009) baseStart_6111009 baseEnd_6111009 := by
    simpa [prefixWord, tailWord_6111009, baseEnd_6111009] using wordTrace_append hprefix tailTrace_6111009
  have hstable : (prefixWord ++ tailWord_6111009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111009).length < 2 ^ (prefixWord ++ tailWord_6111009).sum := by decide
  have hdescent : baseEnd_6111009 < baseStart_6111009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111019 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 3, 7, 2]
def baseStart_6111019 : Nat := 118140960795 + 6111019 * 2 ^ 59
def prefixEnd_6111019 : Nat := 4983230072969 + 3 ^ 40 * 6111019 * 2
def baseEnd_6111019 : Nat := 3137890035758131343758441

theorem tailTrace_6111019 : CollatzResearch.WordTrace tailWord_6111019 prefixEnd_6111019 3137890035758131343758441 := by
  unfold tailWord_6111019
  simp only [CollatzResearch.WordTrace]
  refine ⟨222887173847829316798784111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148591449231886211199189407 222887173847829316798784111)
  ·
    refine ⟨334330760771743975198176167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222887173847829316798784111 334330760771743975198176167)
    ·
      refine ⟨501496141157615962797264251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334330760771743975198176167 501496141157615962797264251)
      ·
        refine ⟨752244211736423944195896377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501496141157615962797264251 752244211736423944195896377)
        ·
          refine ⟨564183158802317958146922283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 752244211736423944195896377 564183158802317958146922283)
          ·
            refine ⟨846274738203476937220383425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564183158802317958146922283 846274738203476937220383425)
            ·
              refine ⟨634706053652607702915287569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 846274738203476937220383425 634706053652607702915287569)
              ·
                refine ⟨476029540239455777186465677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634706053652607702915287569 476029540239455777186465677)
                ·
                  refine ⟨178511077589795916444924629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 476029540239455777186465677 178511077589795916444924629)
                  ·
                    refine ⟨4183853381010841791677921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 178511077589795916444924629 4183853381010841791677921)
                    ·
                      refine ⟨3137890035758131343758441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4183853381010841791677921 3137890035758131343758441)
                      ·
                        rfl

theorem cell23_6111019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 7, 2].length) (baseStart_6111019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111019 prefixEnd_6111019 := by exact prefixLift 6111019
  have htrace : WordTrace (prefixWord ++ tailWord_6111019) baseStart_6111019 baseEnd_6111019 := by
    simpa [prefixWord, tailWord_6111019, baseEnd_6111019] using wordTrace_append hprefix tailTrace_6111019
  have hstable : (prefixWord ++ tailWord_6111019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111019).length < 2 ^ (prefixWord ++ tailWord_6111019).sum := by decide
  have hdescent : baseEnd_6111019 < baseStart_6111019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111049 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 4, 1, 4]
def baseStart_6111049 : Nat := 118140960795 + 6111049 * 2 ^ 59
def prefixEnd_6111049 : Nat := 4983230072969 + 3 ^ 40 * 6111049 * 2
def baseEnd_6111049 : Nat := 3137905440177766226383303

theorem tailTrace_6111049 : CollatzResearch.WordTrace tailWord_6111049 prefixEnd_6111049 3137905440177766226383303 := by
  unfold tailWord_6111049
  simp only [CollatzResearch.WordTrace]
  refine ⟨222888268037720631922376201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148592178691813754614917467 222888268037720631922376201)
  ·
    refine ⟨167166201028290473941782151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222888268037720631922376201 167166201028290473941782151)
    ·
      refine ⟨250749301542435710912673227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167166201028290473941782151 250749301542435710912673227)
      ·
        refine ⟨376123952313653566369009841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250749301542435710912673227 376123952313653566369009841)
        ·
          refine ⟨282092964235240174776757381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376123952313653566369009841 282092964235240174776757381)
          ·
            refine ⟨52892430794107532770642009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 282092964235240174776757381 52892430794107532770642009)
            ·
              refine ⟨39669323095580649577981507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52892430794107532770642009 39669323095580649577981507)
              ·
                refine ⟨59503984643370974366972261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39669323095580649577981507 59503984643370974366972261)
                ·
                  refine ⟨11156997120632057693807299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59503984643370974366972261 11156997120632057693807299)
                  ·
                    refine ⟨16735495680948086540710949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11156997120632057693807299 16735495680948086540710949)
                    ·
                      refine ⟨3137905440177766226383303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16735495680948086540710949 3137905440177766226383303)
                      ·
                        rfl

theorem cell23_6111049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 1, 4].length) (baseStart_6111049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111049 prefixEnd_6111049 := by exact prefixLift 6111049
  have htrace : WordTrace (prefixWord ++ tailWord_6111049) baseStart_6111049 baseEnd_6111049 := by
    simpa [prefixWord, tailWord_6111049, baseEnd_6111049] using wordTrace_append hprefix tailTrace_6111049
  have hstable : (prefixWord ++ tailWord_6111049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111049).length < 2 ^ (prefixWord ++ tailWord_6111049).sum := by decide
  have hdescent : baseEnd_6111049 < baseStart_6111049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111066 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2]
def baseStart_6111066 : Nat := 118140960795 + 6111066 * 2 ^ 59
def prefixEnd_6111066 : Nat := 4983230072969 + 3 ^ 40 * 6111066 * 2
def baseEnd_6111066 : Nat := 3137914169348892659870725

theorem tailTrace_6111066 : CollatzResearch.WordTrace tailWord_6111066 prefixEnd_6111066 3137914169348892659870725 := by
  unfold tailWord_6111066
  simp only [CollatzResearch.WordTrace]
  refine ⟨55722222019664760956436263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148592592052439362550496701 55722222019664760956436263)
  ·
    refine ⟨83583333029497141434654395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55722222019664760956436263 83583333029497141434654395)
    ·
      refine ⟨125374999544245712151981593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83583333029497141434654395 125374999544245712151981593)
      ·
        refine ⟨94031249658184284113986195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125374999544245712151981593 94031249658184284113986195)
        ·
          refine ⟨141046874487276426170979293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94031249658184284113986195 141046874487276426170979293)
          ·
            refine ⟨52892577932728659814117235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141046874487276426170979293 52892577932728659814117235)
            ·
              refine ⟨79338866899092989721175853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52892577932728659814117235 79338866899092989721175853)
              ·
                refine ⟨29752075087159871145440945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79338866899092989721175853 29752075087159871145440945)
                ·
                  refine ⟨22314056315369903359080709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29752075087159871145440945 22314056315369903359080709)
                  ·
                    refine ⟨4183885559131856879827633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22314056315369903359080709 4183885559131856879827633)
                    ·
                      refine ⟨3137914169348892659870725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4183885559131856879827633 3137914169348892659870725)
                      ·
                        rfl

theorem cell23_6111066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_6111066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111066 prefixEnd_6111066 := by exact prefixLift 6111066
  have htrace : WordTrace (prefixWord ++ tailWord_6111066) baseStart_6111066 baseEnd_6111066 := by
    simpa [prefixWord, tailWord_6111066, baseEnd_6111066] using wordTrace_append hprefix tailTrace_6111066
  have hstable : (prefixWord ++ tailWord_6111066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111066).length < 2 ^ (prefixWord ++ tailWord_6111066).sum := by decide
  have hdescent : baseEnd_6111066 < baseStart_6111066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111079 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_6111079 : Nat := 118140960795 + 6111079 * 2 ^ 59
def prefixEnd_6111079 : Nat := 4983230072969 + 3 ^ 40 * 6111079 * 2
def baseEnd_6111079 : Nat := 3137920844597401109008165

theorem tailTrace_6111079 : CollatzResearch.WordTrace tailWord_6111079 prefixEnd_6111079 3137920844597401109008165 := by
  unfold tailWord_6111079
  simp only [CollatzResearch.WordTrace]
  refine ⟨222889362227611947045968291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148592908151741298030645527 222889362227611947045968291)
  ·
    refine ⟨334334043341417920568952437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222889362227611947045968291 334334043341417920568952437)
    ·
      refine ⟨31343816563257930053339291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 334334043341417920568952437 31343816563257930053339291)
      ·
        refine ⟨47015724844886895080008937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31343816563257930053339291 47015724844886895080008937)
        ·
          refine ⟨35261793633665171310006703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47015724844886895080008937 35261793633665171310006703)
          ·
            refine ⟨52892690450497756965010055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35261793633665171310006703 52892690450497756965010055)
            ·
              refine ⟨79339035675746635447515083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52892690450497756965010055 79339035675746635447515083)
              ·
                refine ⟨119008553513619953171272625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79339035675746635447515083 119008553513619953171272625)
                ·
                  refine ⟨89256415135214964878454469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119008553513619953171272625 89256415135214964878454469)
                  ·
                    refine ⟨16735577837852805914710213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89256415135214964878454469 16735577837852805914710213)
                    ·
                      refine ⟨3137920844597401109008165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16735577837852805914710213 3137920844597401109008165)
                      ·
                        rfl

theorem cell23_6111079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_6111079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111079 prefixEnd_6111079 := by exact prefixLift 6111079
  have htrace : WordTrace (prefixWord ++ tailWord_6111079) baseStart_6111079 baseEnd_6111079 := by
    simpa [prefixWord, tailWord_6111079, baseEnd_6111079] using wordTrace_append hprefix tailTrace_6111079
  have hstable : (prefixWord ++ tailWord_6111079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111079).length < 2 ^ (prefixWord ++ tailWord_6111079).sum := by decide
  have hdescent : baseEnd_6111079 < baseStart_6111079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111207 : List Nat := [1, 1, 5, 2, 3, 2, 2, 1, 1, 1, 4]
def baseStart_6111207 : Nat := 118140960795 + 6111207 * 2 ^ 59
def prefixEnd_6111207 : Nat := 4983230072969 + 3 ^ 40 * 6111207 * 2
def baseEnd_6111207 : Nat := 3137986570121176608207577

theorem tailTrace_6111207 : CollatzResearch.WordTrace tailWord_6111207 prefixEnd_6111207 3137986570121176608207577 := by
  unfold tailWord_6111207
  simp only [CollatzResearch.WordTrace]
  refine ⟨222894030771148224906627875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148596020514098816604418583 222894030771148224906627875)
  ·
    refine ⟨334341046156722337359941813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222894030771148224906627875 334341046156722337359941813)
    ·
      refine ⟨31344473077192719127494545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 334341046156722337359941813 31344473077192719127494545)
      ·
        refine ⟨23508354807894539345620909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31344473077192719127494545 23508354807894539345620909)
        ·
          refine ⟨8815633052960452254607841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23508354807894539345620909 8815633052960452254607841)
          ·
            refine ⟨6611724789720339190955881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8815633052960452254607841 6611724789720339190955881)
            ·
              refine ⟨4958793592290254393216911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6611724789720339190955881 4958793592290254393216911)
              ·
                refine ⟨7438190388435381589825367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4958793592290254393216911 7438190388435381589825367)
                ·
                  refine ⟨11157285582653072384738051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7438190388435381589825367 11157285582653072384738051)
                  ·
                    refine ⟨16735928373979608577107077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11157285582653072384738051 16735928373979608577107077)
                    ·
                      refine ⟨3137986570121176608207577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16735928373979608577107077 3137986570121176608207577)
                      ·
                        rfl

theorem cell23_6111207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_6111207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111207 prefixEnd_6111207 := by exact prefixLift 6111207
  have htrace : WordTrace (prefixWord ++ tailWord_6111207) baseStart_6111207 baseEnd_6111207 := by
    simpa [prefixWord, tailWord_6111207, baseEnd_6111207] using wordTrace_append hprefix tailTrace_6111207
  have hstable : (prefixWord ++ tailWord_6111207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111207).length < 2 ^ (prefixWord ++ tailWord_6111207).sum := by decide
  have hdescent : baseEnd_6111207 < baseStart_6111207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111213 : List Nat := [1, 5, 1, 4, 1, 1, 10]
def baseStart_6111213 : Nat := 118140960795 + 6111213 * 2 ^ 59
def prefixEnd_6111213 : Nat := 4983230072969 + 3 ^ 40 * 6111213 * 2
def baseEnd_6111213 : Nat := 38740612975371649194229

theorem tailTrace_6111213 : CollatzResearch.WordTrace tailWord_6111213 prefixEnd_6111213 38740612975371649194229 := by
  unfold tailWord_6111213
  simp only [CollatzResearch.WordTrace]
  refine ⟨222894249609126487931346293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148596166406084325287564195 222894249609126487931346293)
  ·
    refine ⟨20896335900855608243563715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222894249609126487931346293 20896335900855608243563715)
    ·
      refine ⟨31344503851283412365345573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20896335900855608243563715 31344503851283412365345573)
      ·
        refine ⟨5877094472115639818502295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31344503851283412365345573 5877094472115639818502295)
        ·
          refine ⟨8815641708173459727753443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5877094472115639818502295 8815641708173459727753443)
          ·
            refine ⟨13223462562260189591630165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8815641708173459727753443 13223462562260189591630165)
            ·
              refine ⟨38740612975371649194229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13223462562260189591630165 38740612975371649194229)
              ·
                rfl

theorem cell23_6111213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 10].length) (baseStart_6111213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111213 prefixEnd_6111213 := by exact prefixLift 6111213
  have htrace : WordTrace (prefixWord ++ tailWord_6111213) baseStart_6111213 baseEnd_6111213 := by
    simpa [prefixWord, tailWord_6111213, baseEnd_6111213] using wordTrace_append hprefix tailTrace_6111213
  have hstable : (prefixWord ++ tailWord_6111213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111213).length < 2 ^ (prefixWord ++ tailWord_6111213).sum := by decide
  have hdescent : baseEnd_6111213 < baseStart_6111213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111217 : List Nat := [1, 2, 2, 2, 6, 1, 1, 2, 2, 4]
def baseStart_6111217 : Nat := 118140960795 + 6111217 * 2 ^ 59
def prefixEnd_6111217 : Nat := 4983230072969 + 3 ^ 40 * 6111217 * 2
def baseEnd_6111217 : Nat := 1045997234975907189694177

theorem tailTrace_6111217 : CollatzResearch.WordTrace tailWord_6111217 prefixEnd_6111217 1045997234975907189694177 := by
  unfold tailWord_6111217
  simp only [CollatzResearch.WordTrace]
  refine ⟨222894395501111996614491905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148596263667407997742994603 222894395501111996614491905)
  ·
    refine ⟨167170796625833997460868929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222894395501111996614491905 167170796625833997460868929)
    ·
      refine ⟨125378097469375498095651697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167170796625833997460868929 125378097469375498095651697)
      ·
        refine ⟨94033573102031623571738773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125378097469375498095651697 94033573102031623571738773)
        ·
          refine ⟨4407823739157732354925255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94033573102031623571738773 4407823739157732354925255)
          ·
            refine ⟨6611735608736598532387883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4407823739157732354925255 6611735608736598532387883)
            ·
              refine ⟨9917603413104897798581825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6611735608736598532387883 9917603413104897798581825)
              ·
                refine ⟨7438202559828673348936369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9917603413104897798581825 7438202559828673348936369)
                ·
                  refine ⟨5578651919871505011702277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7438202559828673348936369 5578651919871505011702277)
                  ·
                    refine ⟨1045997234975907189694177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5578651919871505011702277 1045997234975907189694177)
                    ·
                      rfl

theorem cell23_6111217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_6111217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111217 prefixEnd_6111217 := by exact prefixLift 6111217
  have htrace : WordTrace (prefixWord ++ tailWord_6111217) baseStart_6111217 baseEnd_6111217 := by
    simpa [prefixWord, tailWord_6111217, baseEnd_6111217] using wordTrace_append hprefix tailTrace_6111217
  have hstable : (prefixWord ++ tailWord_6111217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111217).length < 2 ^ (prefixWord ++ tailWord_6111217).sum := by decide
  have hdescent : baseEnd_6111217 < baseStart_6111217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111263 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 3, 4, 2]
def baseStart_6111263 : Nat := 118140960795 + 6111263 * 2 ^ 59
def prefixEnd_6111263 : Nat := 4983230072969 + 3 ^ 40 * 6111263 * 2
def baseEnd_6111263 : Nat := 3138015325037828389107319

theorem tailTrace_6111263 : CollatzResearch.WordTrace tailWord_6111263 prefixEnd_6111263 3138015325037828389107319 := by
  unfold tailWord_6111263
  simp only [CollatzResearch.WordTrace]
  refine ⟨222896073258945346470666443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148597382172630230980444295 222896073258945346470666443)
  ·
    refine ⟨334344109888418019705999665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222896073258945346470666443 334344109888418019705999665)
    ·
      refine ⟨250758082416313514779499749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334344109888418019705999665 250758082416313514779499749)
      ·
        refine ⟨47017140453058784021156203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250758082416313514779499749 47017140453058784021156203)
        ·
          refine ⟨70525710679588176031734305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47017140453058784021156203 70525710679588176031734305)
          ·
            refine ⟨52894283009691132023800729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70525710679588176031734305 52894283009691132023800729)
            ·
              refine ⟨39670712257268349017850547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52894283009691132023800729 39670712257268349017850547)
              ·
                refine ⟨59506068385902523526775821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39670712257268349017850547 59506068385902523526775821)
                ·
                  refine ⟨22314775644713446322540933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59506068385902523526775821 22314775644713446322540933)
                  ·
                    refine ⟨4184020433383771185476425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22314775644713446322540933 4184020433383771185476425)
                    ·
                      refine ⟨3138015325037828389107319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4184020433383771185476425 3138015325037828389107319)
                      ·
                        rfl

theorem cell23_6111263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_6111263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111263 prefixEnd_6111263 := by exact prefixLift 6111263
  have htrace : WordTrace (prefixWord ++ tailWord_6111263) baseStart_6111263 baseEnd_6111263 := by
    simpa [prefixWord, tailWord_6111263, baseEnd_6111263] using wordTrace_append hprefix tailTrace_6111263
  have hstable : (prefixWord ++ tailWord_6111263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111263).length < 2 ^ (prefixWord ++ tailWord_6111263).sum := by decide
  have hdescent : baseEnd_6111263 < baseStart_6111263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111276 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 4]
def baseStart_6111276 : Nat := 118140960795 + 6111276 * 2 ^ 59
def prefixEnd_6111276 : Nat := 4983230072969 + 3 ^ 40 * 6111276 * 2
def baseEnd_6111276 : Nat := 3138022000286336838244759

theorem tailTrace_6111276 : CollatzResearch.WordTrace tailWord_6111276 prefixEnd_6111276 3138022000286336838244759 := by
  unfold tailWord_6111276
  simp only [CollatzResearch.WordTrace]
  refine ⟨111448273703949124845444841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148597698271932166460593121 111448273703949124845444841)
  ·
    refine ⟨83586205277961843634083631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111448273703949124845444841 83586205277961843634083631)
    ·
      refine ⟨125379307916942765451125447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83586205277961843634083631 125379307916942765451125447)
      ·
        refine ⟨188068961875414148176688171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125379307916942765451125447 188068961875414148176688171)
        ·
          refine ⟨282103442813121222265032257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188068961875414148176688171 282103442813121222265032257)
          ·
            refine ⟨211577582109840916698774193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282103442813121222265032257 211577582109840916698774193)
            ·
              refine ⟨158683186582380687524080645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211577582109840916698774193 158683186582380687524080645)
              ·
                refine ⟨29753097484196378910765121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158683186582380687524080645 29753097484196378910765121)
                ·
                  refine ⟨22314823113147284183073841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29753097484196378910765121 22314823113147284183073841)
                  ·
                    refine ⟨16736117334860463137305381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22314823113147284183073841 16736117334860463137305381)
                    ·
                      refine ⟨3138022000286336838244759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16736117334860463137305381 3138022000286336838244759)
                      ·
                        rfl

theorem cell23_6111276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_6111276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111276 prefixEnd_6111276 := by exact prefixLift 6111276
  have htrace : WordTrace (prefixWord ++ tailWord_6111276) baseStart_6111276 baseEnd_6111276 := by
    simpa [prefixWord, tailWord_6111276, baseEnd_6111276] using wordTrace_append hprefix tailTrace_6111276
  have hstable : (prefixWord ++ tailWord_6111276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111276).length < 2 ^ (prefixWord ++ tailWord_6111276).sum := by decide
  have hdescent : baseEnd_6111276 < baseStart_6111276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111280 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 4, 2, 2]
def baseStart_6111280 : Nat := 118140960795 + 6111280 * 2 ^ 59
def prefixEnd_6111280 : Nat := 4983230072969 + 3 ^ 40 * 6111280 * 2
def baseEnd_6111280 : Nat := 3138024054208954822594741

theorem tailTrace_6111280 : CollatzResearch.WordTrace tailWord_6111280 prefixEnd_6111280 3138024054208954822594741 := by
  unfold tailWord_6111280
  simp only [CollatzResearch.WordTrace]
  refine ⟨111448346649941879187017647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148597795533255838916023529 111448346649941879187017647)
  ·
    refine ⟨167172519974912818780526471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111448346649941879187017647 167172519974912818780526471)
    ·
      refine ⟨250758779962369228170789707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167172519974912818780526471 250758779962369228170789707)
      ·
        refine ⟨376138169943553842256184561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250758779962369228170789707 376138169943553842256184561)
        ·
          refine ⟨282103627457665381692138421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376138169943553842256184561 282103627457665381692138421)
          ·
            refine ⟨26447215074156129533637977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 282103627457665381692138421 26447215074156129533637977)
            ·
              refine ⟨19835411305617097150228483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26447215074156129533637977 19835411305617097150228483)
              ·
                refine ⟨29753116958425645725342725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19835411305617097150228483 29753116958425645725342725)
                ·
                  refine ⟨5578709429704808573501761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29753116958425645725342725 5578709429704808573501761)
                  ·
                    refine ⟨4184032072278606430126321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5578709429704808573501761 4184032072278606430126321)
                    ·
                      refine ⟨3138024054208954822594741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4184032072278606430126321 3138024054208954822594741)
                      ·
                        rfl

theorem cell23_6111280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 4, 2, 2].length) (baseStart_6111280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111280 prefixEnd_6111280 := by exact prefixLift 6111280
  have htrace : WordTrace (prefixWord ++ tailWord_6111280) baseStart_6111280 baseEnd_6111280 := by
    simpa [prefixWord, tailWord_6111280, baseEnd_6111280] using wordTrace_append hprefix tailTrace_6111280
  have hstable : (prefixWord ++ tailWord_6111280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111280).length < 2 ^ (prefixWord ++ tailWord_6111280).sum := by decide
  have hdescent : baseEnd_6111280 < baseStart_6111280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111333 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 2, 5]
def baseStart_6111333 : Nat := 118140960795 + 6111333 * 2 ^ 59
def prefixEnd_6111333 : Nat := 4983230072969 + 3 ^ 40 * 6111333 * 2
def baseEnd_6111333 : Nat := 1046017089561214371743999

theorem tailTrace_6111333 : CollatzResearch.WordTrace tailWord_6111333 prefixEnd_6111333 1046017089561214371743999 := by
  unfold tailWord_6111333
  simp only [CollatzResearch.WordTrace]
  refine ⟨222898626368691748425714653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148599084245794498950476435 222898626368691748425714653)
  ·
    refine ⟨83586984888259405659642995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222898626368691748425714653 83586984888259405659642995)
    ·
      refine ⟨125380477332389108489464493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83586984888259405659642995 125380477332389108489464493)
      ·
        refine ⟨47017678999645915683549185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125380477332389108489464493 47017678999645915683549185)
        ·
          refine ⟨35263259249734436762661889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47017678999645915683549185 35263259249734436762661889)
          ·
            refine ⟨26447444437300827571996417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35263259249734436762661889 26447444437300827571996417)
            ·
              refine ⟨19835583327975620678997313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26447444437300827571996417 19835583327975620678997313)
              ·
                refine ⟨14876687495981715509247985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19835583327975620678997313 14876687495981715509247985)
                ·
                  refine ⟨11157515621986286631935989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14876687495981715509247985 11157515621986286631935989)
                  ·
                    refine ⟨1046017089561214371743999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11157515621986286631935989 1046017089561214371743999)
                    ·
                      rfl

theorem cell23_6111333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_6111333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111333 prefixEnd_6111333 := by exact prefixLift 6111333
  have htrace : WordTrace (prefixWord ++ tailWord_6111333) baseStart_6111333 baseEnd_6111333 := by
    simpa [prefixWord, tailWord_6111333, baseEnd_6111333] using wordTrace_append hprefix tailTrace_6111333
  have hstable : (prefixWord ++ tailWord_6111333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111333).length < 2 ^ (prefixWord ++ tailWord_6111333).sum := by decide
  have hdescent : baseEnd_6111333 < baseStart_6111333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111363 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 5, 4]
def baseStart_6111363 : Nat := 118140960795 + 6111363 * 2 ^ 59
def prefixEnd_6111363 : Nat := 4983230072969 + 3 ^ 40 * 6111363 * 2
def baseEnd_6111363 : Nat := 1046022224367759332618953

theorem tailTrace_6111363 : CollatzResearch.WordTrace tailWord_6111363 prefixEnd_6111363 1046022224367759332618953 := by
  unfold tailWord_6111363
  simp only [CollatzResearch.WordTrace]
  refine ⟨222899720558583063549306743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148599813705722042366204495 222899720558583063549306743)
  ·
    refine ⟨334349580837874595323960115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222899720558583063549306743 334349580837874595323960115)
    ·
      refine ⟨501524371256811892985940173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334349580837874595323960115 501524371256811892985940173)
      ·
        refine ⟨188071639221304459869727565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 501524371256811892985940173 188071639221304459869727565)
        ·
          refine ⟨70526864707989172451147837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188071639221304459869727565 70526864707989172451147837)
          ·
            refine ⟨26447574265495939669180439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70526864707989172451147837 26447574265495939669180439)
            ·
              refine ⟨39671361398243909503770659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26447574265495939669180439 39671361398243909503770659)
              ·
                refine ⟨59507042097365864255655989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39671361398243909503770659 59507042097365864255655989)
                ·
                  refine ⟨5578785196628049773967749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59507042097365864255655989 5578785196628049773967749)
                  ·
                    refine ⟨1046022224367759332618953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5578785196628049773967749 1046022224367759332618953)
                    ·
                      rfl

theorem cell23_6111363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 4].length) (baseStart_6111363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111363 prefixEnd_6111363 := by exact prefixLift 6111363
  have htrace : WordTrace (prefixWord ++ tailWord_6111363) baseStart_6111363 baseEnd_6111363 := by
    simpa [prefixWord, tailWord_6111363, baseEnd_6111363] using wordTrace_append hprefix tailTrace_6111363
  have hstable : (prefixWord ++ tailWord_6111363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111363).length < 2 ^ (prefixWord ++ tailWord_6111363).sum := by decide
  have hdescent : baseEnd_6111363 < baseStart_6111363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111370 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 2, 1, 4]
def baseStart_6111370 : Nat := 118140960795 + 6111370 * 2 ^ 59
def prefixEnd_6111370 : Nat := 4983230072969 + 3 ^ 40 * 6111370 * 2
def baseEnd_6111370 : Nat := 3138070267467859470469327

theorem tailTrace_6111370 : CollatzResearch.WordTrace tailWord_6111370 prefixEnd_6111370 3138070267467859470469327 := by
  unfold tailWord_6111370
  simp only [CollatzResearch.WordTrace]
  refine ⟨55724993967389425936202891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148599983913038469163207709 55724993967389425936202891)
  ·
    refine ⟨83587490951084138904304337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55724993967389425936202891 83587490951084138904304337)
    ·
      refine ⟨62690618213313104178228253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83587490951084138904304337 62690618213313104178228253)
      ·
        refine ⟨23508981829992414066835595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62690618213313104178228253 23508981829992414066835595)
        ·
          refine ⟨35263472744988621100253393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23508981829992414066835595 35263472744988621100253393)
          ·
            refine ⟨26447604558741465825190045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35263472744988621100253393 26447604558741465825190045)
            ·
              refine ⟨9917851709528049684446267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26447604558741465825190045 9917851709528049684446267)
              ·
                refine ⟨14876777564292074526669401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9917851709528049684446267 14876777564292074526669401)
                ·
                  refine ⟨11157583173219055895002051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14876777564292074526669401 11157583173219055895002051)
                  ·
                    refine ⟨16736374759828583842503077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11157583173219055895002051 16736374759828583842503077)
                    ·
                      refine ⟨3138070267467859470469327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16736374759828583842503077 3138070267467859470469327)
                      ·
                        rfl

theorem cell23_6111370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_6111370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111370 prefixEnd_6111370 := by exact prefixLift 6111370
  have htrace : WordTrace (prefixWord ++ tailWord_6111370) baseStart_6111370 baseEnd_6111370 := by
    simpa [prefixWord, tailWord_6111370, baseEnd_6111370] using wordTrace_append hprefix tailTrace_6111370
  have hstable : (prefixWord ++ tailWord_6111370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111370).length < 2 ^ (prefixWord ++ tailWord_6111370).sum := by decide
  have hdescent : baseEnd_6111370 < baseStart_6111370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111376 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 8]
def baseStart_6111376 : Nat := 118140960795 + 6111376 * 2 ^ 59
def prefixEnd_6111376 : Nat := 4983230072969 + 3 ^ 40 * 6111376 * 2
def baseEnd_6111376 : Nat := 348674816483531827443811

theorem tailTrace_6111376 : CollatzResearch.WordTrace tailWord_6111376 prefixEnd_6111376 348674816483531827443811 := by
  unfold tailWord_6111376
  simp only [CollatzResearch.WordTrace]
  refine ⟨111450097353767983384764991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148600129805023977846353321 111450097353767983384764991)
  ·
    refine ⟨167175146030651975077147487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111450097353767983384764991 167175146030651975077147487)
    ·
      refine ⟨250762719045977962615721231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167175146030651975077147487 250762719045977962615721231)
      ·
        refine ⟨376144078568966943923581847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250762719045977962615721231 376144078568966943923581847)
        ·
          refine ⟨564216117853450415885372771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376144078568966943923581847 564216117853450415885372771)
          ·
            refine ⟨846324176780175623828059157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564216117853450415885372771 846324176780175623828059157)
            ·
              refine ⟨39671445786570732366940273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 846324176780175623828059157 39671445786570732366940273)
              ·
                refine ⟨29753584339928049275205205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39671445786570732366940273 29753584339928049275205205)
                ·
                  refine ⟨348674816483531827443811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29753584339928049275205205 348674816483531827443811)
                  ·
                    rfl

theorem cell23_6111376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 8].length) (baseStart_6111376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111376 prefixEnd_6111376 := by exact prefixLift 6111376
  have htrace : WordTrace (prefixWord ++ tailWord_6111376) baseStart_6111376 baseEnd_6111376 := by
    simpa [prefixWord, tailWord_6111376, baseEnd_6111376] using wordTrace_append hprefix tailTrace_6111376
  have hstable : (prefixWord ++ tailWord_6111376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111376).length < 2 ^ (prefixWord ++ tailWord_6111376).sum := by decide
  have hdescent : baseEnd_6111376 < baseStart_6111376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111382 : List Nat := [5, 3, 2, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_6111382 : Nat := 118140960795 + 6111382 * 2 ^ 59
def prefixEnd_6111382 : Nat := 4983230072969 + 3 ^ 40 * 6111382 * 2
def baseEnd_6111382 : Nat := 3138076429235713423519273

theorem tailTrace_6111382 : CollatzResearch.WordTrace tailWord_6111382 prefixEnd_6111382 3138076429235713423519273 := by
  unfold tailWord_6111382
  simp only [CollatzResearch.WordTrace]
  refine ⟨13931275846594639362140525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148600275697009486529498933 13931275846594639362140525)
  ·
    refine ⟨5224228442472989760802697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13931275846594639362140525 5224228442472989760802697)
    ·
      refine ⟨3918171331854742320602023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5224228442472989760802697 3918171331854742320602023)
      ·
        refine ⟨5877256997782113480903035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3918171331854742320602023 5877256997782113480903035)
        ·
          refine ⟨8815885496673170221354553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5877256997782113480903035 8815885496673170221354553)
          ·
            refine ⟨6611914122504877666015915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8815885496673170221354553 6611914122504877666015915)
            ·
              refine ⟨9917871183757316499023873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6611914122504877666015915 9917871183757316499023873)
              ·
                refine ⟨7438403387817987374267905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9917871183757316499023873 7438403387817987374267905)
                ·
                  refine ⟨5578802540863490530700929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7438403387817987374267905 5578802540863490530700929)
                  ·
                    refine ⟨4184101905647617898025697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5578802540863490530700929 4184101905647617898025697)
                    ·
                      refine ⟨3138076429235713423519273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4184101905647617898025697 3138076429235713423519273)
                      ·
                        rfl

theorem cell23_6111382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_6111382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111382 prefixEnd_6111382 := by exact prefixLift 6111382
  have htrace : WordTrace (prefixWord ++ tailWord_6111382) baseStart_6111382 baseEnd_6111382 := by
    simpa [prefixWord, tailWord_6111382, baseEnd_6111382] using wordTrace_append hprefix tailTrace_6111382
  have hstable : (prefixWord ++ tailWord_6111382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111382).length < 2 ^ (prefixWord ++ tailWord_6111382).sum := by decide
  have hdescent : baseEnd_6111382 < baseStart_6111382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111393 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 8]
def baseStart_6111393 : Nat := 118140960795 + 6111393 * 2 ^ 59
def prefixEnd_6111393 : Nat := 4983230072969 + 3 ^ 40 * 6111393 * 2
def baseEnd_6111393 : Nat := 348675786391434764497969

theorem tailTrace_6111393 : CollatzResearch.WordTrace tailWord_6111393 prefixEnd_6111393 348675786391434764497969 := by
  unfold tailWord_6111393
  simp only [CollatzResearch.WordTrace]
  refine ⟨222900814748474378672898833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148600543165649585781932555 222900814748474378672898833)
  ·
    refine ⟨167175611061355784004674125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222900814748474378672898833 167175611061355784004674125)
    ·
      refine ⟨62690854148008419001752797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167175611061355784004674125 62690854148008419001752797)
      ·
        refine ⟨23509070305503157125657299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62690854148008419001752797 23509070305503157125657299)
        ·
          refine ⟨35263605458254735688485949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23509070305503157125657299 35263605458254735688485949)
          ·
            refine ⟨13223852046845525883182231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35263605458254735688485949 13223852046845525883182231)
            ·
              refine ⟨19835778070268288824773347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13223852046845525883182231 19835778070268288824773347)
              ·
                refine ⟨29753667105402433237160021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19835778070268288824773347 29753667105402433237160021)
                ·
                  refine ⟨348675786391434764497969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29753667105402433237160021 348675786391434764497969)
                  ·
                    rfl

theorem cell23_6111393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 8].length) (baseStart_6111393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111393 prefixEnd_6111393 := by exact prefixLift 6111393
  have htrace : WordTrace (prefixWord ++ tailWord_6111393) baseStart_6111393 baseEnd_6111393 := by
    simpa [prefixWord, tailWord_6111393, baseEnd_6111393] using wordTrace_append hprefix tailTrace_6111393
  have hstable : (prefixWord ++ tailWord_6111393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111393).length < 2 ^ (prefixWord ++ tailWord_6111393).sum := by decide
  have hdescent : baseEnd_6111393 < baseStart_6111393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111410 : List Nat := [3, 2, 1, 1, 1, 3, 5, 1, 6]
def baseStart_6111410 : Nat := 118140960795 + 6111410 * 2 ^ 59
def prefixEnd_6111410 : Nat := 4983230072969 + 3 ^ 40 * 6111410 * 2
def baseEnd_6111410 : Nat := 348676756299337701552127

theorem tailTrace_6111410 : CollatzResearch.WordTrace tailWord_6111410 prefixEnd_6111410 348676756299337701552127 := by
  unfold tailWord_6111410
  simp only [CollatzResearch.WordTrace]
  refine ⟨55725358697353197644066921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148600956526275193717511789 55725358697353197644066921)
  ·
    refine ⟨41794019023014898233050191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55725358697353197644066921 41794019023014898233050191)
    ·
      refine ⟨62691028534522347349575287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41794019023014898233050191 62691028534522347349575287)
      ·
        refine ⟨94036542801783521024362931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62691028534522347349575287 94036542801783521024362931)
        ·
          refine ⟨141054814202675281536544397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94036542801783521024362931 141054814202675281536544397)
          ·
            refine ⟨52895555326003230576204149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141054814202675281536544397 52895555326003230576204149)
            ·
              refine ⟨4958958311812802866519139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52895555326003230576204149 4958958311812802866519139)
              ·
                refine ⟨7438437467719204299778709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4958958311812802866519139 7438437467719204299778709)
                ·
                  refine ⟨348676756299337701552127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7438437467719204299778709 348676756299337701552127)
                  ·
                    rfl

theorem cell23_6111410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_6111410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111410 prefixEnd_6111410 := by exact prefixLift 6111410
  have htrace : WordTrace (prefixWord ++ tailWord_6111410) baseStart_6111410 baseEnd_6111410 := by
    simpa [prefixWord, tailWord_6111410, baseEnd_6111410] using wordTrace_append hprefix tailTrace_6111410
  have hstable : (prefixWord ++ tailWord_6111410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111410).length < 2 ^ (prefixWord ++ tailWord_6111410).sum := by decide
  have hdescent : baseEnd_6111410 < baseStart_6111410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111473 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 1, 1, 6]
def baseStart_6111473 : Nat := 118140960795 + 6111473 * 2 ^ 59
def prefixEnd_6111473 : Nat := 4983230072969 + 3 ^ 40 * 6111473 * 2
def baseEnd_6111473 : Nat := 3138123155975272567481353

theorem tailTrace_6111473 : CollatzResearch.WordTrace tailWord_6111473 prefixEnd_6111473 3138123155975272567481353 := by
  unfold tailWord_6111473
  simp only [CollatzResearch.WordTrace]
  refine ⟨222903732588184552335811073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148602488392123034890540715 222903732588184552335811073)
  ·
    refine ⟨167177799441138414251858305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222903732588184552335811073 167177799441138414251858305)
    ·
      refine ⟨125383349580853810688893729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167177799441138414251858305 125383349580853810688893729)
      ·
        refine ⟨94037512185640358016670297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125383349580853810688893729 94037512185640358016670297)
        ·
          refine ⟨70528134139230268512502723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94037512185640358016670297 70528134139230268512502723)
          ·
            refine ⟨105792201208845402768754085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70528134139230268512502723 105792201208845402768754085)
            ·
              refine ⟨19836037726658513019141391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105792201208845402768754085 19836037726658513019141391)
              ·
                refine ⟨29754056589987769528712087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19836037726658513019141391 29754056589987769528712087)
                ·
                  refine ⟨44631084884981654293068131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29754056589987769528712087 44631084884981654293068131)
                  ·
                    refine ⟨66946627327472481439602197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44631084884981654293068131 66946627327472481439602197)
                    ·
                      refine ⟨3138123155975272567481353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66946627327472481439602197 3138123155975272567481353)
                      ·
                        rfl

theorem cell23_6111473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_6111473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111473 prefixEnd_6111473 := by exact prefixLift 6111473
  have htrace : WordTrace (prefixWord ++ tailWord_6111473) baseStart_6111473 baseEnd_6111473 := by
    simpa [prefixWord, tailWord_6111473, baseEnd_6111473] using wordTrace_append hprefix tailTrace_6111473
  have hstable : (prefixWord ++ tailWord_6111473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111473).length < 2 ^ (prefixWord ++ tailWord_6111473).sum := by decide
  have hdescent : baseEnd_6111473 < baseStart_6111473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111511 : List Nat := [1, 1, 3, 4, 1, 3, 1, 4, 1, 2, 2]
def baseStart_6111511 : Nat := 118140960795 + 6111511 * 2 ^ 59
def prefixEnd_6111511 : Nat := 4983230072969 + 3 ^ 40 * 6111511 * 2
def baseEnd_6111511 : Nat := 3138142668240143418806179

theorem tailTrace_6111511 : CollatzResearch.WordTrace tailWord_6111511 prefixEnd_6111511 3138142668240143418806179 := by
  unfold tailWord_6111511
  simp only [CollatzResearch.WordTrace]
  refine ⟨222905118562046884825694387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148603412374697923217129591 222905118562046884825694387)
  ·
    refine ⟨334357677843070327238541581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222905118562046884825694387 334357677843070327238541581)
    ·
      refine ⟨125384129191151372714453093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334357677843070327238541581 125384129191151372714453093)
      ·
        refine ⟨23509524223340882383959955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125384129191151372714453093 23509524223340882383959955)
        ·
          refine ⟨35264286335011323575939933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23509524223340882383959955 35264286335011323575939933)
          ·
            refine ⟨13224107375629246340977475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35264286335011323575939933 13224107375629246340977475)
            ·
              refine ⟨19836161063443869511466213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13224107375629246340977475 19836161063443869511466213)
              ·
                refine ⟨3719280199395725533399915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19836161063443869511466213 3719280199395725533399915)
                ·
                  refine ⟨5578920299093588300099873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3719280199395725533399915 5578920299093588300099873)
                  ·
                    refine ⟨4184190224320191225074905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5578920299093588300099873 4184190224320191225074905)
                    ·
                      refine ⟨3138142668240143418806179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4184190224320191225074905 3138142668240143418806179)
                      ·
                        rfl

theorem cell23_6111511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_6111511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111511 prefixEnd_6111511 := by exact prefixLift 6111511
  have htrace : WordTrace (prefixWord ++ tailWord_6111511) baseStart_6111511 baseEnd_6111511 := by
    simpa [prefixWord, tailWord_6111511, baseEnd_6111511] using wordTrace_append hprefix tailTrace_6111511
  have hstable : (prefixWord ++ tailWord_6111511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111511).length < 2 ^ (prefixWord ++ tailWord_6111511).sum := by decide
  have hdescent : baseEnd_6111511 < baseStart_6111511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111517 : List Nat := [1, 4, 2, 3, 2, 2, 1, 8]
def baseStart_6111517 : Nat := 118140960795 + 6111517 * 2 ^ 59
def prefixEnd_6111517 : Nat := 4983230072969 + 3 ^ 40 * 6111517 * 2
def baseEnd_6111517 : Nat := 116227620337928533160413

theorem tailTrace_6111517 : CollatzResearch.WordTrace tailWord_6111517 prefixEnd_6111517 116227620337928533160413 := by
  unfold tailWord_6111517
  simp only [CollatzResearch.WordTrace]
  refine ⟨222905337400025147850412805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148603558266683431900275203 222905337400025147850412805)
  ·
    refine ⟨41794750762504715221952401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222905337400025147850412805 41794750762504715221952401)
    ·
      refine ⟨31346063071878536416464301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41794750762504715221952401 31346063071878536416464301)
      ·
        refine ⟨11754773651954451156174113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31346063071878536416464301 11754773651954451156174113)
        ·
          refine ⟨8816080238965838367130585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11754773651954451156174113 8816080238965838367130585)
          ·
            refine ⟨6612060179224378775347939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8816080238965838367130585 6612060179224378775347939)
            ·
              refine ⟨9918090268836568163021909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6612060179224378775347939 9918090268836568163021909)
              ·
                refine ⟨116227620337928533160413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9918090268836568163021909 116227620337928533160413)
                ·
                  rfl

theorem cell23_6111517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 8].length) (baseStart_6111517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111517 prefixEnd_6111517 := by exact prefixLift 6111517
  have htrace : WordTrace (prefixWord ++ tailWord_6111517) baseStart_6111517 baseEnd_6111517 := by
    simpa [prefixWord, tailWord_6111517, baseEnd_6111517] using wordTrace_append hprefix tailTrace_6111517
  have hstable : (prefixWord ++ tailWord_6111517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111517).length < 2 ^ (prefixWord ++ tailWord_6111517).sum := by decide
  have hdescent : baseEnd_6111517 < baseStart_6111517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111534 : List Nat := [4, 1, 3, 3, 1, 1, 3, 7]
def baseStart_6111534 : Nat := 118140960795 + 6111534 * 2 ^ 59
def prefixEnd_6111534 : Nat := 4983230072969 + 3 ^ 40 * 6111534 * 2
def baseEnd_6111534 : Nat := 116227943640562845511799

theorem tailTrace_6111534 : CollatzResearch.WordTrace tailWord_6111534 prefixEnd_6111534 116227943640562845511799 := by
  unfold tailWord_6111534
  simp only [CollatzResearch.WordTrace]
  refine ⟨27863244680120444969222707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148603971627309039835854437 27863244680120444969222707)
  ·
    refine ⟨41794867020180667453834061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27863244680120444969222707 41794867020180667453834061)
    ·
      refine ⟨15673075132567750295187773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41794867020180667453834061 15673075132567750295187773)
      ·
        refine ⟨5877403174712906360695415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15673075132567750295187773 5877403174712906360695415)
        ·
          refine ⟨8816104762069359541043123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5877403174712906360695415 8816104762069359541043123)
          ·
            refine ⟨13224157143104039311564685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8816104762069359541043123 13224157143104039311564685)
            ·
              refine ⟨4959058928664014741836757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13224157143104039311564685 4959058928664014741836757)
              ·
                refine ⟨116227943640562845511799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4959058928664014741836757 116227943640562845511799)
                ·
                  rfl

theorem cell23_6111534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 7].length) (baseStart_6111534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111534 prefixEnd_6111534 := by exact prefixLift 6111534
  have htrace : WordTrace (prefixWord ++ tailWord_6111534) baseStart_6111534 baseEnd_6111534 := by
    simpa [prefixWord, tailWord_6111534, baseEnd_6111534] using wordTrace_append hprefix tailTrace_6111534
  have hstable : (prefixWord ++ tailWord_6111534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111534).length < 2 ^ (prefixWord ++ tailWord_6111534).sum := by decide
  have hdescent : baseEnd_6111534 < baseStart_6111534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111570 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_6111570 : Nat := 118140960795 + 6111570 * 2 ^ 59
def prefixEnd_6111570 : Nat := 4983230072969 + 3 ^ 40 * 6111570 * 2
def baseEnd_6111570 : Nat := 3138172963598758687968407

theorem tailTrace_6111570 : CollatzResearch.WordTrace tailWord_6111570 prefixEnd_6111570 3138172963598758687968407 := by
  unfold tailWord_6111570
  simp only [CollatzResearch.WordTrace]
  refine ⟨55726817617208284475523041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148604846979222091934728109 55726817617208284475523041)
  ·
    refine ⟨41795113212906213356642281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55726817617208284475523041 41795113212906213356642281)
    ·
      refine ⟨31346334909679660017481711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41795113212906213356642281 31346334909679660017481711)
      ·
        refine ⟨47019502364519490026222567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31346334909679660017481711 47019502364519490026222567)
        ·
          refine ⟨70529253546779235039333851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47019502364519490026222567 70529253546779235039333851)
          ·
            refine ⟨105793880320168852559000777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70529253546779235039333851 105793880320168852559000777)
            ·
              refine ⟨79345410240126639419250583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105793880320168852559000777 79345410240126639419250583)
              ·
                refine ⟨119018115360189959128875875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79345410240126639419250583 119018115360189959128875875)
                ·
                  refine ⟨178527173040284938693313813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119018115360189959128875875 178527173040284938693313813)
                  ·
                    refine ⟨8368461236263356501249085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 178527173040284938693313813 8368461236263356501249085)
                    ·
                      refine ⟨3138172963598758687968407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8368461236263356501249085 3138172963598758687968407)
                      ·
                        rfl

theorem cell23_6111570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_6111570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111570 prefixEnd_6111570 := by exact prefixLift 6111570
  have htrace : WordTrace (prefixWord ++ tailWord_6111570) baseStart_6111570 baseEnd_6111570 := by
    simpa [prefixWord, tailWord_6111570, baseEnd_6111570] using wordTrace_append hprefix tailTrace_6111570
  have hstable : (prefixWord ++ tailWord_6111570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111570).length < 2 ^ (prefixWord ++ tailWord_6111570).sum := by decide
  have hdescent : baseEnd_6111570 < baseStart_6111570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111624 : List Nat := [2, 1, 3, 3, 1, 1, 5, 2, 5]
def baseStart_6111624 : Nat := 118140960795 + 6111624 * 2 ^ 59
def prefixEnd_6111624 : Nat := 4983230072969 + 3 ^ 40 * 6111624 * 2
def baseEnd_6111624 : Nat := 348688965728233497410351

theorem tailTrace_6111624 : CollatzResearch.WordTrace tailWord_6111624 prefixEnd_6111624 348688965728233497410351 := by
  unfold tailWord_6111624
  simp only [CollatzResearch.WordTrace]
  refine ⟨111454620005318752562278963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148606160007091670083038617 111454620005318752562278963)
  ·
    refine ⟨167181930007978128843418445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111454620005318752562278963 167181930007978128843418445)
    ·
      refine ⟨62693223752991798316281917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167181930007978128843418445 62693223752991798316281917)
      ·
        refine ⟨23509958907371924368605719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62693223752991798316281917 23509958907371924368605719)
        ·
          refine ⟨35264938361057886552908579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23509958907371924368605719 35264938361057886552908579)
          ·
            refine ⟨52897407541586829829362869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35264938361057886552908579 52897407541586829829362869)
            ·
              refine ⟨4959131957023765296502769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52897407541586829829362869 4959131957023765296502769)
              ·
                refine ⟨3719348967767823972377077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4959131957023765296502769 3719348967767823972377077)
                ·
                  refine ⟨348688965728233497410351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3719348967767823972377077 348688965728233497410351)
                  ·
                    rfl

theorem cell23_6111624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 5].length) (baseStart_6111624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111624 prefixEnd_6111624 := by exact prefixLift 6111624
  have htrace : WordTrace (prefixWord ++ tailWord_6111624) baseStart_6111624 baseEnd_6111624 := by
    simpa [prefixWord, tailWord_6111624, baseEnd_6111624] using wordTrace_append hprefix tailTrace_6111624
  have hstable : (prefixWord ++ tailWord_6111624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111624).length < 2 ^ (prefixWord ++ tailWord_6111624).sum := by decide
  have hdescent : baseEnd_6111624 < baseStart_6111624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111741 : List Nat := [1, 4, 1, 1, 1, 3, 1, 6, 1, 1, 3]
def baseStart_6111741 : Nat := 118140960795 + 6111741 * 2 ^ 59
def prefixEnd_6111741 : Nat := 4983230072969 + 3 ^ 40 * 6111741 * 2
def baseEnd_6111741 : Nat := 3138260768790677518930121

theorem tailTrace_6111741 : CollatzResearch.WordTrace tailWord_6111741 prefixEnd_6111741 3138260768790677518930121 := by
  unfold tailWord_6111741
  simp only [CollatzResearch.WordTrace]
  refine ⟨222913507351213634106567077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148609004900809089404378051 222913507351213634106567077)
  ·
    refine ⟨41796282628352556394981327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222913507351213634106567077 41796282628352556394981327)
    ·
      refine ⟨62694423942528834592471991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41796282628352556394981327 62694423942528834592471991)
      ·
        refine ⟨94041635913793251888707987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62694423942528834592471991 94041635913793251888707987)
        ·
          refine ⟨141062453870689877833061981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94041635913793251888707987 141062453870689877833061981)
          ·
            refine ⟨52898420201508704187398243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141062453870689877833061981 52898420201508704187398243)
            ·
              refine ⟨79347630302263056281097365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52898420201508704187398243 79347630302263056281097365)
              ·
                refine ⟨3719420170418580763176439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79347630302263056281097365 3719420170418580763176439)
                ·
                  refine ⟨5579130255627871144764659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3719420170418580763176439 5579130255627871144764659)
                  ·
                    refine ⟨8368695383441806717146989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5579130255627871144764659 8368695383441806717146989)
                    ·
                      refine ⟨3138260768790677518930121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8368695383441806717146989 3138260768790677518930121)
                      ·
                        rfl

theorem cell23_6111741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_6111741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111741 prefixEnd_6111741 := by exact prefixLift 6111741
  have htrace : WordTrace (prefixWord ++ tailWord_6111741) baseStart_6111741 baseEnd_6111741 := by
    simpa [prefixWord, tailWord_6111741, baseEnd_6111741] using wordTrace_append hprefix tailTrace_6111741
  have hstable : (prefixWord ++ tailWord_6111741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111741).length < 2 ^ (prefixWord ++ tailWord_6111741).sum := by decide
  have hdescent : baseEnd_6111741 < baseStart_6111741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111777 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_6111777 : Nat := 118140960795 + 6111777 * 2 ^ 59
def prefixEnd_6111777 : Nat := 4983230072969 + 3 ^ 40 * 6111777 * 2
def baseEnd_6111777 : Nat := 3138279254094239378079955

theorem tailTrace_6111777 : CollatzResearch.WordTrace tailWord_6111777 prefixEnd_6111777 3138279254094239378079955 := by
  unfold tailWord_6111777
  simp only [CollatzResearch.WordTrace]
  refine ⟨222914820379083212254877585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148609880252722141503251723 222914820379083212254877585)
  ·
    refine ⟨167186115284312409191158189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222914820379083212254877585 167186115284312409191158189)
    ·
      refine ⟨62694793231617153446684321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167186115284312409191158189 62694793231617153446684321)
      ·
        refine ⟨47021094923712865085013241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62694793231617153446684321 47021094923712865085013241)
        ·
          refine ⟨35265821192784648813759931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47021094923712865085013241 35265821192784648813759931)
          ·
            refine ⟨52898731789176973220639897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35265821192784648813759931 52898731789176973220639897)
            ·
              refine ⟨39674048841882729915479923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52898731789176973220639897 39674048841882729915479923)
              ·
                refine ⟨59511073262824094873219885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39674048841882729915479923 59511073262824094873219885)
                ·
                  refine ⟨22316652473559035577457457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59511073262824094873219885 22316652473559035577457457)
                  ·
                    refine ⟨16737489355169276683093093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22316652473559035577457457 16737489355169276683093093)
                    ·
                      refine ⟨3138279254094239378079955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16737489355169276683093093 3138279254094239378079955)
                      ·
                        rfl

theorem cell23_6111777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_6111777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111777 prefixEnd_6111777 := by exact prefixLift 6111777
  have htrace : WordTrace (prefixWord ++ tailWord_6111777) baseStart_6111777 baseEnd_6111777 := by
    simpa [prefixWord, tailWord_6111777, baseEnd_6111777] using wordTrace_append hprefix tailTrace_6111777
  have hstable : (prefixWord ++ tailWord_6111777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111777).length < 2 ^ (prefixWord ++ tailWord_6111777).sum := by decide
  have hdescent : baseEnd_6111777 < baseStart_6111777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111784 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_6111784 : Nat := 118140960795 + 6111784 * 2 ^ 59
def prefixEnd_6111784 : Nat := 4983230072969 + 3 ^ 40 * 6111784 * 2
def baseEnd_6111784 : Nat := 3138282848458820850692423

theorem tailTrace_6111784 : CollatzResearch.WordTrace tailWord_6111784 prefixEnd_6111784 3138282848458820850692423 := by
  unfold tailWord_6111784
  simp only [CollatzResearch.WordTrace]
  refine ⟨111457537845028926225191203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148610050460038568300254937 111457537845028926225191203)
  ·
    refine ⟨167186306767543389337786805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111457537845028926225191203 167186306767543389337786805)
    ·
      refine ⟨15673716259457192750417513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167186306767543389337786805 15673716259457192750417513)
      ·
        refine ⟨11755287194592894562813135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15673716259457192750417513 11755287194592894562813135)
        ·
          refine ⟨17632930791889341844219703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11755287194592894562813135 17632930791889341844219703)
          ·
            refine ⟨26449396187834012766329555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17632930791889341844219703 26449396187834012766329555)
            ·
              refine ⟨39674094281751019149494333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26449396187834012766329555 39674094281751019149494333)
              ·
                refine ⟨14877785355656632181060375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39674094281751019149494333 14877785355656632181060375)
                ·
                  refine ⟨22316678033484948271590563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14877785355656632181060375 22316678033484948271590563)
                  ·
                    refine ⟨33475017050227422407385845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22316678033484948271590563 33475017050227422407385845)
                    ·
                      refine ⟨3138282848458820850692423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33475017050227422407385845 3138282848458820850692423)
                      ·
                        rfl

theorem cell23_6111784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_6111784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111784 prefixEnd_6111784 := by exact prefixLift 6111784
  have htrace : WordTrace (prefixWord ++ tailWord_6111784) baseStart_6111784 baseEnd_6111784 := by
    simpa [prefixWord, tailWord_6111784, baseEnd_6111784] using wordTrace_append hprefix tailTrace_6111784
  have hstable : (prefixWord ++ tailWord_6111784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111784).length < 2 ^ (prefixWord ++ tailWord_6111784).sum := by decide
  have hdescent : baseEnd_6111784 < baseStart_6111784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111812 : List Nat := [2, 3, 5, 1, 2, 1, 1, 2, 1, 5]
def baseStart_6111812 : Nat := 118140960795 + 6111812 * 2 ^ 59
def prefixEnd_6111812 : Nat := 4983230072969 + 3 ^ 40 * 6111812 * 2
def baseEnd_6111812 : Nat := 1046099075305715580380765

theorem tailTrace_6111812 : CollatzResearch.WordTrace tailWord_6111812 prefixEnd_6111812 1046099075305715580380765 := by
  unfold tailWord_6111812
  simp only [CollatzResearch.WordTrace]
  refine ⟨111458048466978206616200845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148610731289304275488267793 111458048466978206616200845)
  ·
    refine ⟨41796768175116827481075317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111458048466978206616200845 41796768175116827481075317)
    ·
      refine ⟨3918447016417202576350811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41796768175116827481075317 3918447016417202576350811)
      ·
        refine ⟨5877670524625803864526217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3918447016417202576350811 5877670524625803864526217)
        ·
          refine ⟨4408252893469352898394663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5877670524625803864526217 4408252893469352898394663)
          ·
            refine ⟨6612379340204029347591995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4408252893469352898394663 6612379340204029347591995)
            ·
              refine ⟨9918569010306044021387993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6612379340204029347591995 9918569010306044021387993)
              ·
                refine ⟨7438926757729533016040995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9918569010306044021387993 7438926757729533016040995)
                ·
                  refine ⟨11158390136594299524061493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7438926757729533016040995 11158390136594299524061493)
                  ·
                    refine ⟨1046099075305715580380765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11158390136594299524061493 1046099075305715580380765)
                    ·
                      rfl

theorem cell23_6111812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_6111812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111812 prefixEnd_6111812 := by exact prefixLift 6111812
  have htrace : WordTrace (prefixWord ++ tailWord_6111812) baseStart_6111812 baseEnd_6111812 := by
    simpa [prefixWord, tailWord_6111812, baseEnd_6111812] using wordTrace_append hprefix tailTrace_6111812
  have hstable : (prefixWord ++ tailWord_6111812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111812).length < 2 ^ (prefixWord ++ tailWord_6111812).sum := by decide
  have hdescent : baseEnd_6111812 < baseStart_6111812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111838 : List Nat := [4, 4, 1, 2, 2, 10]
def baseStart_6111838 : Nat := 118140960795 + 6111838 * 2 ^ 59
def prefixEnd_6111838 : Nat := 4983230072969 + 3 ^ 40 * 6111838 * 2
def baseEnd_6111838 : Nat := 12914858339152936787725

theorem tailTrace_6111838 : CollatzResearch.WordTrace tailWord_6111838 prefixEnd_6111838 12914858339152936787725 := by
  unfold tailWord_6111838
  simp only [CollatzResearch.WordTrace]
  refine ⟨27864630653982777459106021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148611363487908146448565445 27864630653982777459106021)
  ·
    refine ⟨5224618247621770773582379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27864630653982777459106021 5224618247621770773582379)
    ·
      refine ⟨7836927371432656160373569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5224618247621770773582379 7836927371432656160373569)
      ·
        refine ⟨5877695528574492120280177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7836927371432656160373569 5877695528574492120280177)
        ·
          refine ⟨4408271646430869090210133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5877695528574492120280177 4408271646430869090210133)
          ·
            refine ⟨12914858339152936787725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4408271646430869090210133 12914858339152936787725)
            ·
              rfl

theorem cell23_6111838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 10].length) (baseStart_6111838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111838 prefixEnd_6111838 := by exact prefixLift 6111838
  have htrace : WordTrace (prefixWord ++ tailWord_6111838) baseStart_6111838 baseEnd_6111838 := by
    simpa [prefixWord, tailWord_6111838, baseEnd_6111838] using wordTrace_append hprefix tailTrace_6111838
  have hstable : (prefixWord ++ tailWord_6111838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111838).length < 2 ^ (prefixWord ++ tailWord_6111838).sum := by decide
  have hdescent : baseEnd_6111838 < baseStart_6111838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111847 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 2, 6]
def baseStart_6111847 : Nat := 118140960795 + 6111847 * 2 ^ 59
def prefixEnd_6111847 : Nat := 4983230072969 + 3 ^ 40 * 6111847 * 2
def baseEnd_6111847 : Nat := 1046105065913351368068211

theorem tailTrace_6111847 : CollatzResearch.WordTrace tailWord_6111847 prefixEnd_6111847 1046105065913351368068211 := by
  unfold tailWord_6111847
  simp only [CollatzResearch.WordTrace]
  refine ⟨222917373488829614209925795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148611582325886409473283863 222917373488829614209925795)
  ·
    refine ⟨334376060233244421314888693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222917373488829614209925795 334376060233244421314888693)
    ·
      refine ⟨31347755646866664498270815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 334376060233244421314888693 31347755646866664498270815)
      ·
        refine ⟨47021633470299996747406223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31347755646866664498270815 47021633470299996747406223)
        ·
          refine ⟨70532450205449995121109335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47021633470299996747406223 70532450205449995121109335)
          ·
            refine ⟨105798675308174992681664003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70532450205449995121109335 105798675308174992681664003)
            ·
              refine ⟨158698012962262489022496005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105798675308174992681664003 158698012962262489022496005)
              ·
                refine ⟨29755877430424216691718001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158698012962262489022496005 29755877430424216691718001)
                ·
                  refine ⟨22316908072818162518788501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29755877430424216691718001 22316908072818162518788501)
                  ·
                    refine ⟨1046105065913351368068211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22316908072818162518788501 1046105065913351368068211)
                    ·
                      rfl

theorem cell23_6111847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_6111847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111847 prefixEnd_6111847 := by exact prefixLift 6111847
  have htrace : WordTrace (prefixWord ++ tailWord_6111847) baseStart_6111847 baseEnd_6111847 := by
    simpa [prefixWord, tailWord_6111847, baseEnd_6111847] using wordTrace_append hprefix tailTrace_6111847
  have hstable : (prefixWord ++ tailWord_6111847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111847).length < 2 ^ (prefixWord ++ tailWord_6111847).sum := by decide
  have hdescent : baseEnd_6111847 < baseStart_6111847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111854 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_6111854 : Nat := 118140960795 + 6111854 * 2 ^ 59
def prefixEnd_6111854 : Nat := 4983230072969 + 3 ^ 40 * 6111854 * 2
def baseEnd_6111854 : Nat := 3138318792104635576817101

theorem tailTrace_6111854 : CollatzResearch.WordTrace tailWord_6111854 prefixEnd_6111854 3138318792104635576817101 := by
  unfold tailWord_6111854
  simp only [CollatzResearch.WordTrace]
  refine ⟨27864703599975531800678827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148611752533202836270287077 27864703599975531800678827)
  ·
    refine ⟨41797055399963297701018241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27864703599975531800678827 41797055399963297701018241)
    ·
      refine ⟨31347791549972473275763681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41797055399963297701018241 31347791549972473275763681)
      ·
        refine ⟨23510843662479354956822761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31347791549972473275763681 23510843662479354956822761)
        ·
          refine ⟨17633132746859516217617071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23510843662479354956822761 17633132746859516217617071)
          ·
            refine ⟨26449699120289274326425607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17633132746859516217617071 26449699120289274326425607)
            ·
              refine ⟨39674548680433911489638411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26449699120289274326425607 39674548680433911489638411)
              ·
                refine ⟨59511823020650867234457617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39674548680433911489638411 59511823020650867234457617)
                ·
                  refine ⟨44633867265488150425843213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59511823020650867234457617 44633867265488150425843213)
                  ·
                    refine ⟨16737700224558056409691205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44633867265488150425843213 16737700224558056409691205)
                    ·
                      refine ⟨3138318792104635576817101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16737700224558056409691205 3138318792104635576817101)
                      ·
                        rfl

theorem cell23_6111854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_6111854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111854 prefixEnd_6111854 := by exact prefixLift 6111854
  have htrace : WordTrace (prefixWord ++ tailWord_6111854) baseStart_6111854 baseEnd_6111854 := by
    simpa [prefixWord, tailWord_6111854, baseEnd_6111854] using wordTrace_append hprefix tailTrace_6111854
  have hstable : (prefixWord ++ tailWord_6111854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111854).length < 2 ^ (prefixWord ++ tailWord_6111854).sum := by decide
  have hdescent : baseEnd_6111854 < baseStart_6111854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111877 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 9]
def baseStart_6111877 : Nat := 118140960795 + 6111877 * 2 ^ 59
def prefixEnd_6111877 : Nat := 4983230072969 + 3 ^ 40 * 6111877 * 2
def baseEnd_6111877 : Nat := 348703400239965442981055

theorem tailTrace_6111877 : CollatzResearch.WordTrace tailWord_6111877 prefixEnd_6111877 348703400239965442981055 := by
  unfold tailWord_6111877
  simp only [CollatzResearch.WordTrace]
  refine ⟨222918467678720929333517885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148612311785813952889011923 222918467678720929333517885)
  ·
    refine ⟨83594425379520348500069207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222918467678720929333517885 83594425379520348500069207)
    ·
      refine ⟨125391638069280522750103811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83594425379520348500069207 125391638069280522750103811)
      ·
        refine ⟨188087457103920784125155717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125391638069280522750103811 188087457103920784125155717)
        ·
          refine ⟨35266398206985147023466697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188087457103920784125155717 35266398206985147023466697)
          ·
            refine ⟨26449798655238860267600023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35266398206985147023466697 26449798655238860267600023)
            ·
              refine ⟨39674697982858290401400035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26449798655238860267600023 39674697982858290401400035)
              ·
                refine ⟨59512046974287435602100053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39674697982858290401400035 59512046974287435602100053)
                ·
                  refine ⟨348703400239965442981055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59512046974287435602100053 348703400239965442981055)
                  ·
                    rfl

theorem cell23_6111877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 9].length) (baseStart_6111877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111877 prefixEnd_6111877 := by exact prefixLift 6111877
  have htrace : WordTrace (prefixWord ++ tailWord_6111877) baseStart_6111877 baseEnd_6111877 := by
    simpa [prefixWord, tailWord_6111877, baseEnd_6111877] using wordTrace_append hprefix tailTrace_6111877
  have hstable : (prefixWord ++ tailWord_6111877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111877).length < 2 ^ (prefixWord ++ tailWord_6111877).sum := by decide
  have hdescent : baseEnd_6111877 < baseStart_6111877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111892 : List Nat := [2, 4, 2, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_6111892 : Nat := 118140960795 + 6111892 * 2 ^ 59
def prefixEnd_6111892 : Nat := 4983230072969 + 3 ^ 40 * 6111892 * 2
def baseEnd_6111892 : Nat := 3138338304369506428141927

theorem tailTrace_6111892 : CollatzResearch.WordTrace tailWord_6111892 prefixEnd_6111892 3138338304369506428141927 := by
  unfold tailWord_6111892
  simp only [CollatzResearch.WordTrace]
  refine ⟨111459507386833293447656965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148612676515777724596875953 111459507386833293447656965)
  ·
    refine ⟨20898657635031242521435681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111459507386833293447656965 20898657635031242521435681)
    ·
      refine ⟨15673993226273431891076761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20898657635031242521435681 15673993226273431891076761)
      ·
        refine ⟨11755494919705073918307571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15673993226273431891076761 11755494919705073918307571)
        ·
          refine ⟨17633242379557610877461357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11755494919705073918307571 17633242379557610877461357)
          ·
            refine ⟨6612465892334104079048009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17633242379557610877461357 6612465892334104079048009)
            ·
              refine ⟨4959349419250578059286007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6612465892334104079048009 4959349419250578059286007)
              ·
                refine ⟨7439024128875867088929011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4959349419250578059286007 7439024128875867088929011)
                ·
                  refine ⟨11158536193313800633393517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7439024128875867088929011 11158536193313800633393517)
                  ·
                    refine ⟨4184451072492675237522569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11158536193313800633393517 4184451072492675237522569)
                    ·
                      refine ⟨3138338304369506428141927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4184451072492675237522569 3138338304369506428141927)
                      ·
                        rfl

theorem cell23_6111892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_6111892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111892 prefixEnd_6111892 := by exact prefixLift 6111892
  have htrace : WordTrace (prefixWord ++ tailWord_6111892) baseStart_6111892 baseEnd_6111892 := by
    simpa [prefixWord, tailWord_6111892, baseEnd_6111892] using wordTrace_append hprefix tailTrace_6111892
  have hstable : (prefixWord ++ tailWord_6111892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111892).length < 2 ^ (prefixWord ++ tailWord_6111892).sum := by decide
  have hdescent : baseEnd_6111892 < baseStart_6111892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111944 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_6111944 : Nat := 118140960795 + 6111944 * 2 ^ 59
def prefixEnd_6111944 : Nat := 4983230072969 + 3 ^ 40 * 6111944 * 2
def baseEnd_6111944 : Nat := 3138365005363540224691687

theorem tailTrace_6111944 : CollatzResearch.WordTrace tailWord_6111944 prefixEnd_6111944 3138365005363540224691687 := by
  unfold tailWord_6111944
  simp only [CollatzResearch.WordTrace]
  refine ⟨111460455684739099888103443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148613940912985466517471257 111460455684739099888103443)
  ·
    refine ⟨167190683527108649832155165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111460455684739099888103443 167190683527108649832155165)
    ·
      refine ⟨62696506322665743687058187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167190683527108649832155165 62696506322665743687058187)
      ·
        refine ⟨94044759483998615530587281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62696506322665743687058187 94044759483998615530587281)
        ·
          refine ⟨70533569612998961647940461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94044759483998615530587281 70533569612998961647940461)
          ·
            refine ⟨26450088604874610617977673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70533569612998961647940461 26450088604874610617977673)
            ·
              refine ⟨19837566453655957963483255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26450088604874610617977673 19837566453655957963483255)
              ·
                refine ⟨29756349680483936945224883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19837566453655957963483255 29756349680483936945224883)
                ·
                  refine ⟨44634524520725905417837325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29756349680483936945224883 44634524520725905417837325)
                  ·
                    refine ⟨16737946695272214531688997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44634524520725905417837325 16737946695272214531688997)
                    ·
                      refine ⟨3138365005363540224691687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16737946695272214531688997 3138365005363540224691687)
                      ·
                        rfl

theorem cell23_6111944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_6111944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111944 prefixEnd_6111944 := by exact prefixLift 6111944
  have htrace : WordTrace (prefixWord ++ tailWord_6111944) baseStart_6111944 baseEnd_6111944 := by
    simpa [prefixWord, tailWord_6111944, baseEnd_6111944] using wordTrace_append hprefix tailTrace_6111944
  have hstable : (prefixWord ++ tailWord_6111944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111944).length < 2 ^ (prefixWord ++ tailWord_6111944).sum := by decide
  have hdescent : baseEnd_6111944 < baseStart_6111944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111947 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 5]
def baseStart_6111947 : Nat := 118140960795 + 6111947 * 2 ^ 59
def prefixEnd_6111947 : Nat := 4983230072969 + 3 ^ 40 * 6111947 * 2
def baseEnd_6111947 : Nat := 3138366545805503712954173

theorem tailTrace_6111947 : CollatzResearch.WordTrace tailWord_6111947 prefixEnd_6111947 3138366545805503712954173 := by
  unfold tailWord_6111947
  simp only [CollatzResearch.WordTrace]
  refine ⟨222921020788467331288566095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148614013858978220859044063 222921020788467331288566095)
  ·
    refine ⟨334381531182700996932849143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222921020788467331288566095 334381531182700996932849143)
    ·
      refine ⟨501572296774051495399273715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334381531182700996932849143 501572296774051495399273715)
      ·
        refine ⟨752358445161077243098910573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501572296774051495399273715 752358445161077243098910573)
        ·
          refine ⟨282134416935403966162091465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 752358445161077243098910573 282134416935403966162091465)
          ·
            refine ⟨211600812701552974621568599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282134416935403966162091465 211600812701552974621568599)
            ·
              refine ⟨317401219052329461932352899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211600812701552974621568599 317401219052329461932352899)
              ·
                refine ⟨476101828578494192898529349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317401219052329461932352899 476101828578494192898529349)
                ·
                  refine ⟨89269092858467661168474253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 476101828578494192898529349 89269092858467661168474253)
                  ·
                    refine ⟨33475909821925372938177845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89269092858467661168474253 33475909821925372938177845)
                    ·
                      refine ⟨3138366545805503712954173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33475909821925372938177845 3138366545805503712954173)
                      ·
                        rfl

theorem cell23_6111947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 5].length) (baseStart_6111947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111947 prefixEnd_6111947 := by exact prefixLift 6111947
  have htrace : WordTrace (prefixWord ++ tailWord_6111947) baseStart_6111947 baseEnd_6111947 := by
    simpa [prefixWord, tailWord_6111947, baseEnd_6111947] using wordTrace_append hprefix tailTrace_6111947
  have hstable : (prefixWord ++ tailWord_6111947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111947).length < 2 ^ (prefixWord ++ tailWord_6111947).sum := by decide
  have hdescent : baseEnd_6111947 < baseStart_6111947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111981 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_6111981 : Nat := 118140960795 + 6111981 * 2 ^ 59
def prefixEnd_6111981 : Nat := 4983230072969 + 3 ^ 40 * 6111981 * 2
def baseEnd_6111981 : Nat := 3138384004147756579929017

theorem tailTrace_6111981 : CollatzResearch.WordTrace tailWord_6111981 prefixEnd_6111981 3138384004147756579929017 := by
  unfold tailWord_6111981
  simp only [CollatzResearch.WordTrace]
  refine ⟨222922260870344155095303797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148614840580229436730202531 222922260870344155095303797)
  ·
    refine ⟨20898961956594764540184731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222922260870344155095303797 20898961956594764540184731)
    ·
      refine ⟨31348442934892146810277097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20898961956594764540184731 31348442934892146810277097)
      ·
        refine ⟨23511332201169110107707823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31348442934892146810277097 23511332201169110107707823)
        ·
          refine ⟨35266998301753665161561735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23511332201169110107707823 35266998301753665161561735)
          ·
            refine ⟨52900497452630497742342603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35266998301753665161561735 52900497452630497742342603)
            ·
              refine ⟨79350746178945746613513905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52900497452630497742342603 79350746178945746613513905)
              ·
                refine ⟨59513059634209309960135429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79350746178945746613513905 59513059634209309960135429)
                ·
                  refine ⟨11158698681414245617525393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59513059634209309960135429 11158698681414245617525393)
                  ·
                    refine ⟨8369024011060684213144045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11158698681414245617525393 8369024011060684213144045)
                    ·
                      refine ⟨3138384004147756579929017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8369024011060684213144045 3138384004147756579929017)
                      ·
                        rfl

theorem cell23_6111981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_6111981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111981 prefixEnd_6111981 := by exact prefixLift 6111981
  have htrace : WordTrace (prefixWord ++ tailWord_6111981) baseStart_6111981 baseEnd_6111981 := by
    simpa [prefixWord, tailWord_6111981, baseEnd_6111981] using wordTrace_append hprefix tailTrace_6111981
  have hstable : (prefixWord ++ tailWord_6111981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111981).length < 2 ^ (prefixWord ++ tailWord_6111981).sum := by decide
  have hdescent : baseEnd_6111981 < baseStart_6111981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111984 : List Nat := [2, 1, 1, 1, 3, 1, 5, 3, 6]
def baseStart_6111984 : Nat := 118140960795 + 6111984 * 2 ^ 59
def prefixEnd_6111984 : Nat := 4983230072969 + 3 ^ 40 * 6111984 * 2
def baseEnd_6111984 : Nat := 348709504954413340910167

theorem tailTrace_6111984 : CollatzResearch.WordTrace tailWord_6111984 prefixEnd_6111984 348709504954413340910167 := by
  unfold tailWord_6111984
  simp only [CollatzResearch.WordTrace]
  refine ⟨111461185144666643303831503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148614913526222191071775337 111461185144666643303831503)
  ·
    refine ⟨167191777716999964955747255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111461185144666643303831503 167191777716999964955747255)
    ·
      refine ⟨250787666575499947433620883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167191777716999964955747255 250787666575499947433620883)
      ·
        refine ⟨376181499863249921150431325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250787666575499947433620883 376181499863249921150431325)
        ·
          refine ⟨141068062448718720431411747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376181499863249921150431325 141068062448718720431411747)
          ·
            refine ⟨211602093673078080647117621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141068062448718720431411747 211602093673078080647117621)
            ·
              refine ⟨19837696281851070060667277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211602093673078080647117621 19837696281851070060667277)
              ·
                refine ⟨7439136105694151272750229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19837696281851070060667277 7439136105694151272750229)
                ·
                  refine ⟨348709504954413340910167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7439136105694151272750229 348709504954413340910167)
                  ·
                    rfl

theorem cell23_6111984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 6].length) (baseStart_6111984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111984 prefixEnd_6111984 := by exact prefixLift 6111984
  have htrace : WordTrace (prefixWord ++ tailWord_6111984) baseStart_6111984 baseEnd_6111984 := by
    simpa [prefixWord, tailWord_6111984, baseEnd_6111984] using wordTrace_append hprefix tailTrace_6111984
  have hstable : (prefixWord ++ tailWord_6111984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111984).length < 2 ^ (prefixWord ++ tailWord_6111984).sum := by decide
  have hdescent : baseEnd_6111984 < baseStart_6111984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111994 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3]
def baseStart_6111994 : Nat := 118140960795 + 6111994 * 2 ^ 59
def prefixEnd_6111994 : Nat := 4983230072969 + 3 ^ 40 * 6111994 * 2
def baseEnd_6111994 : Nat := 3138390679396265029066457

theorem tailTrace_6111994 : CollatzResearch.WordTrace tailWord_6111994 prefixEnd_6111994 3138390679396265029066457 := by
  unfold tailWord_6111994
  simp only [CollatzResearch.WordTrace]
  refine ⟨55730683754824264578881759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148615156679531372210351357 55730683754824264578881759)
  ·
    refine ⟨83596025632236396868322639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55730683754824264578881759 83596025632236396868322639)
    ·
      refine ⟨125394038448354595302483959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83596025632236396868322639 125394038448354595302483959)
      ·
        refine ⟨188091057672531892953725939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125394038448354595302483959 188091057672531892953725939)
        ·
          refine ⟨282136586508797839430588909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188091057672531892953725939 282136586508797839430588909)
          ·
            refine ⟨105801219940799189786470841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282136586508797839430588909 105801219940799189786470841)
            ·
              refine ⟨79350914955599392339853131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105801219940799189786470841 79350914955599392339853131)
              ·
                refine ⟨119026372433399088509779697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79350914955599392339853131 119026372433399088509779697)
                ·
                  refine ⟨89269779325049316382334773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119026372433399088509779697 89269779325049316382334773)
                  ·
                    refine ⟨8369041811723373410843885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89269779325049316382334773 8369041811723373410843885)
                    ·
                      refine ⟨3138390679396265029066457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8369041811723373410843885 3138390679396265029066457)
                      ·
                        rfl

theorem cell23_6111994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_6111994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111994 prefixEnd_6111994 := by exact prefixLift 6111994
  have htrace : WordTrace (prefixWord ++ tailWord_6111994) baseStart_6111994 baseEnd_6111994 := by
    simpa [prefixWord, tailWord_6111994, baseEnd_6111994] using wordTrace_append hprefix tailTrace_6111994
  have hstable : (prefixWord ++ tailWord_6111994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111994).length < 2 ^ (prefixWord ++ tailWord_6111994).sum := by decide
  have hdescent : baseEnd_6111994 < baseStart_6111994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6111998 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_6111998 : Nat := 118140960795 + 6111998 * 2 ^ 59
def prefixEnd_6111998 : Nat := 4983230072969 + 3 ^ 40 * 6111998 * 2
def baseEnd_6111998 : Nat := 3138392733318883013416439

theorem tailTrace_6111998 : CollatzResearch.WordTrace tailWord_6111998 prefixEnd_6111998 3138392733318883013416439 := by
  unfold tailWord_6111998
  simp only [CollatzResearch.WordTrace]
  refine ⟨27865360113910320874834081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148615253940855044665781765 27865360113910320874834081)
  ·
    refine ⟨20899020085432740656125561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27865360113910320874834081 20899020085432740656125561)
    ·
      refine ⟨15674265064074555492094171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20899020085432740656125561 15674265064074555492094171)
      ·
        refine ⟨23511397596111833238141257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15674265064074555492094171 23511397596111833238141257)
        ·
          refine ⟨17633548197083874928605943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23511397596111833238141257 17633548197083874928605943)
          ·
            refine ⟨26450322295625812392908915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17633548197083874928605943 26450322295625812392908915)
            ·
              refine ⟨39675483443438718589363373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26450322295625812392908915 39675483443438718589363373)
              ·
                refine ⟨14878306291289519471011265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39675483443438718589363373 14878306291289519471011265)
                ·
                  refine ⟨11158729718467139603258449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14878306291289519471011265 11158729718467139603258449)
                  ·
                    refine ⟨8369047288850354702443837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11158729718467139603258449 8369047288850354702443837)
                    ·
                      refine ⟨3138392733318883013416439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8369047288850354702443837 3138392733318883013416439)
                      ·
                        rfl

theorem cell23_6111998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_6111998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6111998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6111998 prefixEnd_6111998 := by exact prefixLift 6111998
  have htrace : WordTrace (prefixWord ++ tailWord_6111998) baseStart_6111998 baseEnd_6111998 := by
    simpa [prefixWord, tailWord_6111998, baseEnd_6111998] using wordTrace_append hprefix tailTrace_6111998
  have hstable : (prefixWord ++ tailWord_6111998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6111998).length < 2 ^ (prefixWord ++ tailWord_6111998).sum := by decide
  have hdescent : baseEnd_6111998 < baseStart_6111998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6111998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112051 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 4]
def baseStart_6112051 : Nat := 118140960795 + 6112051 * 2 ^ 59
def prefixEnd_6112051 : Nat := 4983230072969 + 3 ^ 40 * 6112051 * 2
def baseEnd_6112051 : Nat := 3138419947793571306053695

theorem tailTrace_6112051 : CollatzResearch.WordTrace tailWord_6112051 prefixEnd_6112051 3138419947793571306053695 := by
  unfold tailWord_6112051
  simp only [CollatzResearch.WordTrace]
  refine ⟨222924813980090557050352007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148616542653393704700234671 222924813980090557050352007)
  ·
    refine ⟨334387220970135835575528011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222924813980090557050352007 334387220970135835575528011)
    ·
      refine ⟨501580831455203753363292017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334387220970135835575528011 501580831455203753363292017)
      ·
        refine ⟨376185623591402815022469013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501580831455203753363292017 376185623591402815022469013)
        ·
          refine ⟨17633701105847006954178235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 376185623591402815022469013 17633701105847006954178235)
          ·
            refine ⟨26450551658770510431267353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17633701105847006954178235 26450551658770510431267353)
            ·
              refine ⟨19837913744077882823450515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26450551658770510431267353 19837913744077882823450515)
              ·
                refine ⟨29756870616116824235175773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19837913744077882823450515 29756870616116824235175773)
                ·
                  refine ⟨11158826481043809088190915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29756870616116824235175773 11158826481043809088190915)
                  ·
                    refine ⟨16738239721565713632286373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11158826481043809088190915 16738239721565713632286373)
                    ·
                      refine ⟨3138419947793571306053695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16738239721565713632286373 3138419947793571306053695)
                      ·
                        rfl

theorem cell23_6112051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 4].length) (baseStart_6112051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112051 prefixEnd_6112051 := by exact prefixLift 6112051
  have htrace : WordTrace (prefixWord ++ tailWord_6112051) baseStart_6112051 baseEnd_6112051 := by
    simpa [prefixWord, tailWord_6112051, baseEnd_6112051] using wordTrace_append hprefix tailTrace_6112051
  have hstable : (prefixWord ++ tailWord_6112051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112051).length < 2 ^ (prefixWord ++ tailWord_6112051).sum := by decide
  have hdescent : baseEnd_6112051 < baseStart_6112051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112065 : List Nat := [1, 2, 5, 3, 1, 1, 1, 3, 1, 5]
def baseStart_6112065 : Nat := 118140960795 + 6112065 * 2 ^ 59
def prefixEnd_6112065 : Nat := 4983230072969 + 3 ^ 40 * 6112065 * 2
def baseEnd_6112065 : Nat := 1046142378840911417092877

theorem tailTrace_6112065 : CollatzResearch.WordTrace tailWord_6112065 prefixEnd_6112065 1046142378840911417092877 := by
  unfold tailWord_6112065
  simp only [CollatzResearch.WordTrace]
  refine ⟨222925324602039837441361649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148616883068026558294241099 222925324602039837441361649)
  ·
    refine ⟨167193993451529878081021237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222925324602039837441361649 167193993451529878081021237)
    ·
      refine ⟨15674436886080926070095741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167193993451529878081021237 15674436886080926070095741)
      ·
        refine ⟨5877913832280347276285903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15674436886080926070095741 5877913832280347276285903)
        ·
          refine ⟨8816870748420520914428855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5877913832280347276285903 8816870748420520914428855)
          ·
            refine ⟨13225306122630781371643283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8816870748420520914428855 13225306122630781371643283)
            ·
              refine ⟨19837959183946172057464925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13225306122630781371643283 19837959183946172057464925)
              ·
                refine ⟨7439234693979814521549347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19837959183946172057464925 7439234693979814521549347)
                ·
                  refine ⟨11158852040969721782324021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7439234693979814521549347 11158852040969721782324021)
                  ·
                    refine ⟨1046142378840911417092877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11158852040969721782324021 1046142378840911417092877)
                    ·
                      rfl

theorem cell23_6112065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_6112065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112065 prefixEnd_6112065 := by exact prefixLift 6112065
  have htrace : WordTrace (prefixWord ++ tailWord_6112065) baseStart_6112065 baseEnd_6112065 := by
    simpa [prefixWord, tailWord_6112065, baseEnd_6112065] using wordTrace_append hprefix tailTrace_6112065
  have hstable : (prefixWord ++ tailWord_6112065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112065).length < 2 ^ (prefixWord ++ tailWord_6112065).sum := by decide
  have hdescent : baseEnd_6112065 < baseStart_6112065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112085 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 3, 2, 2]
def baseStart_6112085 : Nat := 118140960795 + 6112085 * 2 ^ 59
def prefixEnd_6112085 : Nat := 4983230072969 + 3 ^ 40 * 6112085 * 2
def baseEnd_6112085 : Nat := 3138437406135824173028539

theorem tailTrace_6112085 : CollatzResearch.WordTrace tailWord_6112085 prefixEnd_6112085 3138437406135824173028539 := by
  unfold tailWord_6112085
  simp only [CollatzResearch.WordTrace]
  refine ⟨222926054061967380857089709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148617369374644920571393139 222926054061967380857089709)
  ·
    refine ⟨83597270273237767821408641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222926054061967380857089709 83597270273237767821408641)
    ·
      refine ⟨62697952704928325866056481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83597270273237767821408641 62697952704928325866056481)
      ·
        refine ⟨47023464528696244399542361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62697952704928325866056481 47023464528696244399542361)
        ·
          refine ⟨35267598396522183299656771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47023464528696244399542361 35267598396522183299656771)
          ·
            refine ⟨52901397594783274949485157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35267598396522183299656771 52901397594783274949485157)
            ·
              refine ⟨9919012049021864053028467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52901397594783274949485157 9919012049021864053028467)
              ·
                refine ⟨14878518073532796079542701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9919012049021864053028467 14878518073532796079542701)
                ·
                  refine ⟨5579444277574798529828513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14878518073532796079542701 5579444277574798529828513)
                  ·
                    refine ⟨4184583208181098897371385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5579444277574798529828513 4184583208181098897371385)
                    ·
                      refine ⟨3138437406135824173028539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4184583208181098897371385 3138437406135824173028539)
                      ·
                        rfl

theorem cell23_6112085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_6112085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112085 prefixEnd_6112085 := by exact prefixLift 6112085
  have htrace : WordTrace (prefixWord ++ tailWord_6112085) baseStart_6112085 baseEnd_6112085 := by
    simpa [prefixWord, tailWord_6112085, baseEnd_6112085] using wordTrace_append hprefix tailTrace_6112085
  have hstable : (prefixWord ++ tailWord_6112085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112085).length < 2 ^ (prefixWord ++ tailWord_6112085).sum := by decide
  have hdescent : baseEnd_6112085 < baseStart_6112085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112098 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_6112098 : Nat := 118140960795 + 6112098 * 2 ^ 59
def prefixEnd_6112098 : Nat := 4983230072969 + 3 ^ 40 * 6112098 * 2
def baseEnd_6112098 : Nat := 3138444081384332622165979

theorem tailTrace_6112098 : CollatzResearch.WordTrace tailWord_6112098 prefixEnd_6112098 3138444081384332622165979 := by
  unfold tailWord_6112098
  simp only [CollatzResearch.WordTrace]
  refine ⟨55731632052730071019328237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148617685473946856051541965 55731632052730071019328237)
  ·
    refine ⟨20899362019773776632248089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55731632052730071019328237 20899362019773776632248089)
    ·
      refine ⟨15674521514830332474186067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20899362019773776632248089 15674521514830332474186067)
      ·
        refine ⟨23511782272245498711279101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15674521514830332474186067 23511782272245498711279101)
        ·
          refine ⟨8816918352092062016729663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23511782272245498711279101 8816918352092062016729663)
          ·
            refine ⟨13225377528138093025094495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8816918352092062016729663 13225377528138093025094495)
            ·
              refine ⟨19838066292207139537641743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13225377528138093025094495 19838066292207139537641743)
              ·
                refine ⟨29757099438310709306462615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19838066292207139537641743 29757099438310709306462615)
                ·
                  refine ⟨44635649157466063959693923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29757099438310709306462615 44635649157466063959693923)
                  ·
                    refine ⟨66953473736199095939540885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44635649157466063959693923 66953473736199095939540885)
                    ·
                      refine ⟨3138444081384332622165979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66953473736199095939540885 3138444081384332622165979)
                      ·
                        rfl

theorem cell23_6112098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_6112098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112098 prefixEnd_6112098 := by exact prefixLift 6112098
  have htrace : WordTrace (prefixWord ++ tailWord_6112098) baseStart_6112098 baseEnd_6112098 := by
    simpa [prefixWord, tailWord_6112098, baseEnd_6112098] using wordTrace_append hprefix tailTrace_6112098
  have hstable : (prefixWord ++ tailWord_6112098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112098).length < 2 ^ (prefixWord ++ tailWord_6112098).sum := by decide
  have hdescent : baseEnd_6112098 < baseStart_6112098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112111 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 2, 7, 2]
def baseStart_6112111 : Nat := 118140960795 + 6112111 * 2 ^ 59
def prefixEnd_6112111 : Nat := 4983230072969 + 3 ^ 40 * 6112111 * 2
def baseEnd_6112111 : Nat := 3138450756632841071303419

theorem tailTrace_6112111 : CollatzResearch.WordTrace tailWord_6112111 prefixEnd_6112111 3138450756632841071303419 := by
  unfold tailWord_6112111
  simp only [CollatzResearch.WordTrace]
  refine ⟨222927002359873187297536187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148618001573248791531690791 222927002359873187297536187)
  ·
    refine ⟨334390503539809780946304281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222927002359873187297536187 334390503539809780946304281)
    ·
      refine ⟨250792877654857335709728211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334390503539809780946304281 250792877654857335709728211)
      ·
        refine ⟨376189316482286003564592317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250792877654857335709728211 376189316482286003564592317)
        ·
          refine ⟨141070993680857251336722119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376189316482286003564592317 141070993680857251336722119)
          ·
            refine ⟨211606490521285877005083179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141070993680857251336722119 211606490521285877005083179)
            ·
              refine ⟨317409735781928815507624769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211606490521285877005083179 317409735781928815507624769)
              ·
                refine ⟨238057301836446611630718577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317409735781928815507624769 238057301836446611630718577)
                ·
                  refine ⟨178542976377334958723038933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238057301836446611630718577 178542976377334958723038933)
                  ·
                    refine ⟨4184601008843788095071225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 178542976377334958723038933 4184601008843788095071225)
                    ·
                      refine ⟨3138450756632841071303419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4184601008843788095071225 3138450756632841071303419)
                      ·
                        rfl

theorem cell23_6112111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 7, 2].length) (baseStart_6112111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112111 prefixEnd_6112111 := by exact prefixLift 6112111
  have htrace : WordTrace (prefixWord ++ tailWord_6112111) baseStart_6112111 baseEnd_6112111 := by
    simpa [prefixWord, tailWord_6112111, baseEnd_6112111] using wordTrace_append hprefix tailTrace_6112111
  have hstable : (prefixWord ++ tailWord_6112111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112111).length < 2 ^ (prefixWord ++ tailWord_6112111).sum := by decide
  have hdescent : baseEnd_6112111 < baseStart_6112111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112124 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_6112124 : Nat := 118140960795 + 6112124 * 2 ^ 59
def prefixEnd_6112124 : Nat := 4983230072969 + 3 ^ 40 * 6112124 * 2
def baseEnd_6112124 : Nat := 3138457431881349520440859

theorem tailTrace_6112124 : CollatzResearch.WordTrace tailWord_6112124 prefixEnd_6112124 3138457431881349520440859 := by
  unfold tailWord_6112124
  simp only [CollatzResearch.WordTrace]
  refine ⟨111463738254413045258879713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148618317672550727011839617 111463738254413045258879713)
  ·
    refine ⟨83597803690809783944159785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111463738254413045258879713 83597803690809783944159785)
    ·
      refine ⟨62698352768107337958119839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83597803690809783944159785 62698352768107337958119839)
      ·
        refine ⟨94047529152161006937179759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62698352768107337958119839 94047529152161006937179759)
        ·
          refine ⟨141071293728241510405769639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94047529152161006937179759 141071293728241510405769639)
          ·
            refine ⟨211606940592362265608654459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141071293728241510405769639 211606940592362265608654459)
            ·
              refine ⟨317410410888543398412981689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211606940592362265608654459 317410410888543398412981689)
              ·
                refine ⟨238057808166407548809736267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317410410888543398412981689 238057808166407548809736267)
                ·
                  refine ⟨357086712249611323214604401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238057808166407548809736267 357086712249611323214604401)
                  ·
                    refine ⟨267815034187208492410953301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 357086712249611323214604401 267815034187208492410953301)
                    ·
                      refine ⟨3138457431881349520440859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 267815034187208492410953301 3138457431881349520440859)
                      ·
                        rfl

theorem cell23_6112124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_6112124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112124 prefixEnd_6112124 := by exact prefixLift 6112124
  have htrace : WordTrace (prefixWord ++ tailWord_6112124) baseStart_6112124 baseEnd_6112124 := by
    simpa [prefixWord, tailWord_6112124, baseEnd_6112124] using wordTrace_append hprefix tailTrace_6112124
  have hstable : (prefixWord ++ tailWord_6112124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112124).length < 2 ^ (prefixWord ++ tailWord_6112124).sum := by decide
  have hdescent : baseEnd_6112124 < baseStart_6112124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112162 : List Nat := [3, 3, 1, 2, 2, 1, 3, 2, 1, 3, 2]
def baseStart_6112162 : Nat := 118140960795 + 6112162 * 2 ^ 59
def prefixEnd_6112162 : Nat := 4983230072969 + 3 ^ 40 * 6112162 * 2
def baseEnd_6112162 : Nat := 3138476944146220371765685

theorem tailTrace_6112162 : CollatzResearch.WordTrace tailWord_6112162 prefixEnd_6112162 3138476944146220371765685 := by
  unfold tailWord_6112162
  simp only [CollatzResearch.WordTrace]
  refine ⟨55732215620672105751910685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148619241655125615338428493 55732215620672105751910685)
  ·
    refine ⟨20899580857752039656966507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55732215620672105751910685 20899580857752039656966507)
    ·
      refine ⟨31349371286628059485449761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20899580857752039656966507 31349371286628059485449761)
      ·
        refine ⟨23512028464971044614087321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31349371286628059485449761 23512028464971044614087321)
        ·
          refine ⟨17634021348728283460565491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23512028464971044614087321 17634021348728283460565491)
          ·
            refine ⟨26451032023092425190848237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17634021348728283460565491 26451032023092425190848237)
            ·
              refine ⟨9919137008659659446568089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26451032023092425190848237 9919137008659659446568089)
              ·
                refine ⟨7439352756494744584926067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9919137008659659446568089 7439352756494744584926067)
                ·
                  refine ⟨11159029134742116877389101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7439352756494744584926067 11159029134742116877389101)
                  ·
                    refine ⟨4184635925528293829020913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11159029134742116877389101 4184635925528293829020913)
                    ·
                      refine ⟨3138476944146220371765685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4184635925528293829020913 3138476944146220371765685)
                      ·
                        rfl

theorem cell23_6112162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_6112162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112162 prefixEnd_6112162 := by exact prefixLift 6112162
  have htrace : WordTrace (prefixWord ++ tailWord_6112162) baseStart_6112162 baseEnd_6112162 := by
    simpa [prefixWord, tailWord_6112162, baseEnd_6112162] using wordTrace_append hprefix tailTrace_6112162
  have hstable : (prefixWord ++ tailWord_6112162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112162).length < 2 ^ (prefixWord ++ tailWord_6112162).sum := by decide
  have hdescent : baseEnd_6112162 < baseStart_6112162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112192 : List Nat := [2, 1, 1, 2, 3, 4, 2, 2, 2, 2, 2]
def baseStart_6112192 : Nat := 118140960795 + 6112192 * 2 ^ 59
def prefixEnd_6112192 : Nat := 4983230072969 + 3 ^ 40 * 6112192 * 2
def baseEnd_6112192 : Nat := 3138492348565855254390547

theorem tailTrace_6112192 : CollatzResearch.WordTrace tailWord_6112192 prefixEnd_6112192 3138492348565855254390547 := by
  unfold tailWord_6112192
  simp only [CollatzResearch.WordTrace]
  refine ⟨111464978336289869065617415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148619971115053158754156553 111464978336289869065617415)
  ·
    refine ⟨167197467504434803598426123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111464978336289869065617415 167197467504434803598426123)
    ·
      refine ⟨250796201256652205397639185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167197467504434803598426123 250796201256652205397639185)
      ·
        refine ⟨188097150942489154048229389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250796201256652205397639185 188097150942489154048229389)
        ·
          refine ⟨70536431603433432768086021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188097150942489154048229389 70536431603433432768086021)
          ·
            refine ⟨13225580925643768644016129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70536431603433432768086021 13225580925643768644016129)
            ·
              refine ⟨9919185694232826483012097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13225580925643768644016129 9919185694232826483012097)
              ·
                refine ⟨7439389270674619862259073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9919185694232826483012097 7439389270674619862259073)
                ·
                  refine ⟨5579541953005964896694305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7439389270674619862259073 5579541953005964896694305)
                  ·
                    refine ⟨4184656464754473672520729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5579541953005964896694305 4184656464754473672520729)
                    ·
                      refine ⟨3138492348565855254390547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4184656464754473672520729 3138492348565855254390547)
                      ·
                        rfl

theorem cell23_6112192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 2, 2, 2].length) (baseStart_6112192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112192 prefixEnd_6112192 := by exact prefixLift 6112192
  have htrace : WordTrace (prefixWord ++ tailWord_6112192) baseStart_6112192 baseEnd_6112192 := by
    simpa [prefixWord, tailWord_6112192, baseEnd_6112192] using wordTrace_append hprefix tailTrace_6112192
  have hstable : (prefixWord ++ tailWord_6112192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112192).length < 2 ^ (prefixWord ++ tailWord_6112192).sum := by decide
  have hdescent : baseEnd_6112192 < baseStart_6112192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112261 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 2, 1, 6]
def baseStart_6112261 : Nat := 118140960795 + 6112261 * 2 ^ 59
def prefixEnd_6112261 : Nat := 4983230072969 + 3 ^ 40 * 6112261 * 2
def baseEnd_6112261 : Nat := 3138527778731015484427729

theorem tailTrace_6112261 : CollatzResearch.WordTrace tailWord_6112261 prefixEnd_6112261 3138527778731015484427729 := by
  unfold tailWord_6112261
  simp only [CollatzResearch.WordTrace]
  refine ⟨222932473309329762915496637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148621648872886508610331091 222932473309329762915496637)
  ·
    refine ⟨83599677490998661093311239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222932473309329762915496637 83599677490998661093311239)
    ·
      refine ⟨125399516236497991639966859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83599677490998661093311239 125399516236497991639966859)
      ·
        refine ⟨188099274354746987459950289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125399516236497991639966859 188099274354746987459950289)
        ·
          refine ⟨141074455766060240594962717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188099274354746987459950289 141074455766060240594962717)
          ·
            refine ⟨52902920912272590223111019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141074455766060240594962717 52902920912272590223111019)
            ·
              refine ⟨79354381368408885334666529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52902920912272590223111019 79354381368408885334666529)
              ·
                refine ⟨59515786026306664000999897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79354381368408885334666529 59515786026306664000999897)
                ·
                  refine ⟨44636839519729998000749923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59515786026306664000999897 44636839519729998000749923)
                  ·
                    refine ⟨66955259279594997001124885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44636839519729998000749923 66955259279594997001124885)
                    ·
                      refine ⟨3138527778731015484427729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66955259279594997001124885 3138527778731015484427729)
                      ·
                        rfl

theorem cell23_6112261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_6112261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112261 prefixEnd_6112261 := by exact prefixLift 6112261
  have htrace : WordTrace (prefixWord ++ tailWord_6112261) baseStart_6112261 baseEnd_6112261 := by
    simpa [prefixWord, tailWord_6112261, baseEnd_6112261] using wordTrace_append hprefix tailTrace_6112261
  have hstable : (prefixWord ++ tailWord_6112261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112261).length < 2 ^ (prefixWord ++ tailWord_6112261).sum := by decide
  have hdescent : baseEnd_6112261 < baseStart_6112261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112268 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 1, 4, 3]
def baseStart_6112268 : Nat := 118140960795 + 6112268 * 2 ^ 59
def prefixEnd_6112268 : Nat := 4983230072969 + 3 ^ 40 * 6112268 * 2
def baseEnd_6112268 : Nat := 3138531373095596957040197

theorem tailTrace_6112268 : CollatzResearch.WordTrace tailWord_6112268 prefixEnd_6112268 3138531373095596957040197 := by
  unfold tailWord_6112268
  simp only [CollatzResearch.WordTrace]
  refine ⟨111466364310152201555500729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148621819080202935407334305 111466364310152201555500729)
  ·
    refine ⟨83599773232614151166625547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111466364310152201555500729 83599773232614151166625547)
    ·
      refine ⟨125399659848921226749938321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83599773232614151166625547 125399659848921226749938321)
      ·
        refine ⟨94049744886690920062453741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125399659848921226749938321 94049744886690920062453741)
        ·
          refine ⟨35268654332509095023420153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94049744886690920062453741 35268654332509095023420153)
          ·
            refine ⟨26451490749381821267565115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35268654332509095023420153 26451490749381821267565115)
            ·
              refine ⟨39677236124072731901347673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26451490749381821267565115 39677236124072731901347673)
              ·
                refine ⟨29757927093054548926010755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39677236124072731901347673 29757927093054548926010755)
                ·
                  refine ⟨44636890639581823389016133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29757927093054548926010755 44636890639581823389016133)
                  ·
                    refine ⟨8369416994921591885440525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44636890639581823389016133 8369416994921591885440525)
                    ·
                      refine ⟨3138531373095596957040197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8369416994921591885440525 3138531373095596957040197)
                      ·
                        rfl

theorem cell23_6112268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_6112268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112268 prefixEnd_6112268 := by exact prefixLift 6112268
  have htrace : WordTrace (prefixWord ++ tailWord_6112268) baseStart_6112268 baseEnd_6112268 := by
    simpa [prefixWord, tailWord_6112268, baseEnd_6112268] using wordTrace_append hprefix tailTrace_6112268
  have hstable : (prefixWord ++ tailWord_6112268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112268).length < 2 ^ (prefixWord ++ tailWord_6112268).sum := by decide
  have hdescent : baseEnd_6112268 < baseStart_6112268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112311 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 7]
def baseStart_6112311 : Nat := 118140960795 + 6112311 * 2 ^ 59
def prefixEnd_6112311 : Nat := 4983230072969 + 3 ^ 40 * 6112311 * 2
def baseEnd_6112311 : Nat := 3138553452763740288802499

theorem tailTrace_6112311 : CollatzResearch.WordTrace tailWord_6112311 prefixEnd_6112311 3138553452763740288802499 := by
  unfold tailWord_6112311
  simp only [CollatzResearch.WordTrace]
  refine ⟨222934296959148621454816787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148622864639432414303211191 222934296959148621454816787)
  ·
    refine ⟨334401445438722932182225181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222934296959148621454816787 334401445438722932182225181)
    ·
      refine ⟨125400542039521099568334443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334401445438722932182225181 125400542039521099568334443)
      ·
        refine ⟨188100813059281649352501665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125400542039521099568334443 188100813059281649352501665)
        ·
          refine ⟨141075609794461237014376249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188100813059281649352501665 141075609794461237014376249)
          ·
            refine ⟨105806707345845927760782187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141075609794461237014376249 105806707345845927760782187)
            ·
              refine ⟨158710061018768891641173281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105806707345845927760782187 158710061018768891641173281)
              ·
                refine ⟨119032545764076668730879961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158710061018768891641173281 119032545764076668730879961)
                ·
                  refine ⟨89274409323057501548159971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119032545764076668730879961 89274409323057501548159971)
                  ·
                    refine ⟨133911613984586252322239957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89274409323057501548159971 133911613984586252322239957)
                    ·
                      refine ⟨3138553452763740288802499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133911613984586252322239957 3138553452763740288802499)
                      ·
                        rfl

theorem cell23_6112311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_6112311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112311 prefixEnd_6112311 := by exact prefixLift 6112311
  have htrace : WordTrace (prefixWord ++ tailWord_6112311) baseStart_6112311 baseEnd_6112311 := by
    simpa [prefixWord, tailWord_6112311, baseEnd_6112311] using wordTrace_append hprefix tailTrace_6112311
  have hstable : (prefixWord ++ tailWord_6112311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112311).length < 2 ^ (prefixWord ++ tailWord_6112311).sum := by decide
  have hdescent : baseEnd_6112311 < baseStart_6112311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112361 : List Nat := [1, 2, 1, 1, 1, 17]
def baseStart_6112361 : Nat := 118140960795 + 6112361 * 2 ^ 59
def prefixEnd_6112361 : Nat := 4983230072969 + 3 ^ 40 * 6112361 * 2
def baseEnd_6112361 : Nat := 12915963484759115609783

theorem tailTrace_6112361 : CollatzResearch.WordTrace tailWord_6112361 prefixEnd_6112361 12915963484759115609783 := by
  unfold tailWord_6112361
  simp only [CollatzResearch.WordTrace]
  refine ⟨222936120608967479994136937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148624080405978319996091291 222936120608967479994136937)
  ·
    refine ⟨167202090456725609995602703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222936120608967479994136937 167202090456725609995602703)
    ·
      refine ⟨250803135685088414993404055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167202090456725609995602703 250803135685088414993404055)
      ·
        refine ⟨376204703527632622490106083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250803135685088414993404055 376204703527632622490106083)
        ·
          refine ⟨564307055291448933735159125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376204703527632622490106083 564307055291448933735159125)
          ·
            refine ⟨12915963484759115609783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 17 564307055291448933735159125 12915963484759115609783)
            ·
              rfl

theorem cell23_6112361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 17].length) (baseStart_6112361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112361 prefixEnd_6112361 := by exact prefixLift 6112361
  have htrace : WordTrace (prefixWord ++ tailWord_6112361) baseStart_6112361 baseEnd_6112361 := by
    simpa [prefixWord, tailWord_6112361, baseEnd_6112361] using wordTrace_append hprefix tailTrace_6112361
  have hstable : (prefixWord ++ tailWord_6112361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112361).length < 2 ^ (prefixWord ++ tailWord_6112361).sum := by decide
  have hdescent : baseEnd_6112361 < baseStart_6112361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112366 : List Nat := [4, 1, 2, 2, 1, 2, 4, 2, 1, 1, 3]
def baseStart_6112366 : Nat := 118140960795 + 6112366 * 2 ^ 59
def prefixEnd_6112366 : Nat := 4983230072969 + 3 ^ 40 * 6112366 * 2
def baseEnd_6112366 : Nat := 3138581694199737573614747

theorem tailTrace_6112366 : CollatzResearch.WordTrace tailWord_6112366 prefixEnd_6112366 3138581694199737573614747 := by
  unfold tailWord_6112366
  simp only [CollatzResearch.WordTrace]
  refine ⟨27867037871743670731008619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148624201982632910565379301 27867037871743670731008619)
  ·
    refine ⟨41800556807615506096512929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27867037871743670731008619 41800556807615506096512929)
    ·
      refine ⟨31350417605711629572384697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41800556807615506096512929 31350417605711629572384697)
      ·
        refine ⟨23512813204283722179288523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31350417605711629572384697 23512813204283722179288523)
        ·
          refine ⟨35269219806425583268932785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23512813204283722179288523 35269219806425583268932785)
          ·
            refine ⟨26451914854819187451699589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35269219806425583268932785 26451914854819187451699589)
            ·
              refine ⟨4959734035278597647193673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26451914854819187451699589 4959734035278597647193673)
              ·
                refine ⟨3719800526458948235395255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4959734035278597647193673 3719800526458948235395255)
                ·
                  refine ⟨5579700789688422353092883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3719800526458948235395255 5579700789688422353092883)
                  ·
                    refine ⟨8369551184532633529639325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5579700789688422353092883 8369551184532633529639325)
                    ·
                      refine ⟨3138581694199737573614747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8369551184532633529639325 3138581694199737573614747)
                      ·
                        rfl

theorem cell23_6112366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_6112366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112366 prefixEnd_6112366 := by exact prefixLift 6112366
  have htrace : WordTrace (prefixWord ++ tailWord_6112366) baseStart_6112366 baseEnd_6112366 := by
    simpa [prefixWord, tailWord_6112366, baseEnd_6112366] using wordTrace_append hprefix tailTrace_6112366
  have hstable : (prefixWord ++ tailWord_6112366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112366).length < 2 ^ (prefixWord ++ tailWord_6112366).sum := by decide
  have hdescent : baseEnd_6112366 < baseStart_6112366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112368 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 4]
def baseStart_6112368 : Nat := 118140960795 + 6112368 * 2 ^ 59
def prefixEnd_6112368 : Nat := 4983230072969 + 3 ^ 40 * 6112368 * 2
def baseEnd_6112368 : Nat := 3138582721161046565789737

theorem tailTrace_6112368 : CollatzResearch.WordTrace tailWord_6112368 prefixEnd_6112368 3138582721161046565789737 := by
  unfold tailWord_6112368
  simp only [CollatzResearch.WordTrace]
  refine ⟨111468187959971060094820879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148624250613294746793094505 111468187959971060094820879)
  ·
    refine ⟨167202281939956590142231319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111468187959971060094820879 167202281939956590142231319)
    ·
      refine ⟨250803422909934885213346979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167202281939956590142231319 250803422909934885213346979)
      ·
        refine ⟨376205134364902327820020469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250803422909934885213346979 376205134364902327820020469)
        ·
          refine ⟨35269231346709593233126919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 376205134364902327820020469 35269231346709593233126919)
          ·
            refine ⟨52903847020064389849690379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35269231346709593233126919 52903847020064389849690379)
            ·
              refine ⟨79355770530096584774535569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52903847020064389849690379 79355770530096584774535569)
              ·
                refine ⟨59516827897572438580901677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79355770530096584774535569 59516827897572438580901677)
                ·
                  refine ⟨22318810461589664467838129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59516827897572438580901677 22318810461589664467838129)
                  ·
                    refine ⟨16739107846192248350878597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22318810461589664467838129 16739107846192248350878597)
                    ·
                      refine ⟨3138582721161046565789737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16739107846192248350878597 3138582721161046565789737)
                      ·
                        rfl

theorem cell23_6112368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_6112368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112368 prefixEnd_6112368 := by exact prefixLift 6112368
  have htrace : WordTrace (prefixWord ++ tailWord_6112368) baseStart_6112368 baseEnd_6112368 := by
    simpa [prefixWord, tailWord_6112368, baseEnd_6112368] using wordTrace_append hprefix tailTrace_6112368
  have hstable : (prefixWord ++ tailWord_6112368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112368).length < 2 ^ (prefixWord ++ tailWord_6112368).sum := by decide
  have hdescent : baseEnd_6112368 < baseStart_6112368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112385 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_6112385 : Nat := 118140960795 + 6112385 * 2 ^ 59
def prefixEnd_6112385 : Nat := 4983230072969 + 3 ^ 40 * 6112385 * 2
def baseEnd_6112385 : Nat := 3138591450332172999277159

theorem tailTrace_6112385 : CollatzResearch.WordTrace tailWord_6112385 prefixEnd_6112385 3138591450332172999277159 := by
  unfold tailWord_6112385
  simp only [CollatzResearch.WordTrace]
  refine ⟨222936995960880532093010609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148624663973920354728673739 222936995960880532093010609)
  ·
    refine ⟨167202746970660399069757957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222936995960880532093010609 167202746970660399069757957)
    ·
      refine ⟨31350515056998824825579617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167202746970660399069757957 31350515056998824825579617)
      ·
        refine ⟨23512886292749118619184713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31350515056998824825579617 23512886292749118619184713)
        ·
          refine ⟨17634664719561838964388535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23512886292749118619184713 17634664719561838964388535)
          ·
            refine ⟨26451997079342758446582803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17634664719561838964388535 26451997079342758446582803)
            ·
              refine ⟨39677995619014137669874205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26451997079342758446582803 39677995619014137669874205)
              ·
                refine ⟨14879248357130301626202827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39677995619014137669874205 14879248357130301626202827)
                ·
                  refine ⟨22318872535695452439304241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14879248357130301626202827 22318872535695452439304241)
                  ·
                    refine ⟨16739154401771589329478181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22318872535695452439304241 16739154401771589329478181)
                    ·
                      refine ⟨3138591450332172999277159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16739154401771589329478181 3138591450332172999277159)
                      ·
                        rfl

theorem cell23_6112385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_6112385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112385 prefixEnd_6112385 := by exact prefixLift 6112385
  have htrace : WordTrace (prefixWord ++ tailWord_6112385) baseStart_6112385 baseEnd_6112385 := by
    simpa [prefixWord, tailWord_6112385, baseEnd_6112385] using wordTrace_append hprefix tailTrace_6112385
  have hstable : (prefixWord ++ tailWord_6112385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112385).length < 2 ^ (prefixWord ++ tailWord_6112385).sum := by decide
  have hdescent : baseEnd_6112385 < baseStart_6112385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112389 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 3, 2, 2]
def baseStart_6112389 : Nat := 118140960795 + 6112389 * 2 ^ 59
def prefixEnd_6112389 : Nat := 4983230072969 + 3 ^ 40 * 6112389 * 2
def baseEnd_6112389 : Nat := 3138593504254790983627141

theorem tailTrace_6112389 : CollatzResearch.WordTrace tailWord_6112389 prefixEnd_6112389 3138593504254790983627141 := by
  unfold tailWord_6112389
  simp only [CollatzResearch.WordTrace]
  refine ⟨222937141852866040776156221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148624761235244027184104147 222937141852866040776156221)
  ·
    refine ⟨83601428194824765291058583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222937141852866040776156221 83601428194824765291058583)
    ·
      refine ⟨125402142292237147936587875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83601428194824765291058583 125402142292237147936587875)
      ·
        refine ⟨188103213438355721904881813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125402142292237147936587875 188103213438355721904881813)
        ·
          refine ⟨8817338129922924464291335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 188103213438355721904881813 8817338129922924464291335)
          ·
            refine ⟨13226007194884386696437003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8817338129922924464291335 13226007194884386696437003)
            ·
              refine ⟨19839010792326580044655505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13226007194884386696437003 19839010792326580044655505)
              ·
                refine ⟨14879258094244935033491629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19839010792326580044655505 14879258094244935033491629)
                ·
                  refine ⟨5579721785341850637559361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14879258094244935033491629 5579721785341850637559361)
                  ·
                    refine ⟨4184791339006387978169521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5579721785341850637559361 4184791339006387978169521)
                    ·
                      refine ⟨3138593504254790983627141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4184791339006387978169521 3138593504254790983627141)
                      ·
                        rfl

theorem cell23_6112389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 2, 2].length) (baseStart_6112389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112389 prefixEnd_6112389 := by exact prefixLift 6112389
  have htrace : WordTrace (prefixWord ++ tailWord_6112389) baseStart_6112389 baseEnd_6112389 := by
    simpa [prefixWord, tailWord_6112389, baseEnd_6112389] using wordTrace_append hprefix tailTrace_6112389
  have hstable : (prefixWord ++ tailWord_6112389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112389).length < 2 ^ (prefixWord ++ tailWord_6112389).sum := by decide
  have hdescent : baseEnd_6112389 < baseStart_6112389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112428 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 4]
def baseStart_6112428 : Nat := 118140960795 + 6112428 * 2 ^ 59
def prefixEnd_6112428 : Nat := 4983230072969 + 3 ^ 40 * 6112428 * 2
def baseEnd_6112428 : Nat := 3138613530000316331039461

theorem tailTrace_6112428 : CollatzResearch.WordTrace tailWord_6112428 prefixEnd_6112428 3138613530000316331039461 := by
  unfold tailWord_6112428
  simp only [CollatzResearch.WordTrace]
  refine ⟨111469282149862375218412969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148625709533149833624550625 111469282149862375218412969)
  ·
    refine ⟨83601961612396781413809727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111469282149862375218412969 83601961612396781413809727)
    ·
      refine ⟨125402942418595172120714591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83601961612396781413809727 125402942418595172120714591)
      ·
        refine ⟨188104413627892758181071887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125402942418595172120714591 188104413627892758181071887)
        ·
          refine ⟨282156620441839137271607831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188104413627892758181071887 282156620441839137271607831)
          ·
            refine ⟨423234930662758705907411747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282156620441839137271607831 423234930662758705907411747)
            ·
              refine ⟨634852395994138058861117621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423234930662758705907411747 634852395994138058861117621)
              ·
                refine ⟨59517412124450443018229777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 634852395994138058861117621 59517412124450443018229777)
                ·
                  refine ⟨44638059093337832263672333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59517412124450443018229777 44638059093337832263672333)
                  ·
                    refine ⟨16739272160001687098877125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44638059093337832263672333 16739272160001687098877125)
                    ·
                      refine ⟨3138613530000316331039461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16739272160001687098877125 3138613530000316331039461)
                      ·
                        rfl

theorem cell23_6112428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_6112428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112428 prefixEnd_6112428 := by exact prefixLift 6112428
  have htrace : WordTrace (prefixWord ++ tailWord_6112428) baseStart_6112428 baseEnd_6112428 := by
    simpa [prefixWord, tailWord_6112428, baseEnd_6112428] using wordTrace_append hprefix tailTrace_6112428
  have hstable : (prefixWord ++ tailWord_6112428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112428).length < 2 ^ (prefixWord ++ tailWord_6112428).sum := by decide
  have hdescent : baseEnd_6112428 < baseStart_6112428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112439 : List Nat := [1, 1, 3, 1, 4, 1, 5, 1, 2, 1, 3]
def baseStart_6112439 : Nat := 118140960795 + 6112439 * 2 ^ 59
def prefixEnd_6112439 : Nat := 4983230072969 + 3 ^ 40 * 6112439 * 2
def baseEnd_6112439 : Nat := 3138619178287515788001911

theorem tailTrace_6112439 : CollatzResearch.WordTrace tailWord_6112439 prefixEnd_6112439 3138619178287515788001911 := by
  unfold tailWord_6112439
  simp only [CollatzResearch.WordTrace]
  refine ⟨222938965502684899315476371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148625977001789932876984247 222938965502684899315476371)
  ·
    refine ⟨334408448254027348973214557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222938965502684899315476371 334408448254027348973214557)
    ·
      refine ⟨125403168095260255864955459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334408448254027348973214557 125403168095260255864955459)
      ·
        refine ⟨188104752142890383797433189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125403168095260255864955459 188104752142890383797433189)
        ·
          refine ⟨35269641026791946962018723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188104752142890383797433189 35269641026791946962018723)
          ·
            refine ⟨52904461540187920443028085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35269641026791946962018723 52904461540187920443028085)
            ·
              refine ⟨4959793269392617541533883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52904461540187920443028085 4959793269392617541533883)
              ·
                refine ⟨7439689904088926312300825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4959793269392617541533883 7439689904088926312300825)
                ·
                  refine ⟨5579767428066694734225619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7439689904088926312300825 5579767428066694734225619)
                  ·
                    refine ⟨8369651142100042101338429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5579767428066694734225619 8369651142100042101338429)
                    ·
                      refine ⟨3138619178287515788001911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8369651142100042101338429 3138619178287515788001911)
                      ·
                        rfl

theorem cell23_6112439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 2, 1, 3].length) (baseStart_6112439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112439 prefixEnd_6112439 := by exact prefixLift 6112439
  have htrace : WordTrace (prefixWord ++ tailWord_6112439) baseStart_6112439 baseEnd_6112439 := by
    simpa [prefixWord, tailWord_6112439, baseEnd_6112439] using wordTrace_append hprefix tailTrace_6112439
  have hstable : (prefixWord ++ tailWord_6112439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112439).length < 2 ^ (prefixWord ++ tailWord_6112439).sum := by decide
  have hdescent : baseEnd_6112439 < baseStart_6112439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112515 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 2, 5]
def baseStart_6112515 : Nat := 118140960795 + 6112515 * 2 ^ 59
def prefixEnd_6112515 : Nat := 4983230072969 + 3 ^ 40 * 6112515 * 2
def baseEnd_6112515 : Nat := 1046219400939085830217187

theorem tailTrace_6112515 : CollatzResearch.WordTrace tailWord_6112515 prefixEnd_6112515 1046219400939085830217187 := by
  unfold tailWord_6112515
  simp only [CollatzResearch.WordTrace]
  refine ⟨222941737450409564295242999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148627824966939709530161999 222941737450409564295242999)
  ·
    refine ⟨334412606175614346442864499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222941737450409564295242999 334412606175614346442864499)
    ·
      refine ⟨501618909263421519664296749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334412606175614346442864499 501618909263421519664296749)
      ·
        refine ⟨188107090973783069874111281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 501618909263421519664296749 188107090973783069874111281)
        ·
          refine ⟨141080318230337302405583461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188107090973783069874111281 141080318230337302405583461)
          ·
            refine ⟨26452559668188244201046899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141080318230337302405583461 26452559668188244201046899)
            ·
              refine ⟨39678839502282366301570349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26452559668188244201046899 39678839502282366301570349)
              ·
                refine ⟨14879564813355887363088881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39678839502282366301570349 14879564813355887363088881)
                ·
                  refine ⟨11159673610016915522316661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14879564813355887363088881 11159673610016915522316661)
                  ·
                    refine ⟨1046219400939085830217187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11159673610016915522316661 1046219400939085830217187)
                    ·
                      rfl

theorem cell23_6112515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 5].length) (baseStart_6112515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112515 prefixEnd_6112515 := by exact prefixLift 6112515
  have htrace : WordTrace (prefixWord ++ tailWord_6112515) baseStart_6112515 baseEnd_6112515 := by
    simpa [prefixWord, tailWord_6112515, baseEnd_6112515] using wordTrace_append hprefix tailTrace_6112515
  have hstable : (prefixWord ++ tailWord_6112515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112515).length < 2 ^ (prefixWord ++ tailWord_6112515).sum := by decide
  have hdescent : baseEnd_6112515 < baseStart_6112515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112528 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 6, 8]
def baseStart_6112528 : Nat := 118140960795 + 6112528 * 2 ^ 59
def prefixEnd_6112528 : Nat := 4983230072969 + 3 ^ 40 * 6112528 * 2
def baseEnd_6112528 : Nat := 1046221626021921979929667

theorem tailTrace_6112528 : CollatzResearch.WordTrace tailWord_6112528 prefixEnd_6112528 1046221626021921979929667 := by
  unfold tailWord_6112528
  simp only [CollatzResearch.WordTrace]
  refine ⟨111471105799681233757733119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148628141066241645010310825 111471105799681233757733119)
  ·
    refine ⟨167206658699521850636599679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111471105799681233757733119 167206658699521850636599679)
    ·
      refine ⟨250809988049282775954899519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167206658699521850636599679 250809988049282775954899519)
      ·
        refine ⟨376214982073924163932349279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250809988049282775954899519 376214982073924163932349279)
        ·
          refine ⟨564322473110886245898523919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376214982073924163932349279 564322473110886245898523919)
          ·
            refine ⟨846483709666329368847785879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564322473110886245898523919 846483709666329368847785879)
            ·
              refine ⟨1269725564499494053271678819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846483709666329368847785879 1269725564499494053271678819)
              ·
                refine ⟨1904588346749241079907518229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269725564499494053271678819 1904588346749241079907518229)
                ·
                  refine ⟨89277578753870675620664917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1904588346749241079907518229 89277578753870675620664917)
                  ·
                    refine ⟨1046221626021921979929667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89277578753870675620664917 1046221626021921979929667)
                    ·
                      rfl

theorem cell23_6112528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 8].length) (baseStart_6112528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112528 prefixEnd_6112528 := by exact prefixLift 6112528
  have htrace : WordTrace (prefixWord ++ tailWord_6112528) baseStart_6112528 baseEnd_6112528 := by
    simpa [prefixWord, tailWord_6112528, baseEnd_6112528] using wordTrace_append hprefix tailTrace_6112528
  have hstable : (prefixWord ++ tailWord_6112528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112528).length < 2 ^ (prefixWord ++ tailWord_6112528).sum := by decide
  have hdescent : baseEnd_6112528 < baseStart_6112528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112530 : List Nat := [3, 2, 4, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_6112530 : Nat := 118140960795 + 6112530 * 2 ^ 59
def prefixEnd_6112530 : Nat := 4983230072969 + 3 ^ 40 * 6112530 * 2
def baseEnd_6112530 : Nat := 3138665905027074931963993

theorem tailTrace_6112530 : CollatzResearch.WordTrace tailWord_6112530 prefixEnd_6112530 3138665905027074931963993 := by
  unfold tailWord_6112530
  simp only [CollatzResearch.WordTrace]
  refine ⟨55735571136338805464259761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148628189696903481238026029 55735571136338805464259761)
  ·
    refine ⟨41801678352254104098194821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55735571136338805464259761 41801678352254104098194821)
    ·
      refine ⟨7837814691047644518411529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41801678352254104098194821 7837814691047644518411529)
      ·
        refine ⟨5878361018285733388808647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7837814691047644518411529 5878361018285733388808647)
        ·
          refine ⟨8817541527428600083212971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5878361018285733388808647 8817541527428600083212971)
          ·
            refine ⟨13226312291142900124819457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8817541527428600083212971 13226312291142900124819457)
            ·
              refine ⟨9919734218357175093614593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13226312291142900124819457 9919734218357175093614593)
              ·
                refine ⟨7439800663767881320210945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9919734218357175093614593 7439800663767881320210945)
                ·
                  refine ⟨5579850497825910990158209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7439800663767881320210945 5579850497825910990158209)
                  ·
                    refine ⟨4184887873369433242618657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5579850497825910990158209 4184887873369433242618657)
                    ·
                      refine ⟨3138665905027074931963993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4184887873369433242618657 3138665905027074931963993)
                      ·
                        rfl

theorem cell23_6112530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_6112530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112530 prefixEnd_6112530 := by exact prefixLift 6112530
  have htrace : WordTrace (prefixWord ++ tailWord_6112530) baseStart_6112530 baseEnd_6112530 := by
    simpa [prefixWord, tailWord_6112530, baseEnd_6112530] using wordTrace_append hprefix tailTrace_6112530
  have hstable : (prefixWord ++ tailWord_6112530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112530).length < 2 ^ (prefixWord ++ tailWord_6112530).sum := by decide
  have hdescent : baseEnd_6112530 < baseStart_6112530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112562 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 5, 4]
def baseStart_6112562 : Nat := 118140960795 + 6112562 * 2 ^ 59
def prefixEnd_6112562 : Nat := 4983230072969 + 3 ^ 40 * 6112562 * 2
def baseEnd_6112562 : Nat := 1046227445469339602254615

theorem tailTrace_6112562 : CollatzResearch.WordTrace tailWord_6112562 prefixEnd_6112562 1046227445469339602254615 := by
  unfold tailWord_6112562
  simp only [CollatzResearch.WordTrace]
  refine ⟨55735862920309822830550985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148628967787492860881469293 55735862920309822830550985)
  ·
    refine ⟨41801897190232367122913239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55735862920309822830550985 41801897190232367122913239)
    ·
      refine ⟨62702845785348550684369859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41801897190232367122913239 62702845785348550684369859)
      ·
        refine ⟨94054268678022826026554789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62702845785348550684369859 94054268678022826026554789)
        ·
          refine ⟨17635175377129279879979023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94054268678022826026554789 17635175377129279879979023)
          ·
            refine ⟨26452763065693919819968535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17635175377129279879979023 26452763065693919819968535)
            ·
              refine ⟨39679144598540879729952803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26452763065693919819968535 39679144598540879729952803)
              ·
                refine ⟨59518716897811319594929205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39679144598540879729952803 59518716897811319594929205)
                ·
                  refine ⟨5579879709169811212024613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59518716897811319594929205 5579879709169811212024613)
                  ·
                    refine ⟨1046227445469339602254615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5579879709169811212024613 1046227445469339602254615)
                    ·
                      rfl

theorem cell23_6112562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_6112562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112562 prefixEnd_6112562 := by exact prefixLift 6112562
  have htrace : WordTrace (prefixWord ++ tailWord_6112562) baseStart_6112562 baseEnd_6112562 := by
    simpa [prefixWord, tailWord_6112562, baseEnd_6112562] using wordTrace_append hprefix tailTrace_6112562
  have hstable : (prefixWord ++ tailWord_6112562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112562).length < 2 ^ (prefixWord ++ tailWord_6112562).sum := by decide
  have hdescent : baseEnd_6112562 < baseStart_6112562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112572 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 1, 4, 3]
def baseStart_6112572 : Nat := 118140960795 + 6112572 * 2 ^ 59
def prefixEnd_6112572 : Nat := 4983230072969 + 3 ^ 40 * 6112572 * 2
def baseEnd_6112572 : Nat := 3138687471214563767638799

theorem tailTrace_6112572 : CollatzResearch.WordTrace tailWord_6112572 prefixEnd_6112572 3138687471214563767638799 := by
  unfold tailWord_6112572
  simp only [CollatzResearch.WordTrace]
  refine ⟨111471908205601531515033985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148629210940802042020045313 111471908205601531515033985)
  ·
    refine ⟨83603931154201148636275489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111471908205601531515033985 83603931154201148636275489)
    ·
      refine ⟨62702948365650861477206617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83603931154201148636275489 62702948365650861477206617)
      ·
        refine ⟨47027211274238146107904963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62702948365650861477206617 47027211274238146107904963)
        ·
          refine ⟨70540816911357219161857445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47027211274238146107904963 70540816911357219161857445)
          ·
            refine ⟨13226403170879478592848271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70540816911357219161857445 13226403170879478592848271)
            ·
              refine ⟨19839604756319217889272407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13226403170879478592848271 19839604756319217889272407)
              ·
                refine ⟨29759407134478826833908611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19839604756319217889272407 29759407134478826833908611)
                ·
                  refine ⟨44639110701718240250862917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29759407134478826833908611 44639110701718240250862917)
                  ·
                    refine ⟨8369833256572170047036797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44639110701718240250862917 8369833256572170047036797)
                    ·
                      refine ⟨3138687471214563767638799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8369833256572170047036797 3138687471214563767638799)
                      ·
                        rfl

theorem cell23_6112572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_6112572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112572 prefixEnd_6112572 := by exact prefixLift 6112572
  have htrace : WordTrace (prefixWord ++ tailWord_6112572) baseStart_6112572 baseEnd_6112572 := by
    simpa [prefixWord, tailWord_6112572, baseEnd_6112572] using wordTrace_append hprefix tailTrace_6112572
  have hstable : (prefixWord ++ tailWord_6112572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112572).length < 2 ^ (prefixWord ++ tailWord_6112572).sum := by decide
  have hdescent : baseEnd_6112572 < baseStart_6112572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112635 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 3, 6]
def baseStart_6112635 : Nat := 118140960795 + 6112635 * 2 ^ 59
def prefixEnd_6112635 : Nat := 4983230072969 + 3 ^ 40 * 6112635 * 2
def baseEnd_6112635 : Nat := 1046239940165265673717003

theorem tailTrace_6112635 : CollatzResearch.WordTrace tailWord_6112635 prefixEnd_6112635 1046239940165265673717003 := by
  unfold tailWord_6112635
  simp only [CollatzResearch.WordTrace]
  refine ⟨222946114209974824789611359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148630742806649883193074239 222946114209974824789611359)
  ·
    refine ⟨334419171314962237184417039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222946114209974824789611359 334419171314962237184417039)
    ·
      refine ⟨501628756972443355776625559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334419171314962237184417039 501628756972443355776625559)
      ·
        refine ⟨752443135458665033664938339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501628756972443355776625559 752443135458665033664938339)
        ·
          refine ⟨1128664703187997550497407509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752443135458665033664938339 1128664703187997550497407509)
          ·
            refine ⟨52906157961937385179565977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1128664703187997550497407509 52906157961937385179565977)
            ·
              refine ⟨39679618471453038884674483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52906157961937385179565977 39679618471453038884674483)
              ·
                refine ⟨59519427707179558327011725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39679618471453038884674483 59519427707179558327011725)
                ·
                  refine ⟨22319785390192334372629397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59519427707179558327011725 22319785390192334372629397)
                  ·
                    refine ⟨1046239940165265673717003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22319785390192334372629397 1046239940165265673717003)
                    ·
                      rfl

theorem cell23_6112635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 6].length) (baseStart_6112635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112635 prefixEnd_6112635 := by exact prefixLift 6112635
  have htrace : WordTrace (prefixWord ++ tailWord_6112635) baseStart_6112635 baseEnd_6112635 := by
    simpa [prefixWord, tailWord_6112635, baseEnd_6112635] using wordTrace_append hprefix tailTrace_6112635
  have hstable : (prefixWord ++ tailWord_6112635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112635).length < 2 ^ (prefixWord ++ tailWord_6112635).sum := by decide
  have hdescent : baseEnd_6112635 < baseStart_6112635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112652 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 4, 4]
def baseStart_6112652 : Nat := 118140960795 + 6112652 * 2 ^ 59
def prefixEnd_6112652 : Nat := 4983230072969 + 3 ^ 40 * 6112652 * 2
def baseEnd_6112652 : Nat := 1046242849888974484879477

theorem tailTrace_6112652 : CollatzResearch.WordTrace tailWord_6112652 prefixEnd_6112652 1046242849888974484879477 := by
  unfold tailWord_6112652
  simp only [CollatzResearch.WordTrace]
  refine ⟨111473367125456618346490105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148631156167275491128653473 111473367125456618346490105)
  ·
    refine ⟨83605025344092463759867579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111473367125456618346490105 83605025344092463759867579)
    ·
      refine ⟨125407538016138695639801369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83605025344092463759867579 125407538016138695639801369)
      ·
        refine ⟨94055653512104021729851027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125407538016138695639801369 94055653512104021729851027)
        ·
          refine ⟨141083480268156032594776541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94055653512104021729851027 141083480268156032594776541)
          ·
            refine ⟨52906305100558512223041203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141083480268156032594776541 52906305100558512223041203)
            ·
              refine ⟨79359457650837768334561805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52906305100558512223041203 79359457650837768334561805)
              ·
                refine ⟨29759796619064163125460677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79359457650837768334561805 29759796619064163125460677)
                ·
                  refine ⟨5579961866074530586023877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29759796619064163125460677 5579961866074530586023877)
                  ·
                    refine ⟨1046242849888974484879477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5579961866074530586023877 1046242849888974484879477)
                    ·
                      rfl

theorem cell23_6112652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_6112652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112652 prefixEnd_6112652 := by exact prefixLift 6112652
  have htrace : WordTrace (prefixWord ++ tailWord_6112652) baseStart_6112652 baseEnd_6112652 := by
    simpa [prefixWord, tailWord_6112652, baseEnd_6112652] using wordTrace_append hprefix tailTrace_6112652
  have hstable : (prefixWord ++ tailWord_6112652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112652).length < 2 ^ (prefixWord ++ tailWord_6112652).sum := by decide
  have hdescent : baseEnd_6112652 < baseStart_6112652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112665 : List Nat := [1, 2, 1, 2, 1, 5, 1, 10]
def baseStart_6112665 : Nat := 118140960795 + 6112665 * 2 ^ 59
def prefixEnd_6112665 : Nat := 4983230072969 + 3 ^ 40 * 6112665 * 2
def baseEnd_6112665 : Nat := 116249452774645626065773

theorem tailTrace_6112665 : CollatzResearch.WordTrace tailWord_6112665 prefixEnd_6112665 116249452774645626065773 := by
  unfold tailWord_6112665
  simp only [CollatzResearch.WordTrace]
  refine ⟨222947208399866139913203449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148631472266577426608802299 222947208399866139913203449)
  ·
    refine ⟨167210406299899604934902587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222947208399866139913203449 167210406299899604934902587)
    ·
      refine ⟨250815609449849407402353881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167210406299899604934902587 250815609449849407402353881)
      ·
        refine ⟨188111707087387055551765411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250815609449849407402353881 188111707087387055551765411)
        ·
          refine ⟨282167560631080583327648117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188111707087387055551765411 282167560631080583327648117)
          ·
            refine ⟨26453208809163804686967011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 282167560631080583327648117 26453208809163804686967011)
            ·
              refine ⟨39679813213745707030450517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26453208809163804686967011 39679813213745707030450517)
              ·
                refine ⟨116249452774645626065773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39679813213745707030450517 116249452774645626065773)
                ·
                  rfl

theorem cell23_6112665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 10].length) (baseStart_6112665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112665 prefixEnd_6112665 := by exact prefixLift 6112665
  have htrace : WordTrace (prefixWord ++ tailWord_6112665) baseStart_6112665 baseEnd_6112665 := by
    simpa [prefixWord, tailWord_6112665, baseEnd_6112665] using wordTrace_append hprefix tailTrace_6112665
  have hstable : (prefixWord ++ tailWord_6112665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112665).length < 2 ^ (prefixWord ++ tailWord_6112665).sum := by decide
  have hdescent : baseEnd_6112665 < baseStart_6112665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112672 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 4]
def baseStart_6112672 : Nat := 118140960795 + 6112672 * 2 ^ 59
def prefixEnd_6112672 : Nat := 4983230072969 + 3 ^ 40 * 6112672 * 2
def baseEnd_6112672 : Nat := 3138738819280013376388339

theorem tailTrace_6112672 : CollatzResearch.WordTrace tailWord_6112672 prefixEnd_6112672 3138738819280013376388339 := by
  unfold tailWord_6112672
  simp only [CollatzResearch.WordTrace]
  refine ⟨111473731855420390054354135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148631642473893853405805513 111473731855420390054354135)
  ·
    refine ⟨167210597783130585081531203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111473731855420390054354135 167210597783130585081531203)
    ·
      refine ⟨250815896674695877622296805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167210597783130585081531203 250815896674695877622296805)
      ·
        refine ⟨47027980626505477054180651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250815896674695877622296805 47027980626505477054180651)
        ·
          refine ⟨70541970939758215581270977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47027980626505477054180651 70541970939758215581270977)
          ·
            refine ⟨52906478204818661685953233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70541970939758215581270977 52906478204818661685953233)
            ·
              refine ⟨39679858653613996264464925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52906478204818661685953233 39679858653613996264464925)
              ·
                refine ⟨14879946995105248599174347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39679858653613996264464925 14879946995105248599174347)
                ·
                  refine ⟨22319920492657872898761521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14879946995105248599174347 22319920492657872898761521)
                  ·
                    refine ⟨16739940369493404674071141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22319920492657872898761521 16739940369493404674071141)
                    ·
                      refine ⟨3138738819280013376388339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16739940369493404674071141 3138738819280013376388339)
                      ·
                        rfl

theorem cell23_6112672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_6112672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112672 prefixEnd_6112672 := by exact prefixLift 6112672
  have htrace : WordTrace (prefixWord ++ tailWord_6112672) baseStart_6112672 baseEnd_6112672 := by
    simpa [prefixWord, tailWord_6112672, baseEnd_6112672] using wordTrace_append hprefix tailTrace_6112672
  have hstable : (prefixWord ++ tailWord_6112672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112672).length < 2 ^ (prefixWord ++ tailWord_6112672).sum := by decide
  have hdescent : baseEnd_6112672 < baseStart_6112672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112679 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_6112679 : Nat := 118140960795 + 6112679 * 2 ^ 59
def prefixEnd_6112679 : Nat := 4983230072969 + 3 ^ 40 * 6112679 * 2
def baseEnd_6112679 : Nat := 3138742413644594849000807

theorem tailTrace_6112679 : CollatzResearch.WordTrace tailWord_6112679 prefixEnd_6112679 3138742413644594849000807 := by
  unfold tailWord_6112679
  simp only [CollatzResearch.WordTrace]
  refine ⟨222947719021815420304213091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148631812681210280202808727 222947719021815420304213091)
  ·
    refine ⟨334421578532723130456319637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222947719021815420304213091 334421578532723130456319637)
    ·
      refine ⟨15676011493721396740139983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 334421578532723130456319637 15676011493721396740139983)
      ·
        refine ⟨23514017240582095110209975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15676011493721396740139983 23514017240582095110209975)
        ·
          refine ⟨35271025860873142665314963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23514017240582095110209975 35271025860873142665314963)
          ·
            refine ⟨52906538791309713997972445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35271025860873142665314963 52906538791309713997972445)
            ·
              refine ⟨19839952046741142749239667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52906538791309713997972445 19839952046741142749239667)
              ·
                refine ⟨29759928070111714123859501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19839952046741142749239667 29759928070111714123859501)
                ·
                  refine ⟨11159973026291892796447313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29759928070111714123859501 11159973026291892796447313)
                  ·
                    refine ⟨8369979769718919597335485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11159973026291892796447313 8369979769718919597335485)
                    ·
                      refine ⟨3138742413644594849000807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8369979769718919597335485 3138742413644594849000807)
                      ·
                        rfl

theorem cell23_6112679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_6112679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112679 prefixEnd_6112679 := by exact prefixLift 6112679
  have htrace : WordTrace (prefixWord ++ tailWord_6112679) baseStart_6112679 baseEnd_6112679 := by
    simpa [prefixWord, tailWord_6112679, baseEnd_6112679] using wordTrace_append hprefix tailTrace_6112679
  have hstable : (prefixWord ++ tailWord_6112679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112679).length < 2 ^ (prefixWord ++ tailWord_6112679).sum := by decide
  have hdescent : baseEnd_6112679 < baseStart_6112679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112719 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 3, 3, 2]
def baseStart_6112719 : Nat := 118140960795 + 6112719 * 2 ^ 59
def prefixEnd_6112719 : Nat := 4983230072969 + 3 ^ 40 * 6112719 * 2
def baseEnd_6112719 : Nat := 3138762952870774692500623

theorem tailTrace_6112719 : CollatzResearch.WordTrace tailWord_6112719 prefixEnd_6112719 3138762952870774692500623 := by
  unfold tailWord_6112719
  simp only [CollatzResearch.WordTrace]
  refine ⟨222949177941670507135669211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148632785294447004757112807 222949177941670507135669211)
  ·
    refine ⟨334423766912505760703503817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222949177941670507135669211 334423766912505760703503817)
    ·
      refine ⟨250817825184379320527627863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334423766912505760703503817 250817825184379320527627863)
      ·
        refine ⟨376226737776568980791441795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250817825184379320527627863 376226737776568980791441795)
        ·
          refine ⟨564340106664853471187162693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376226737776568980791441795 564340106664853471187162693)
          ·
            refine ⟨105813769999660025847593005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 564340106664853471187162693 105813769999660025847593005)
            ·
              refine ⟨39680163749872509692847377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105813769999660025847593005 39680163749872509692847377)
              ·
                refine ⟨29760122812404382269635533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39680163749872509692847377 29760122812404382269635533)
                ·
                  refine ⟨11160046054651643351113325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29760122812404382269635533 11160046054651643351113325)
                  ·
                    refine ⟨4185017270494366256667497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11160046054651643351113325 4185017270494366256667497)
                    ·
                      refine ⟨3138762952870774692500623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4185017270494366256667497 3138762952870774692500623)
                      ·
                        rfl

theorem cell23_6112719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 3, 2].length) (baseStart_6112719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112719 prefixEnd_6112719 := by exact prefixLift 6112719
  have htrace : WordTrace (prefixWord ++ tailWord_6112719) baseStart_6112719 baseEnd_6112719 := by
    simpa [prefixWord, tailWord_6112719, baseEnd_6112719] using wordTrace_append hprefix tailTrace_6112719
  have hstable : (prefixWord ++ tailWord_6112719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112719).length < 2 ^ (prefixWord ++ tailWord_6112719).sum := by decide
  have hdescent : baseEnd_6112719 < baseStart_6112719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112726 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_6112726 : Nat := 118140960795 + 6112726 * 2 ^ 59
def prefixEnd_6112726 : Nat := 4983230072969 + 3 ^ 40 * 6112726 * 2
def baseEnd_6112726 : Nat := 3138766547235356165113091

theorem tailTrace_6112726 : CollatzResearch.WordTrace tailWord_6112726 prefixEnd_6112726 3138766547235356165113091 := by
  unfold tailWord_6112726
  simp only [CollatzResearch.WordTrace]
  refine ⟨13934339578290321708198377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148632955501763431554116021 13934339578290321708198377)
  ·
    refine ⟨10450754683717741281148783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13934339578290321708198377 10450754683717741281148783)
    ·
      refine ⟨15676132025576611921723175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10450754683717741281148783 15676132025576611921723175)
      ·
        refine ⟨23514198038364917882584763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15676132025576611921723175 23514198038364917882584763)
        ·
          refine ⟨35271297057547376823877145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23514198038364917882584763 35271297057547376823877145)
          ·
            refine ⟨26453472793160532617907859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35271297057547376823877145 26453472793160532617907859)
            ·
              refine ⟨39680209189740798926861789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26453472793160532617907859 39680209189740798926861789)
              ·
                refine ⟨14880078446152799597573171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39680209189740798926861789 14880078446152799597573171)
                ·
                  refine ⟨22320117669229199396359757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14880078446152799597573171 22320117669229199396359757)
                  ·
                    refine ⟨8370044125960949773634909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22320117669229199396359757 8370044125960949773634909)
                    ·
                      refine ⟨3138766547235356165113091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8370044125960949773634909 3138766547235356165113091)
                      ·
                        rfl

theorem cell23_6112726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_6112726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112726 prefixEnd_6112726 := by exact prefixLift 6112726
  have htrace : WordTrace (prefixWord ++ tailWord_6112726) baseStart_6112726 baseEnd_6112726 := by
    simpa [prefixWord, tailWord_6112726, baseEnd_6112726] using wordTrace_append hprefix tailTrace_6112726
  have hstable : (prefixWord ++ tailWord_6112726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112726).length < 2 ^ (prefixWord ++ tailWord_6112726).sum := by decide
  have hdescent : baseEnd_6112726 < baseStart_6112726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112753 : List Nat := [1, 2, 2, 2, 3, 2, 4, 1, 1, 3, 2]
def baseStart_6112753 : Nat := 118140960795 + 6112753 * 2 ^ 59
def prefixEnd_6112753 : Nat := 4983230072969 + 3 ^ 40 * 6112753 * 2
def baseEnd_6112753 : Nat := 3138780411213027559475467

theorem tailTrace_6112753 : CollatzResearch.WordTrace tailWord_6112753 prefixEnd_6112753 3138780411213027559475467 := by
  unfold tailWord_6112753
  simp only [CollatzResearch.WordTrace]
  refine ⟨222950418023547330942406913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148633612015698220628271275 222950418023547330942406913)
  ·
    refine ⟨167212813517660498206805185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222950418023547330942406913 167212813517660498206805185)
    ·
      refine ⟨125409610138245373655103889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167212813517660498206805185 125409610138245373655103889)
      ·
        refine ⟨94057207603684030241327917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125409610138245373655103889 94057207603684030241327917)
        ·
          refine ⟨35271452851381511340497969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94057207603684030241327917 35271452851381511340497969)
          ·
            refine ⟨26453589638536133505373477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35271452851381511340497969 26453589638536133505373477)
            ·
              refine ⟨4960048057225525032257527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26453589638536133505373477 4960048057225525032257527)
              ·
                refine ⟨7440072085838287548386291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4960048057225525032257527 7440072085838287548386291)
                ·
                  refine ⟨11160108128757431322579437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7440072085838287548386291 11160108128757431322579437)
                  ·
                    refine ⟨4185040548284036745967289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11160108128757431322579437 4185040548284036745967289)
                    ·
                      refine ⟨3138780411213027559475467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4185040548284036745967289 3138780411213027559475467)
                      ·
                        rfl

theorem cell23_6112753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_6112753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112753 prefixEnd_6112753 := by exact prefixLift 6112753
  have htrace : WordTrace (prefixWord ++ tailWord_6112753) baseStart_6112753 baseEnd_6112753 := by
    simpa [prefixWord, tailWord_6112753, baseEnd_6112753] using wordTrace_append hprefix tailTrace_6112753
  have hstable : (prefixWord ++ tailWord_6112753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112753).length < 2 ^ (prefixWord ++ tailWord_6112753).sum := by decide
  have hdescent : baseEnd_6112753 < baseStart_6112753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112762 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4]
def baseStart_6112762 : Nat := 118140960795 + 6112762 * 2 ^ 59
def prefixEnd_6112762 : Nat := 4983230072969 + 3 ^ 40 * 6112762 * 2
def baseEnd_6112762 : Nat := 3138785032538918024262925

theorem tailTrace_6112762 : CollatzResearch.WordTrace tailWord_6112762 prefixEnd_6112762 3138785032538918024262925 := by
  unfold tailWord_6112762
  simp only [CollatzResearch.WordTrace]
  refine ⟨55737686570128681369871135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148633830853676483652989693 55737686570128681369871135)
  ·
    refine ⟨83606529855193022054806703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55737686570128681369871135 83606529855193022054806703)
    ·
      refine ⟨125409794782789533082210055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83606529855193022054806703 125409794782789533082210055)
      ·
        refine ⟨188114692174184299623315083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125409794782789533082210055 188114692174184299623315083)
        ·
          refine ⟨282172038261276449434972625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188114692174184299623315083 282172038261276449434972625)
          ·
            refine ⟨211629028695957337076229469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282172038261276449434972625 211629028695957337076229469)
            ·
              refine ⟨79360885760984001403586051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211629028695957337076229469 79360885760984001403586051)
              ·
                refine ⟨119041328641476002105379077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79360885760984001403586051 119041328641476002105379077)
                ·
                  refine ⟨22320249120276750394758577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119041328641476002105379077 22320249120276750394758577)
                  ·
                    refine ⟨16740186840207562796068933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22320249120276750394758577 16740186840207562796068933)
                    ·
                      refine ⟨3138785032538918024262925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16740186840207562796068933 3138785032538918024262925)
                      ·
                        rfl

theorem cell23_6112762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_6112762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112762 prefixEnd_6112762 := by exact prefixLift 6112762
  have htrace : WordTrace (prefixWord ++ tailWord_6112762) baseStart_6112762 baseEnd_6112762 := by
    simpa [prefixWord, tailWord_6112762, baseEnd_6112762] using wordTrace_append hprefix tailTrace_6112762
  have hstable : (prefixWord ++ tailWord_6112762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112762).length < 2 ^ (prefixWord ++ tailWord_6112762).sum := by decide
  have hdescent : baseEnd_6112762 < baseStart_6112762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112819 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 2, 5]
def baseStart_6112819 : Nat := 118140960795 + 6112819 * 2 ^ 59
def prefixEnd_6112819 : Nat := 4983230072969 + 3 ^ 40 * 6112819 * 2
def baseEnd_6112819 : Nat := 1046271433645408100416721

theorem tailTrace_6112819 : CollatzResearch.WordTrace tailWord_6112819 prefixEnd_6112819 1046271433645408100416721 := by
  unfold tailWord_6112819
  simp only [CollatzResearch.WordTrace]
  refine ⟨222952825241308224214309511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148635216827538816142873007 222952825241308224214309511)
  ·
    refine ⟨334429237861962336321464267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222952825241308224214309511 334429237861962336321464267)
    ·
      refine ⟨501643856792943504482196401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334429237861962336321464267 501643856792943504482196401)
      ·
        refine ⟨376232892594707628361647301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501643856792943504482196401 376232892594707628361647301)
        ·
          refine ⟨70543667361507680317808869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 376232892594707628361647301 70543667361507680317808869)
          ·
            refine ⟨13226937630282690059589163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70543667361507680317808869 13226937630282690059589163)
            ·
              refine ⟨19840406445424035089383745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13226937630282690059589163 19840406445424035089383745)
              ·
                refine ⟨14880304834068026317037809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19840406445424035089383745 14880304834068026317037809)
                ·
                  refine ⟨11160228625551019737778357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14880304834068026317037809 11160228625551019737778357)
                  ·
                    refine ⟨1046271433645408100416721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11160228625551019737778357 1046271433645408100416721)
                    ·
                      rfl

theorem cell23_6112819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 5].length) (baseStart_6112819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112819 prefixEnd_6112819 := by exact prefixLift 6112819
  have htrace : WordTrace (prefixWord ++ tailWord_6112819) baseStart_6112819 baseEnd_6112819 := by
    simpa [prefixWord, tailWord_6112819, baseEnd_6112819] using wordTrace_append hprefix tailTrace_6112819
  have hstable : (prefixWord ++ tailWord_6112819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112819).length < 2 ^ (prefixWord ++ tailWord_6112819).sum := by decide
  have hdescent : baseEnd_6112819 < baseStart_6112819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112849 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 5, 4]
def baseStart_6112849 : Nat := 118140960795 + 6112849 * 2 ^ 59
def prefixEnd_6112849 : Nat := 4983230072969 + 3 ^ 40 * 6112849 * 2
def baseEnd_6112849 : Nat := 1046276568451953061291675

theorem tailTrace_6112849 : CollatzResearch.WordTrace tailWord_6112849 prefixEnd_6112849 1046276568451953061291675 := by
  unfold tailWord_6112849
  simp only [CollatzResearch.WordTrace]
  refine ⟨222953919431199539337901601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148635946287466359558601067 222953919431199539337901601)
  ·
    refine ⟨167215439573399654503426201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222953919431199539337901601 167215439573399654503426201)
    ·
      refine ⟨125411579680049740877569651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167215439573399654503426201 125411579680049740877569651)
      ·
        refine ⟨188117369520074611316354477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125411579680049740877569651 188117369520074611316354477)
        ·
          refine ⟨70544013570027979243632929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188117369520074611316354477 70544013570027979243632929)
          ·
            refine ⟨52908010177520984432724697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70544013570027979243632929 52908010177520984432724697)
            ·
              refine ⟨39681007633140738324543523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52908010177520984432724697 39681007633140738324543523)
              ·
                refine ⟨59521511449711107486815285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39681007633140738324543523 59521511449711107486815285)
                ·
                  refine ⟨5580141698410416326888933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59521511449711107486815285 5580141698410416326888933)
                  ·
                    refine ⟨1046276568451953061291675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5580141698410416326888933 1046276568451953061291675)
                    ·
                      rfl

theorem cell23_6112849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_6112849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112849 prefixEnd_6112849 := by exact prefixLift 6112849
  have htrace : WordTrace (prefixWord ++ tailWord_6112849) baseStart_6112849 baseEnd_6112849 := by
    simpa [prefixWord, tailWord_6112849, baseEnd_6112849] using wordTrace_append hprefix tailTrace_6112849
  have hstable : (prefixWord ++ tailWord_6112849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112849).length < 2 ^ (prefixWord ++ tailWord_6112849).sum := by decide
  have hdescent : baseEnd_6112849 < baseStart_6112849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112930 : List Nat := [3, 3, 1, 4, 1, 2, 1, 2, 6]
def baseStart_6112930 : Nat := 118140960795 + 6112930 * 2 ^ 59
def prefixEnd_6112930 : Nat := 4983230072969 + 3 ^ 40 * 6112930 * 2
def baseEnd_6112930 : Nat := 348763477476541485218017

theorem tailTrace_6112930 : CollatzResearch.WordTrace tailWord_6112930 prefixEnd_6112930 348763477476541485218017 := by
  unfold tailWord_6112930
  simp only [CollatzResearch.WordTrace]
  refine ⟨55739218435976522542900061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148637915829270726781066829 55739218435976522542900061)
  ·
    refine ⟨20902206913491195953587523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55739218435976522542900061 20902206913491195953587523)
    ·
      refine ⟨31353310370236793930381285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20902206913491195953587523 31353310370236793930381285)
      ·
        refine ⟨5878745694419398861946491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31353310370236793930381285 5878745694419398861946491)
        ·
          refine ⟨8818118541629098292919737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5878745694419398861946491 8818118541629098292919737)
          ·
            refine ⟨6613588906221823719689803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8818118541629098292919737 6613588906221823719689803)
            ·
              refine ⟨9920383359332735579534705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6613588906221823719689803 9920383359332735579534705)
              ·
                refine ⟨7440287519499551684651029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9920383359332735579534705 7440287519499551684651029)
                ·
                  refine ⟨348763477476541485218017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7440287519499551684651029 348763477476541485218017)
                  ·
                    rfl

theorem cell23_6112930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_6112930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112930 prefixEnd_6112930 := by exact prefixLift 6112930
  have htrace : WordTrace (prefixWord ++ tailWord_6112930) baseStart_6112930 baseEnd_6112930 := by
    simpa [prefixWord, tailWord_6112930, baseEnd_6112930] using wordTrace_append hprefix tailTrace_6112930
  have hstable : (prefixWord ++ tailWord_6112930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112930).length < 2 ^ (prefixWord ++ tailWord_6112930).sum := by decide
  have hdescent : baseEnd_6112930 < baseStart_6112930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112950 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_6112950 : Nat := 118140960795 + 6112950 * 2 ^ 59
def prefixEnd_6112950 : Nat := 4983230072969 + 3 ^ 40 * 6112950 * 2
def baseEnd_6112950 : Nat := 3138881566901963288712061

theorem tailTrace_6112950 : CollatzResearch.WordTrace tailWord_6112950 prefixEnd_6112950 3138881566901963288712061 := by
  unfold tailWord_6112950
  simp only [CollatzResearch.WordTrace]
  refine ⟨13934850200239602099208019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148638402135889089058218869 13934850200239602099208019)
  ·
    refine ⟨20902275300359403148812029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13934850200239602099208019 20902275300359403148812029)
    ·
      refine ⟨7838353237634776180804511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20902275300359403148812029 7838353237634776180804511)
      ·
        refine ⟨11757529856452164271206767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7838353237634776180804511 11757529856452164271206767)
        ·
          refine ⟨17636294784678246406810151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11757529856452164271206767 17636294784678246406810151)
          ·
            refine ⟨26454442177017369610215227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17636294784678246406810151 26454442177017369610215227)
            ·
              refine ⟨39681663265526054415322841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26454442177017369610215227 39681663265526054415322841)
              ·
                refine ⟨29761247449144540811492131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39681663265526054415322841 29761247449144540811492131)
                ·
                  refine ⟨44641871173716811217238197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29761247449144540811492131 44641871173716811217238197)
                  ·
                    refine ⟨4185175422535951051616081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44641871173716811217238197 4185175422535951051616081)
                    ·
                      refine ⟨3138881566901963288712061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4185175422535951051616081 3138881566901963288712061)
                      ·
                        rfl

theorem cell23_6112950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_6112950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112950 prefixEnd_6112950 := by exact prefixLift 6112950
  have htrace : WordTrace (prefixWord ++ tailWord_6112950) baseStart_6112950 baseEnd_6112950 := by
    simpa [prefixWord, tailWord_6112950, baseEnd_6112950] using wordTrace_append hprefix tailTrace_6112950
  have hstable : (prefixWord ++ tailWord_6112950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112950).length < 2 ^ (prefixWord ++ tailWord_6112950).sum := by decide
  have hdescent : baseEnd_6112950 < baseStart_6112950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112956 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 1, 6]
def baseStart_6112956 : Nat := 118140960795 + 6112956 * 2 ^ 59
def prefixEnd_6112956 : Nat := 4983230072969 + 3 ^ 40 * 6112956 * 2
def baseEnd_6112956 : Nat := 1046294882595296755079011

theorem tailTrace_6112956 : CollatzResearch.WordTrace tailWord_6112956 prefixEnd_6112956 1046294882595296755079011 := by
  unfold tailWord_6112956
  simp only [CollatzResearch.WordTrace]
  refine ⟨111478911020905948306023361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148638548027874597741364481 111478911020905948306023361)
  ·
    refine ⟨83609183265679461229517521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111478911020905948306023361 83609183265679461229517521)
    ·
      refine ⟨62706887449259595922138141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83609183265679461229517521 62706887449259595922138141)
      ·
        refine ⟨23515082793472348470801803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62706887449259595922138141 23515082793472348470801803)
        ·
          refine ⟨35272624190208522706202705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23515082793472348470801803 35272624190208522706202705)
          ·
            refine ⟨26454468142656392029652029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35272624190208522706202705 26454468142656392029652029)
            ·
              refine ⟨9920425553496147011119511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26454468142656392029652029 9920425553496147011119511)
              ·
                refine ⟨14880638330244220516679267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9920425553496147011119511 14880638330244220516679267)
                ·
                  refine ⟨22320957495366330775018901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14880638330244220516679267 22320957495366330775018901)
                  ·
                    refine ⟨1046294882595296755079011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22320957495366330775018901 1046294882595296755079011)
                    ·
                      rfl

theorem cell23_6112956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_6112956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112956 prefixEnd_6112956 := by exact prefixLift 6112956
  have htrace : WordTrace (prefixWord ++ tailWord_6112956) baseStart_6112956 baseEnd_6112956 := by
    simpa [prefixWord, tailWord_6112956, baseEnd_6112956] using wordTrace_append hprefix tailTrace_6112956
  have hstable : (prefixWord ++ tailWord_6112956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112956).length < 2 ^ (prefixWord ++ tailWord_6112956).sum := by decide
  have hdescent : baseEnd_6112956 < baseStart_6112956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6112959 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 6]
def baseStart_6112959 : Nat := 118140960795 + 6112959 * 2 ^ 59
def prefixEnd_6112959 : Nat := 4983230072969 + 3 ^ 40 * 6112959 * 2
def baseEnd_6112959 : Nat := 3138886188227853753499519

theorem tailTrace_6112959 : CollatzResearch.WordTrace tailWord_6112959 prefixEnd_6112959 3138886188227853753499519 := by
  unfold tailWord_6112959
  simp only [CollatzResearch.WordTrace]
  refine ⟨222957931460801028124405931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148638620973867352082937287 222957931460801028124405931)
  ·
    refine ⟨334436897191201542186608897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222957931460801028124405931 334436897191201542186608897)
    ·
      refine ⟨250827672893401156639956673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334436897191201542186608897 250827672893401156639956673)
      ·
        refine ⟨188120754670050867479967505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250827672893401156639956673 188120754670050867479967505)
        ·
          refine ⟨141090566002538150609975629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188120754670050867479967505 141090566002538150609975629)
          ·
            refine ⟨52908962250951806478740861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141090566002538150609975629 52908962250951806478740861)
            ·
              refine ⟨19840860844106927429527823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52908962250951806478740861 19840860844106927429527823)
              ·
                refine ⟨29761291266160391144291735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19840860844106927429527823 29761291266160391144291735)
                ·
                  refine ⟨44641936899240586716437603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29761291266160391144291735 44641936899240586716437603)
                  ·
                    refine ⟨66962905348860880074656405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44641936899240586716437603 66962905348860880074656405)
                    ·
                      refine ⟨3138886188227853753499519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66962905348860880074656405 3138886188227853753499519)
                      ·
                        rfl

theorem cell23_6112959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_6112959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6112959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6112959 prefixEnd_6112959 := by exact prefixLift 6112959
  have htrace : WordTrace (prefixWord ++ tailWord_6112959) baseStart_6112959 baseEnd_6112959 := by
    simpa [prefixWord, tailWord_6112959, baseEnd_6112959] using wordTrace_append hprefix tailTrace_6112959
  have hstable : (prefixWord ++ tailWord_6112959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6112959).length < 2 ^ (prefixWord ++ tailWord_6112959).sum := by decide
  have hdescent : baseEnd_6112959 < baseStart_6112959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6112959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113019 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 4]
def baseStart_6113019 : Nat := 118140960795 + 6113019 * 2 ^ 59
def prefixEnd_6113019 : Nat := 4983230072969 + 3 ^ 40 * 6113019 * 2
def baseEnd_6113019 : Nat := 3138916997067123518749243

theorem tailTrace_6113019 : CollatzResearch.WordTrace tailWord_6113019 prefixEnd_6113019 3138916997067123518749243 := by
  unfold tailWord_6113019
  simp only [CollatzResearch.WordTrace]
  refine ⟨222960119840583658371590111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148640079893722438914393407 222960119840583658371590111)
  ·
    refine ⟨334440179760875487557385167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222960119840583658371590111 334440179760875487557385167)
    ·
      refine ⟨501660269641313231336077751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334440179760875487557385167 501660269641313231336077751)
      ·
        refine ⟨752490404461969847004116627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501660269641313231336077751 752490404461969847004116627)
        ·
          refine ⟨1128735606692954770506174941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752490404461969847004116627 1128735606692954770506174941)
          ·
            refine ⟨423275852509858038939815603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1128735606692954770506174941 423275852509858038939815603)
            ·
              refine ⟨634913778764787058409723405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423275852509858038939815603 634913778764787058409723405)
              ·
                refine ⟨238092667036795146903646277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 634913778764787058409723405 238092667036795146903646277)
                ·
                  refine ⟨44642375069399090044433677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 238092667036795146903646277 44642375069399090044433677)
                  ·
                    refine ⟨16740890651024658766662629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44642375069399090044433677 16740890651024658766662629)
                    ·
                      refine ⟨3138916997067123518749243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16740890651024658766662629 3138916997067123518749243)
                      ·
                        rfl

theorem cell23_6113019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 4].length) (baseStart_6113019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113019 prefixEnd_6113019 := by exact prefixLift 6113019
  have htrace : WordTrace (prefixWord ++ tailWord_6113019) baseStart_6113019 baseEnd_6113019 := by
    simpa [prefixWord, tailWord_6113019, baseEnd_6113019] using wordTrace_append hprefix tailTrace_6113019
  have hstable : (prefixWord ++ tailWord_6113019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113019).length < 2 ^ (prefixWord ++ tailWord_6113019).sum := by decide
  have hdescent : baseEnd_6113019 < baseStart_6113019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113029 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 6, 6]
def baseStart_6113029 : Nat := 118140960795 + 6113029 * 2 ^ 59
def prefixEnd_6113029 : Nat := 4983230072969 + 3 ^ 40 * 6113029 * 2
def baseEnd_6113029 : Nat := 1046307377291222826541399

theorem tailTrace_6113029 : CollatzResearch.WordTrace tailWord_6113029 prefixEnd_6113029 1046307377291222826541399 := by
  unfold tailWord_6113029
  simp only [CollatzResearch.WordTrace]
  refine ⟨222960484570547430079454141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148640323047031620052969427 222960484570547430079454141)
  ·
    refine ⟨83610181713955286279795303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222960484570547430079454141 83610181713955286279795303)
    ·
      refine ⟨125415272570932929419692955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83610181713955286279795303 125415272570932929419692955)
      ·
        refine ⟨188122908856399394129539433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125415272570932929419692955 188122908856399394129539433)
        ·
          refine ⟨141092181642299545597154575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188122908856399394129539433 141092181642299545597154575)
          ·
            refine ⟨211638272463449318395731863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141092181642299545597154575 211638272463449318395731863)
            ·
              refine ⟨317457408695173977593597795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211638272463449318395731863 317457408695173977593597795)
              ·
                refine ⟨476186113042760966390396693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317457408695173977593597795 476186113042760966390396693)
                ·
                  refine ⟨22321224048879420299549845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 476186113042760966390396693 22321224048879420299549845)
                  ·
                    refine ⟨1046307377291222826541399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22321224048879420299549845 1046307377291222826541399)
                    ·
                      rfl

theorem cell23_6113029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_6113029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113029 prefixEnd_6113029 := by exact prefixLift 6113029
  have htrace : WordTrace (prefixWord ++ tailWord_6113029) baseStart_6113029 baseEnd_6113029 := by
    simpa [prefixWord, tailWord_6113029, baseEnd_6113029] using wordTrace_append hprefix tailTrace_6113029
  have hstable : (prefixWord ++ tailWord_6113029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113029).length < 2 ^ (prefixWord ++ tailWord_6113029).sum := by decide
  have hdescent : baseEnd_6113029 < baseStart_6113029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113037 : List Nat := [1, 7, 2, 1, 2, 10]
def baseStart_6113037 : Nat := 118140960795 + 6113037 * 2 ^ 59
def prefixEnd_6113037 : Nat := 4983230072969 + 3 ^ 40 * 6113037 * 2
def baseEnd_6113037 : Nat := 12917391932999606783227

theorem tailTrace_6113037 : CollatzResearch.WordTrace tailWord_6113037 prefixEnd_6113037 12917391932999606783227 := by
  unfold tailWord_6113037
  simp only [CollatzResearch.WordTrace]
  refine ⟨222960776354518447445745365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148640517569678964963830243 222960776354518447445745365)
  ·
    refine ⟨5225643195809026112009657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 222960776354518447445745365 5225643195809026112009657)
    ·
      refine ⟨3919232396856769584007243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5225643195809026112009657 3919232396856769584007243)
      ·
        refine ⟨5878848595285154376010865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3919232396856769584007243 5878848595285154376010865)
        ·
          refine ⟨4409136446463865782008149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5878848595285154376010865 4409136446463865782008149)
          ·
            refine ⟨12917391932999606783227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4409136446463865782008149 12917391932999606783227)
            ·
              rfl

theorem cell23_6113037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 10].length) (baseStart_6113037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113037 prefixEnd_6113037 := by exact prefixLift 6113037
  have htrace : WordTrace (prefixWord ++ tailWord_6113037) baseStart_6113037 baseEnd_6113037 := by
    simpa [prefixWord, tailWord_6113037, baseEnd_6113037] using wordTrace_append hprefix tailTrace_6113037
  have hstable : (prefixWord ++ tailWord_6113037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113037).length < 2 ^ (prefixWord ++ tailWord_6113037).sum := by decide
  have hdescent : baseEnd_6113037 < baseStart_6113037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113039 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 5]
def baseStart_6113039 : Nat := 118140960795 + 6113039 * 2 ^ 59
def prefixEnd_6113039 : Nat := 4983230072969 + 3 ^ 40 * 6113039 * 2
def baseEnd_6113039 : Nat := 3138927266680213440499151

theorem tailTrace_6113039 : CollatzResearch.WordTrace tailWord_6113039 prefixEnd_6113039 3138927266680213440499151 := by
  unfold tailWord_6113039
  simp only [CollatzResearch.WordTrace]
  refine ⟨222960849300511201787318171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148640566200340801191545447 222960849300511201787318171)
  ·
    refine ⟨334441273950766802680977257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222960849300511201787318171 334441273950766802680977257)
    ·
      refine ⟨250830955463075102010732943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334441273950766802680977257 250830955463075102010732943)
      ·
        refine ⟨376246433194612653016099415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250830955463075102010732943 376246433194612653016099415)
        ·
          refine ⟨564369649791918979524149123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376246433194612653016099415 564369649791918979524149123)
          ·
            refine ⟨846554474687878469286223685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564369649791918979524149123 846554474687878469286223685)
            ·
              refine ⟨158728964003977212991166941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 846554474687878469286223685 158728964003977212991166941)
              ·
                refine ⟨59523361501491454871687603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158728964003977212991166941 59523361501491454871687603)
                ·
                  refine ⟨89285042252237182307531405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59523361501491454871687603 89285042252237182307531405)
                  ·
                    refine ⟨33481890844588943365324277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89285042252237182307531405 33481890844588943365324277)
                    ·
                      refine ⟨3138927266680213440499151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33481890844588943365324277 3138927266680213440499151)
                      ·
                        rfl

theorem cell23_6113039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_6113039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113039 prefixEnd_6113039 := by exact prefixLift 6113039
  have htrace : WordTrace (prefixWord ++ tailWord_6113039) baseStart_6113039 baseEnd_6113039 := by
    simpa [prefixWord, tailWord_6113039, baseEnd_6113039] using wordTrace_append hprefix tailTrace_6113039
  have hstable : (prefixWord ++ tailWord_6113039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113039).length < 2 ^ (prefixWord ++ tailWord_6113039).sum := by decide
  have hdescent : baseEnd_6113039 < baseStart_6113039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113056 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 3]
def baseStart_6113056 : Nat := 118140960795 + 6113056 * 2 ^ 59
def prefixEnd_6113056 : Nat := 4983230072969 + 3 ^ 40 * 6113056 * 2
def baseEnd_6113056 : Nat := 3138935995851339873986573

theorem tailTrace_6113056 : CollatzResearch.WordTrace tailWord_6113056 prefixEnd_6113056 3138935995851339873986573 := by
  unfold tailWord_6113056
  simp only [CollatzResearch.WordTrace]
  refine ⟨111480734670724806845343511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148640979560966409127124681 111480734670724806845343511)
  ·
    refine ⟨167221102006087210268015267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111480734670724806845343511 167221102006087210268015267)
    ·
      refine ⟨250831653009130815402022901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167221102006087210268015267 250831653009130815402022901)
      ·
        refine ⟨23515467469606013943939647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 250831653009130815402022901 23515467469606013943939647)
        ·
          refine ⟨35273201204409020915909471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23515467469606013943939647 35273201204409020915909471)
          ·
            refine ⟨52909801806613531373864207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35273201204409020915909471 52909801806613531373864207)
            ·
              refine ⟨79364702709920297060796311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52909801806613531373864207 79364702709920297060796311)
              ·
                refine ⟨119047054064880445591194467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79364702709920297060796311 119047054064880445591194467)
                ·
                  refine ⟨178570581097320668386791701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119047054064880445591194467 178570581097320668386791701)
                  ·
                    refine ⟨8370495988936906330630861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 178570581097320668386791701 8370495988936906330630861)
                    ·
                      refine ⟨3138935995851339873986573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8370495988936906330630861 3138935995851339873986573)
                      ·
                        rfl

theorem cell23_6113056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_6113056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113056 prefixEnd_6113056 := by exact prefixLift 6113056
  have htrace : WordTrace (prefixWord ++ tailWord_6113056) baseStart_6113056 baseEnd_6113056 := by
    simpa [prefixWord, tailWord_6113056, baseEnd_6113056] using wordTrace_append hprefix tailTrace_6113056
  have hstable : (prefixWord ++ tailWord_6113056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113056).length < 2 ^ (prefixWord ++ tailWord_6113056).sum := by decide
  have hdescent : baseEnd_6113056 < baseStart_6113056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113093 : List Nat := [1, 3, 1, 1, 1, 2, 6, 3, 5]
def baseStart_6113093 : Nat := 118140960795 + 6113093 * 2 ^ 59
def prefixEnd_6113093 : Nat := 4983230072969 + 3 ^ 40 * 6113093 * 2
def baseEnd_6113093 : Nat := 348772777181728469913767

theorem tailTrace_6113093 : CollatzResearch.WordTrace tailWord_6113093 prefixEnd_6113093 348772777181728469913767 := by
  unfold tailWord_6113093
  simp only [CollatzResearch.WordTrace]
  refine ⟨222962818842315569009783933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148641879228210379339855955 222962818842315569009783933)
  ·
    refine ⟨83611057065868338378668975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222962818842315569009783933 83611057065868338378668975)
    ·
      refine ⟨125416585598802507568003463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83611057065868338378668975 125416585598802507568003463)
      ·
        refine ⟨188124878398203761352005195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125416585598802507568003463 188124878398203761352005195)
        ·
          refine ⟨282187317597305642028007793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188124878398203761352005195 282187317597305642028007793)
          ·
            refine ⟨211640488197979231521005845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282187317597305642028007793 211640488197979231521005845)
            ·
              refine ⟨9920647884280276477547149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 211640488197979231521005845 9920647884280276477547149)
              ·
                refine ⟨3720242956605103679080181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9920647884280276477547149 3720242956605103679080181)
                ·
                  refine ⟨348772777181728469913767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3720242956605103679080181 348772777181728469913767)
                  ·
                    rfl

theorem cell23_6113093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 5].length) (baseStart_6113093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113093 prefixEnd_6113093 := by exact prefixLift 6113093
  have htrace : WordTrace (prefixWord ++ tailWord_6113093) baseStart_6113093 baseEnd_6113093 := by
    simpa [prefixWord, tailWord_6113093, baseEnd_6113093] using wordTrace_append hprefix tailTrace_6113093
  have hstable : (prefixWord ++ tailWord_6113093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113093).length < 2 ^ (prefixWord ++ tailWord_6113093).sum := by decide
  have hdescent : baseEnd_6113093 < baseStart_6113093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113156 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_6113156 : Nat := 118140960795 + 6113156 * 2 ^ 59
def prefixEnd_6113156 : Nat := 4983230072969 + 3 ^ 40 * 6113156 * 2
def baseEnd_6113156 : Nat := 3138987343916789482736113

theorem tailTrace_6113156 : CollatzResearch.WordTrace tailWord_6113156 prefixEnd_6113156 3138987343916789482736113 := by
  unfold tailWord_6113156
  simp only [CollatzResearch.WordTrace]
  refine ⟨111482558320543665384663661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148643411094058220512884881 111482558320543665384663661)
  ·
    refine ⟨41805959370203874519248873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111482558320543665384663661 41805959370203874519248873)
    ·
      refine ⟨31354469527652905889436655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41805959370203874519248873 31354469527652905889436655)
      ·
        refine ⟨47031704291479358834154983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31354469527652905889436655 47031704291479358834154983)
        ·
          refine ⟨70547556437219038251232475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47031704291479358834154983 70547556437219038251232475)
          ·
            refine ⟨105821334655828557376848713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70547556437219038251232475 105821334655828557376848713)
            ·
              refine ⟨79366000991871418032636535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105821334655828557376848713 79366000991871418032636535)
              ·
                refine ⟨119049001487807127048954803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79366000991871418032636535 119049001487807127048954803)
                ·
                  refine ⟨178573502231710690573432205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119049001487807127048954803 178573502231710690573432205)
                  ·
                    refine ⟨66965063336891508965037077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 178573502231710690573432205 66965063336891508965037077)
                    ·
                      refine ⟨3138987343916789482736113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66965063336891508965037077 3138987343916789482736113)
                      ·
                        rfl

theorem cell23_6113156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_6113156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113156 prefixEnd_6113156 := by exact prefixLift 6113156
  have htrace : WordTrace (prefixWord ++ tailWord_6113156) baseStart_6113156 baseEnd_6113156 := by
    simpa [prefixWord, tailWord_6113156, baseEnd_6113156] using wordTrace_append hprefix tailTrace_6113156
  have hstable : (prefixWord ++ tailWord_6113156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113156).length < 2 ^ (prefixWord ++ tailWord_6113156).sum := by decide
  have hdescent : baseEnd_6113156 < baseStart_6113156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113160 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 2, 1, 4]
def baseStart_6113160 : Nat := 118140960795 + 6113160 * 2 ^ 59
def prefixEnd_6113160 : Nat := 4983230072969 + 3 ^ 40 * 6113160 * 2
def baseEnd_6113160 : Nat := 3138989397839407467086095

theorem tailTrace_6113160 : CollatzResearch.WordTrace tailWord_6113160 prefixEnd_6113160 3138989397839407467086095 := by
  unfold tailWord_6113160
  simp only [CollatzResearch.WordTrace]
  refine ⟨111482631266536419726236467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148643508355381892968315289 111482631266536419726236467)
  ·
    refine ⟨167223946899804629589354701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111482631266536419726236467 167223946899804629589354701)
    ·
      refine ⟨62708980087426736096008013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167223946899804629589354701 62708980087426736096008013)
      ·
        refine ⟨23515867532785026036003005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62708980087426736096008013 23515867532785026036003005)
        ·
          refine ⟨8818450324794384763501127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23515867532785026036003005 8818450324794384763501127)
          ·
            refine ⟨13227675487191577145251691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8818450324794384763501127 13227675487191577145251691)
            ·
              refine ⟨19841513230787365717877537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13227675487191577145251691 19841513230787365717877537)
              ·
                refine ⟨14881134923090524288408153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19841513230787365717877537 14881134923090524288408153)
                ·
                  refine ⟨11160851192317893216306115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14881134923090524288408153 11160851192317893216306115)
                  ·
                    refine ⟨16741276788476839824459173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11160851192317893216306115 16741276788476839824459173)
                    ·
                      refine ⟨3138989397839407467086095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16741276788476839824459173 3138989397839407467086095)
                      ·
                        rfl

theorem cell23_6113160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_6113160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113160 prefixEnd_6113160 := by exact prefixLift 6113160
  have htrace : WordTrace (prefixWord ++ tailWord_6113160) baseStart_6113160 baseEnd_6113160 := by
    simpa [prefixWord, tailWord_6113160, baseEnd_6113160] using wordTrace_append hprefix tailTrace_6113160
  have hstable : (prefixWord ++ tailWord_6113160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113160).length < 2 ^ (prefixWord ++ tailWord_6113160).sum := by decide
  have hdescent : baseEnd_6113160 < baseStart_6113160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113227 : List Nat := [1, 1, 1, 1, 3, 4, 3, 4, 1, 1, 3]
def baseStart_6113227 : Nat := 118140960795 + 6113227 * 2 ^ 59
def prefixEnd_6113227 : Nat := 4983230072969 + 3 ^ 40 * 6113227 * 2
def baseEnd_6113227 : Nat := 3139023801043258704948287

theorem tailTrace_6113227 : CollatzResearch.WordTrace tailWord_6113227 prefixEnd_6113227 3139023801043258704948287 := by
  unfold tailWord_6113227
  simp only [CollatzResearch.WordTrace]
  refine ⟨222967706223830109895161935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148645137482553406596774623 222967706223830109895161935)
  ·
    refine ⟨334451559335745164842742903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222967706223830109895161935 334451559335745164842742903)
    ·
      refine ⟨501677339003617747264114355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334451559335745164842742903 501677339003617747264114355)
      ·
        refine ⟨752516008505426620896171533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501677339003617747264114355 752516008505426620896171533)
        ·
          refine ⟨282193503189534982836064325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 752516008505426620896171533 282193503189534982836064325)
          ·
            refine ⟨52911281848037809281762061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 282193503189534982836064325 52911281848037809281762061)
            ·
              refine ⟨19841730693014178480660773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52911281848037809281762061 19841730693014178480660773)
              ·
                refine ⟨3720324504940158465123895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19841730693014178480660773 3720324504940158465123895)
                ·
                  refine ⟨5580486757410237697685843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3720324504940158465123895 5580486757410237697685843)
                  ·
                    refine ⟨8370730136115356546528765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5580486757410237697685843 8370730136115356546528765)
                    ·
                      refine ⟨3139023801043258704948287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8370730136115356546528765 3139023801043258704948287)
                      ·
                        rfl

theorem cell23_6113227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 1, 1, 3].length) (baseStart_6113227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113227 prefixEnd_6113227 := by exact prefixLift 6113227
  have htrace : WordTrace (prefixWord ++ tailWord_6113227) baseStart_6113227 baseEnd_6113227 := by
    simpa [prefixWord, tailWord_6113227, baseEnd_6113227] using wordTrace_append hprefix tailTrace_6113227
  have hstable : (prefixWord ++ tailWord_6113227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113227).length < 2 ^ (prefixWord ++ tailWord_6113227).sum := by decide
  have hdescent : baseEnd_6113227 < baseStart_6113227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113263 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 4]
def baseStart_6113263 : Nat := 118140960795 + 6113263 * 2 ^ 59
def prefixEnd_6113263 : Nat := 4983230072969 + 3 ^ 40 * 6113263 * 2
def baseEnd_6113263 : Nat := 3139042286346820564098121

theorem tailTrace_6113263 : CollatzResearch.WordTrace tailWord_6113263 prefixEnd_6113263 3139042286346820564098121 := by
  unfold tailWord_6113263
  simp only [CollatzResearch.WordTrace]
  refine ⟨222969019251699688043472443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148646012834466458695648295 222969019251699688043472443)
  ·
    refine ⟨334453528877549532065208665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222969019251699688043472443 334453528877549532065208665)
    ·
      refine ⟨250840146658162149048906499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334453528877549532065208665 250840146658162149048906499)
      ·
        refine ⟨376260219987243223573359749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250840146658162149048906499 376260219987243223573359749)
        ·
          refine ⟨70548791247608104420004953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 376260219987243223573359749 70548791247608104420004953)
          ·
            refine ⟨52911593435706078315003715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70548791247608104420004953 52911593435706078315003715)
            ·
              refine ⟨79367390153559117472505573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52911593435706078315003715 79367390153559117472505573)
              ·
                refine ⟨14881385653792334526094795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79367390153559117472505573 14881385653792334526094795)
                ·
                  refine ⟨22322078480688501789142193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14881385653792334526094795 22322078480688501789142193)
                  ·
                    refine ⟨16741558860516376341856645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22322078480688501789142193 16741558860516376341856645)
                    ·
                      refine ⟨3139042286346820564098121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16741558860516376341856645 3139042286346820564098121)
                      ·
                        rfl

theorem cell23_6113263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_6113263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113263 prefixEnd_6113263 := by exact prefixLift 6113263
  have htrace : WordTrace (prefixWord ++ tailWord_6113263) baseStart_6113263 baseEnd_6113263 := by
    simpa [prefixWord, tailWord_6113263, baseEnd_6113263] using wordTrace_append hprefix tailTrace_6113263
  have hstable : (prefixWord ++ tailWord_6113263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113263).length < 2 ^ (prefixWord ++ tailWord_6113263).sum := by decide
  have hdescent : baseEnd_6113263 < baseStart_6113263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113283 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 3]
def baseStart_6113283 : Nat := 118140960795 + 6113283 * 2 ^ 59
def prefixEnd_6113283 : Nat := 4983230072969 + 3 ^ 40 * 6113283 * 2
def baseEnd_6113283 : Nat := 3139052555959910485848029

theorem tailTrace_6113283 : CollatzResearch.WordTrace tailWord_6113283 prefixEnd_6113283 3139052555959910485848029 := by
  unfold tailWord_6113283
  simp only [CollatzResearch.WordTrace]
  refine ⟨222969748711627231459200503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148646499141084820972800335 222969748711627231459200503)
  ·
    refine ⟨334454623067440847188800755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222969748711627231459200503 334454623067440847188800755)
    ·
      refine ⟨501681934601161270783201133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334454623067440847188800755 501681934601161270783201133)
      ·
        refine ⟨188130725475435476543700425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 501681934601161270783201133 188130725475435476543700425)
        ·
          refine ⟨141098044106576607407775319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188130725475435476543700425 141098044106576607407775319)
          ·
            refine ⟨211647066159864911111662979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141098044106576607407775319 211647066159864911111662979)
            ·
              refine ⟨317470599239797366667494469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211647066159864911111662979 317470599239797366667494469)
              ·
                refine ⟨59525737357462006250155213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317470599239797366667494469 59525737357462006250155213)
                ·
                  refine ⟨22322151509048252343808205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59525737357462006250155213 22322151509048252343808205)
                  ·
                    refine ⟨8370806815893094628928077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22322151509048252343808205 8370806815893094628928077)
                    ·
                      refine ⟨3139052555959910485848029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8370806815893094628928077 3139052555959910485848029)
                      ·
                        rfl

theorem cell23_6113283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_6113283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113283 prefixEnd_6113283 := by exact prefixLift 6113283
  have htrace : WordTrace (prefixWord ++ tailWord_6113283) baseStart_6113283 baseEnd_6113283 := by
    simpa [prefixWord, tailWord_6113283, baseEnd_6113283] using wordTrace_append hprefix tailTrace_6113283
  have hstable : (prefixWord ++ tailWord_6113283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113283).length < 2 ^ (prefixWord ++ tailWord_6113283).sum := by decide
  have hdescent : baseEnd_6113283 < baseStart_6113283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113333 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 4, 6]
def baseStart_6113333 : Nat := 118140960795 + 6113333 * 2 ^ 59
def prefixEnd_6113333 : Nat := 4983230072969 + 3 ^ 40 * 6113333 * 2
def baseEnd_6113333 : Nat := 1046359409997545096740933

theorem tailTrace_6113333 : CollatzResearch.WordTrace tailWord_6113333 prefixEnd_6113333 1046359409997545096740933 := by
  unfold tailWord_6113333
  simp only [CollatzResearch.WordTrace]
  refine ⟨222971572361446089998520653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148647714907630726665680435 222971572361446089998520653)
  ·
    refine ⟨83614339635542283749445245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222971572361446089998520653 83614339635542283749445245)
    ·
      refine ⟨31355377363328356406041967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83614339635542283749445245 31355377363328356406041967)
      ·
        refine ⟨47033066044992534609062951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31355377363328356406041967 47033066044992534609062951)
        ·
          refine ⟨70549599067488801913594427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47033066044992534609062951 70549599067488801913594427)
          ·
            refine ⟨105824398601233202870391641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70549599067488801913594427 105824398601233202870391641)
            ·
              refine ⟨79368298950924902152793731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105824398601233202870391641 79368298950924902152793731)
              ·
                refine ⟨119052448426387353229190597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79368298950924902152793731 119052448426387353229190597)
                ·
                  refine ⟨22322334079947628730473237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119052448426387353229190597 22322334079947628730473237)
                  ·
                    refine ⟨1046359409997545096740933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22322334079947628730473237 1046359409997545096740933)
                    ·
                      rfl

theorem cell23_6113333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_6113333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113333 prefixEnd_6113333 := by exact prefixLift 6113333
  have htrace : WordTrace (prefixWord ++ tailWord_6113333) baseStart_6113333 baseEnd_6113333 := by
    simpa [prefixWord, tailWord_6113333, baseEnd_6113333] using wordTrace_append hprefix tailTrace_6113333
  have hstable : (prefixWord ++ tailWord_6113333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113333).length < 2 ^ (prefixWord ++ tailWord_6113333).sum := by decide
  have hdescent : baseEnd_6113333 < baseStart_6113333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113334 : List Nat := [5, 1, 2, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_6113334 : Nat := 118140960795 + 6113334 * 2 ^ 59
def prefixEnd_6113334 : Nat := 4983230072969 + 3 ^ 40 * 6113334 * 2
def baseEnd_6113334 : Nat := 3139078743473289786310295

theorem tailTrace_6113334 : CollatzResearch.WordTrace tailWord_6113334 prefixEnd_6113334 3139078743473289786310295 := by
  unfold tailWord_6113334
  simp only [CollatzResearch.WordTrace]
  refine ⟨13935725552152654198081691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148647739222961644779538037 13935725552152654198081691)
  ·
    refine ⟨20903588328228981297122537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13935725552152654198081691 20903588328228981297122537)
    ·
      refine ⟨15677691246171735972841903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20903588328228981297122537 15677691246171735972841903)
      ·
        refine ⟨23516536869257603959262855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15677691246171735972841903 23516536869257603959262855)
        ·
          refine ⟨35274805303886405938894283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23516536869257603959262855 35274805303886405938894283)
          ·
            refine ⟨52912207955829608908341425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35274805303886405938894283 52912207955829608908341425)
            ·
              refine ⟨39684155966872206681256069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52912207955829608908341425 39684155966872206681256069)
              ·
                refine ⟨7440779243788538752735513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39684155966872206681256069 7440779243788538752735513)
                ·
                  refine ⟨5580584432841404064551635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7440779243788538752735513 5580584432841404064551635)
                  ·
                    refine ⟨8370876649262106096827453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5580584432841404064551635 8370876649262106096827453)
                    ·
                      refine ⟨3139078743473289786310295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8370876649262106096827453 3139078743473289786310295)
                      ·
                        rfl

theorem cell23_6113334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_6113334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113334 prefixEnd_6113334 := by exact prefixLift 6113334
  have htrace : WordTrace (prefixWord ++ tailWord_6113334) baseStart_6113334 baseEnd_6113334 := by
    simpa [prefixWord, tailWord_6113334, baseEnd_6113334] using wordTrace_append hprefix tailTrace_6113334
  have hstable : (prefixWord ++ tailWord_6113334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113334).length < 2 ^ (prefixWord ++ tailWord_6113334).sum := by decide
  have hdescent : baseEnd_6113334 < baseStart_6113334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113353 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 1, 4, 4]
def baseStart_6113353 : Nat := 118140960795 + 6113353 * 2 ^ 59
def prefixEnd_6113353 : Nat := 4983230072969 + 3 ^ 40 * 6113353 * 2
def baseEnd_6113353 : Nat := 3139088499605725211972707

theorem tailTrace_6113353 : CollatzResearch.WordTrace tailWord_6113353 prefixEnd_6113353 3139088499605725211972707 := by
  unfold tailWord_6113353
  simp only [CollatzResearch.WordTrace]
  refine ⟨222972301821373633414248713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148648201214249088942832475 222972301821373633414248713)
  ·
    refine ⟨167229226366030225060686535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222972301821373633414248713 167229226366030225060686535)
    ·
      refine ⟨250843839549045337591029803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167229226366030225060686535 250843839549045337591029803)
      ·
        refine ⟨376265759323568006386544705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250843839549045337591029803 376265759323568006386544705)
        ·
          refine ⟨282199319492676004789908529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376265759323568006386544705 282199319492676004789908529)
          ·
            refine ⟨211649489619507003592431397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282199319492676004789908529 211649489619507003592431397)
            ·
              refine ⟨39684279303657563173580887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211649489619507003592431397 39684279303657563173580887)
              ·
                refine ⟨59526418955486344760371331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39684279303657563173580887 59526418955486344760371331)
                ·
                  refine ⟨89289628433229517140556997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59526418955486344760371331 89289628433229517140556997)
                  ·
                    refine ⟨16741805331230534463854437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89289628433229517140556997 16741805331230534463854437)
                    ·
                      refine ⟨3139088499605725211972707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16741805331230534463854437 3139088499605725211972707)
                      ·
                        rfl

theorem cell23_6113353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_6113353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113353 prefixEnd_6113353 := by exact prefixLift 6113353
  have htrace : WordTrace (prefixWord ++ tailWord_6113353) baseStart_6113353 baseEnd_6113353 := by
    simpa [prefixWord, tailWord_6113353, baseEnd_6113353] using wordTrace_append hprefix tailTrace_6113353
  have hstable : (prefixWord ++ tailWord_6113353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113353).length < 2 ^ (prefixWord ++ tailWord_6113353).sum := by decide
  have hdescent : baseEnd_6113353 < baseStart_6113353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113378 : List Nat := [3, 3, 2, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_6113378 : Nat := 118140960795 + 6113378 * 2 ^ 59
def prefixEnd_6113378 : Nat := 4983230072969 + 3 ^ 40 * 6113378 * 2
def baseEnd_6113378 : Nat := 3139101336622087614160093

theorem tailTrace_6113378 : CollatzResearch.WordTrace tailWord_6113378 prefixEnd_6113378 3139101336622087614160093 := by
  unfold tailWord_6113378
  simp only [CollatzResearch.WordTrace]
  refine ⟨55743303411570765670977197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148648809097522041789272525 55743303411570765670977197)
  ·
    refine ⟨20903738779339037126616449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55743303411570765670977197 20903738779339037126616449)
    ·
      refine ⟨15677804084504277844962337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20903738779339037126616449 15677804084504277844962337)
      ·
        refine ⟨11758353063378208383721753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15677804084504277844962337 11758353063378208383721753)
        ·
          refine ⟨8818764797533656287791315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11758353063378208383721753 8818764797533656287791315)
          ·
            refine ⟨13228147196300484431686973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8818764797533656287791315 13228147196300484431686973)
            ·
              refine ⟨4960555198612681661882615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13228147196300484431686973 4960555198612681661882615)
              ·
                refine ⟨7440832797919022492823923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4960555198612681661882615 7440832797919022492823923)
                ·
                  refine ⟨11161249196878533739235885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7440832797919022492823923 11161249196878533739235885)
                  ·
                    refine ⟨4185468448829450152213457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11161249196878533739235885 4185468448829450152213457)
                    ·
                      refine ⟨3139101336622087614160093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4185468448829450152213457 3139101336622087614160093)
                      ·
                        rfl

theorem cell23_6113378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_6113378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113378 prefixEnd_6113378 := by exact prefixLift 6113378
  have htrace : WordTrace (prefixWord ++ tailWord_6113378) baseStart_6113378 baseEnd_6113378 := by
    simpa [prefixWord, tailWord_6113378, baseEnd_6113378] using wordTrace_append hprefix tailTrace_6113378
  have hstable : (prefixWord ++ tailWord_6113378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113378).length < 2 ^ (prefixWord ++ tailWord_6113378).sum := by decide
  have hdescent : baseEnd_6113378 < baseStart_6113378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113480 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 1, 7, 3]
def baseStart_6113480 : Nat := 118140960795 + 6113480 * 2 ^ 59
def prefixEnd_6113480 : Nat := 4983230072969 + 3 ^ 40 * 6113480 * 2
def baseEnd_6113480 : Nat := 3139153711648846215084623

theorem tailTrace_6113480 : CollatzResearch.WordTrace tailWord_6113480 prefixEnd_6113480 3139153711648846215084623 := by
  unfold tailWord_6113480
  simp only [CollatzResearch.WordTrace]
  refine ⟨111488466945956767052060947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148651289261275689402747929 111488466945956767052060947)
  ·
    refine ⟨167232700418935150578091421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111488466945956767052060947 167232700418935150578091421)
    ·
      refine ⟨62712262657100681466784283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167232700418935150578091421 62712262657100681466784283)
      ·
        refine ⟨94068393985651022200176425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62712262657100681466784283 94068393985651022200176425)
        ·
          refine ⟨70551295489238266650132319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94068393985651022200176425 70551295489238266650132319)
          ·
            refine ⟨105826943233857399975198479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70551295489238266650132319 105826943233857399975198479)
            ·
              refine ⟨158740414850786099962797719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105826943233857399975198479 158740414850786099962797719)
              ·
                refine ⟨238110622276179149944196579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158740414850786099962797719 238110622276179149944196579)
                ·
                  refine ⟨357165933414268724916294869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238110622276179149944196579 357165933414268724916294869)
                  ·
                    refine ⟨8371076564396923240225661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 357165933414268724916294869 8371076564396923240225661)
                    ·
                      refine ⟨3139153711648846215084623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8371076564396923240225661 3139153711648846215084623)
                      ·
                        rfl

theorem cell23_6113480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_6113480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113480 prefixEnd_6113480 := by exact prefixLift 6113480
  have htrace : WordTrace (prefixWord ++ tailWord_6113480) baseStart_6113480 baseEnd_6113480 := by
    simpa [prefixWord, tailWord_6113480, baseEnd_6113480] using wordTrace_append hprefix tailTrace_6113480
  have hstable : (prefixWord ++ tailWord_6113480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113480).length < 2 ^ (prefixWord ++ tailWord_6113480).sum := by decide
  have hdescent : baseEnd_6113480 < baseStart_6113480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113497 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 5, 1, 3]
def baseStart_6113497 : Nat := 118140960795 + 6113497 * 2 ^ 59
def prefixEnd_6113497 : Nat := 4983230072969 + 3 ^ 40 * 6113497 * 2
def baseEnd_6113497 : Nat := 3139162440819972648572045

theorem tailTrace_6113497 : CollatzResearch.WordTrace tailWord_6113497 prefixEnd_6113497 3139162440819972648572045 := by
  unfold tailWord_6113497
  simp only [CollatzResearch.WordTrace]
  refine ⟨222977553932851946007490745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148651702621901297338327163 222977553932851946007490745)
  ·
    refine ⟨167233165449638959505618059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222977553932851946007490745 167233165449638959505618059)
    ·
      refine ⟨250849748174458439258427089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167233165449638959505618059 250849748174458439258427089)
      ·
        refine ⟨188137311130843829443820317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250849748174458439258427089 188137311130843829443820317)
        ·
          refine ⟨70551491674066436041432619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188137311130843829443820317 70551491674066436041432619)
          ·
            refine ⟨105827237511099654062148929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70551491674066436041432619 105827237511099654062148929)
            ·
              refine ⟨79370428133324740546611697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105827237511099654062148929 79370428133324740546611697)
              ·
                refine ⟨59527821099993555409958773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79370428133324740546611697 59527821099993555409958773)
                ·
                  refine ⟨5580733228124395819683635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59527821099993555409958773 5580733228124395819683635)
                  ·
                    refine ⟨8371099842186593729525453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5580733228124395819683635 8371099842186593729525453)
                    ·
                      refine ⟨3139162440819972648572045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8371099842186593729525453 3139162440819972648572045)
                      ·
                        rfl

theorem cell23_6113497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_6113497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113497 prefixEnd_6113497 := by exact prefixLift 6113497
  have htrace : WordTrace (prefixWord ++ tailWord_6113497) baseStart_6113497 baseEnd_6113497 := by
    simpa [prefixWord, tailWord_6113497, baseEnd_6113497] using wordTrace_append hprefix tailTrace_6113497
  have hstable : (prefixWord ++ tailWord_6113497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113497).length < 2 ^ (prefixWord ++ tailWord_6113497).sum := by decide
  have hdescent : baseEnd_6113497 < baseStart_6113497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113537 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_6113537 : Nat := 118140960795 + 6113537 * 2 ^ 59
def prefixEnd_6113537 : Nat := 4983230072969 + 3 ^ 40 * 6113537 * 2
def baseEnd_6113537 : Nat := 3139182980046152492071861

theorem tailTrace_6113537 : CollatzResearch.WordTrace tailWord_6113537 prefixEnd_6113537 3139182980046152492071861 := by
  unfold tailWord_6113537
  simp only [CollatzResearch.WordTrace]
  refine ⟨222979012852707032838946865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148652675235138021892631243 222979012852707032838946865)
  ·
    refine ⟨167234259639530274629210149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222979012852707032838946865 167234259639530274629210149)
    ·
      refine ⟨31356423682411926492976903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167234259639530274629210149 31356423682411926492976903)
      ·
        refine ⟨47034635523617889739465355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31356423682411926492976903 47034635523617889739465355)
        ·
          refine ⟨70551953285426834609198033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47034635523617889739465355 70551953285426834609198033)
          ·
            refine ⟨52913964964070125956898525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70551953285426834609198033 52913964964070125956898525)
            ·
              refine ⟨19842736861526297233836947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52913964964070125956898525 19842736861526297233836947)
              ·
                refine ⟨29764105292289445850755421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19842736861526297233836947 29764105292289445850755421)
                ·
                  refine ⟨11161539484608542194033283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29764105292289445850755421 11161539484608542194033283)
                  ·
                    refine ⟨16742309226912813291049925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11161539484608542194033283 16742309226912813291049925)
                    ·
                      refine ⟨3139182980046152492071861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16742309226912813291049925 3139182980046152492071861)
                      ·
                        rfl

theorem cell23_6113537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_6113537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113537 prefixEnd_6113537 := by exact prefixLift 6113537
  have htrace : WordTrace (prefixWord ++ tailWord_6113537) baseStart_6113537 baseEnd_6113537 := by
    simpa [prefixWord, tailWord_6113537, baseEnd_6113537] using wordTrace_append hprefix tailTrace_6113537
  have hstable : (prefixWord ++ tailWord_6113537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113537).length < 2 ^ (prefixWord ++ tailWord_6113537).sum := by decide
  have hdescent : baseEnd_6113537 < baseStart_6113537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113557 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 1, 1, 5]
def baseStart_6113557 : Nat := 118140960795 + 6113557 * 2 ^ 59
def prefixEnd_6113557 : Nat := 4983230072969 + 3 ^ 40 * 6113557 * 2
def baseEnd_6113557 : Nat := 3139193249659242413821769

theorem tailTrace_6113557 : CollatzResearch.WordTrace tailWord_6113557 prefixEnd_6113557 3139193249659242413821769 := by
  unfold tailWord_6113557
  simp only [CollatzResearch.WordTrace]
  refine ⟨222979742312634576254674925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148653161541756384169783283 222979742312634576254674925)
  ·
    refine ⟨83617403367237966095503097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222979742312634576254674925 83617403367237966095503097)
    ·
      refine ⟨62713052525428474571627323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83617403367237966095503097 62713052525428474571627323)
      ·
        refine ⟨94069578788142711857440985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62713052525428474571627323 94069578788142711857440985)
        ·
          refine ⟨70552184091107033893080739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94069578788142711857440985 70552184091107033893080739)
          ·
            refine ⟨105828276136660550839621109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70552184091107033893080739 105828276136660550839621109)
            ·
              refine ⟨9921400887811926641214479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105828276136660550839621109 9921400887811926641214479)
              ·
                refine ⟨14882101331717889961821719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9921400887811926641214479 14882101331717889961821719)
                ·
                  refine ⟨22323151997576834942732579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14882101331717889961821719 22323151997576834942732579)
                  ·
                    refine ⟨33484727996365252414098869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22323151997576834942732579 33484727996365252414098869)
                    ·
                      refine ⟨3139193249659242413821769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33484727996365252414098869 3139193249659242413821769)
                      ·
                        rfl

theorem cell23_6113557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_6113557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113557 prefixEnd_6113557 := by exact prefixLift 6113557
  have htrace : WordTrace (prefixWord ++ tailWord_6113557) baseStart_6113557 baseEnd_6113557 := by
    simpa [prefixWord, tailWord_6113557, baseEnd_6113557] using wordTrace_append hprefix tailTrace_6113557
  have hstable : (prefixWord ++ tailWord_6113557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113557).length < 2 ^ (prefixWord ++ tailWord_6113557).sum := by decide
  have hdescent : baseEnd_6113557 < baseStart_6113557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113580 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 6]
def baseStart_6113580 : Nat := 118140960795 + 6113580 * 2 ^ 59
def prefixEnd_6113580 : Nat := 4983230072969 + 3 ^ 40 * 6113580 * 2
def baseEnd_6113580 : Nat := 3139205059714295823834163

theorem tailTrace_6113580 : CollatzResearch.WordTrace tailWord_6113580 prefixEnd_6113580 3139205059714295823834163 := by
  unfold tailWord_6113580
  simp only [CollatzResearch.WordTrace]
  refine ⟨111490290595775625591381097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148653720794367500788508129 111490290595775625591381097)
  ·
    refine ⟨83617717946831719193535823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111490290595775625591381097 83617717946831719193535823)
    ·
      refine ⟨125426576920247578790303735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83617717946831719193535823 125426576920247578790303735)
      ·
        refine ⟨188139865380371368185455603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125426576920247578790303735 188139865380371368185455603)
        ·
          refine ⟨282209798070557052278183405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188139865380371368185455603 282209798070557052278183405)
          ·
            refine ⟨105828674276458894604318777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282209798070557052278183405 105828674276458894604318777)
            ·
              refine ⟨79371505707344170953239083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105828674276458894604318777 79371505707344170953239083)
              ·
                refine ⟨119057258561016256429858625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79371505707344170953239083 119057258561016256429858625)
                ·
                  refine ⟨89292943920762192322393969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119057258561016256429858625 89292943920762192322393969)
                  ·
                    refine ⟨66969707940571644241795477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89292943920762192322393969 66969707940571644241795477)
                    ·
                      refine ⟨3139205059714295823834163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66969707940571644241795477 3139205059714295823834163)
                      ·
                        rfl

theorem cell23_6113580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_6113580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113580 prefixEnd_6113580 := by exact prefixLift 6113580
  have htrace : WordTrace (prefixWord ++ tailWord_6113580) baseStart_6113580 baseEnd_6113580 := by
    simpa [prefixWord, tailWord_6113580, baseEnd_6113580] using wordTrace_append hprefix tailTrace_6113580
  have hstable : (prefixWord ++ tailWord_6113580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113580).length < 2 ^ (prefixWord ++ tailWord_6113580).sum := by decide
  have hdescent : baseEnd_6113580 < baseStart_6113580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113581 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_6113581 : Nat := 118140960795 + 6113581 * 2 ^ 59
def prefixEnd_6113581 : Nat := 4983230072969 + 3 ^ 40 * 6113581 * 2
def baseEnd_6113581 : Nat := 1046401857731650106640553

theorem tailTrace_6113581 : CollatzResearch.WordTrace tailWord_6113581 prefixEnd_6113581 1046401857731650106640553 := by
  unfold tailWord_6113581
  simp only [CollatzResearch.WordTrace]
  refine ⟨222980617664547628353548597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148653745109698418902365731 222980617664547628353548597)
  ·
    refine ⟨20904432906051340158145181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222980617664547628353548597 20904432906051340158145181)
    ·
      refine ⟨7839162339769252559304443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20904432906051340158145181 7839162339769252559304443)
      ·
        refine ⟨11758743509653878838956665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7839162339769252559304443 11758743509653878838956665)
        ·
          refine ⟨8819057632240409129217499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11758743509653878838956665 8819057632240409129217499)
          ·
            refine ⟨13228586448360613693826249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8819057632240409129217499 13228586448360613693826249)
            ·
              refine ⟨9921439836270460270369687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13228586448360613693826249 9921439836270460270369687)
              ·
                refine ⟨14882159754405690405554531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9921439836270460270369687 14882159754405690405554531)
                ·
                  refine ⟨22323239631608535608331797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14882159754405690405554531 22323239631608535608331797)
                  ·
                    refine ⟨1046401857731650106640553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22323239631608535608331797 1046401857731650106640553)
                    ·
                      rfl

theorem cell23_6113581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_6113581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113581 prefixEnd_6113581 := by exact prefixLift 6113581
  have htrace : WordTrace (prefixWord ++ tailWord_6113581) baseStart_6113581 baseEnd_6113581 := by
    simpa [prefixWord, tailWord_6113581, baseEnd_6113581] using wordTrace_append hprefix tailTrace_6113581
  have hstable : (prefixWord ++ tailWord_6113581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113581).length < 2 ^ (prefixWord ++ tailWord_6113581).sum := by decide
  have hdescent : baseEnd_6113581 < baseStart_6113581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113588 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_6113588 : Nat := 118140960795 + 6113588 * 2 ^ 59
def prefixEnd_6113588 : Nat := 4983230072969 + 3 ^ 40 * 6113588 * 2
def baseEnd_6113588 : Nat := 3139209167559531792534127

theorem tailTrace_6113588 : CollatzResearch.WordTrace tailWord_6113588 prefixEnd_6113588 3139209167559531792534127 := by
  unfold tailWord_6113588
  simp only [CollatzResearch.WordTrace]
  refine ⟨111490436487761134274526709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148653915317014845699368945 111490436487761134274526709)
  ·
    refine ⟨10452228420727606338236879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111490436487761134274526709 10452228420727606338236879)
    ·
      refine ⟨15678342631091409507355319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10452228420727606338236879 15678342631091409507355319)
      ·
        refine ⟨23517513946637114261032979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15678342631091409507355319 23517513946637114261032979)
        ·
          refine ⟨35276270919955671391549469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23517513946637114261032979 35276270919955671391549469)
          ·
            refine ⟨13228601594983376771831051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35276270919955671391549469 13228601594983376771831051)
            ·
              refine ⟨19842902392475065157746577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13228601594983376771831051 19842902392475065157746577)
              ·
                refine ⟨14882176794356298868309933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19842902392475065157746577 14882176794356298868309933)
                ·
                  refine ⟨5580816297883612075616225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14882176794356298868309933 5580816297883612075616225)
                  ·
                    refine ⟨4185612223412709056712169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5580816297883612075616225 4185612223412709056712169)
                    ·
                      refine ⟨3139209167559531792534127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4185612223412709056712169 3139209167559531792534127)
                      ·
                        rfl

theorem cell23_6113588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_6113588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113588 prefixEnd_6113588 := by exact prefixLift 6113588
  have htrace : WordTrace (prefixWord ++ tailWord_6113588) baseStart_6113588 baseEnd_6113588 := by
    simpa [prefixWord, tailWord_6113588, baseEnd_6113588] using wordTrace_append hprefix tailTrace_6113588
  have hstable : (prefixWord ++ tailWord_6113588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113588).length < 2 ^ (prefixWord ++ tailWord_6113588).sum := by decide
  have hdescent : baseEnd_6113588 < baseStart_6113588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113614 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2]
def baseStart_6113614 : Nat := 118140960795 + 6113614 * 2 ^ 59
def prefixEnd_6113614 : Nat := 4983230072969 + 3 ^ 40 * 6113614 * 2
def baseEnd_6113614 : Nat := 3139222518056548690809007

theorem tailTrace_6113614 : CollatzResearch.WordTrace tailWord_6113614 prefixEnd_6113614 3139222518056548690809007 := by
  unfold tailWord_6113614
  simp only [CollatzResearch.WordTrace]
  refine ⟨27872727659178509373687487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148654547515618716659666597 27872727659178509373687487)
  ·
    refine ⟨41809091488767764060531231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27872727659178509373687487 41809091488767764060531231)
    ·
      refine ⟨62713637233151646090796847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41809091488767764060531231 62713637233151646090796847)
      ·
        refine ⟨94070455849727469136195271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62713637233151646090796847 94070455849727469136195271)
        ·
          refine ⟨141105683774591203704292907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94070455849727469136195271 141105683774591203704292907)
          ·
            refine ⟨211658525661886805556439361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141105683774591203704292907 211658525661886805556439361)
            ·
              refine ⟨158743894246415104167329521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211658525661886805556439361 158743894246415104167329521)
              ·
                refine ⟨119057920684811328125497141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158743894246415104167329521 119057920684811328125497141)
                ·
                  refine ⟨11161680064201062011765357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119057920684811328125497141 11161680064201062011765357)
                  ·
                    refine ⟨4185630024075398254412009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11161680064201062011765357 4185630024075398254412009)
                    ·
                      refine ⟨3139222518056548690809007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4185630024075398254412009 3139222518056548690809007)
                      ·
                        rfl

theorem cell23_6113614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_6113614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113614 prefixEnd_6113614 := by exact prefixLift 6113614
  have htrace : WordTrace (prefixWord ++ tailWord_6113614) baseStart_6113614 baseEnd_6113614 := by
    simpa [prefixWord, tailWord_6113614, baseEnd_6113614] using wordTrace_append hprefix tailTrace_6113614
  have hstable : (prefixWord ++ tailWord_6113614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113614).length < 2 ^ (prefixWord ++ tailWord_6113614).sum := by decide
  have hdescent : baseEnd_6113614 < baseStart_6113614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113621 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 4, 1, 3]
def baseStart_6113621 : Nat := 118140960795 + 6113621 * 2 ^ 59
def prefixEnd_6113621 : Nat := 4983230072969 + 3 ^ 40 * 6113621 * 2
def baseEnd_6113621 : Nat := 3139226112421130163421475

theorem tailTrace_6113621 : CollatzResearch.WordTrace tailWord_6113621 prefixEnd_6113621 3139226112421130163421475 := by
  unfold tailWord_6113621
  simp only [CollatzResearch.WordTrace]
  refine ⟨222982076584402715185004717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148654717722935143456669811 222982076584402715185004717)
  ·
    refine ⟨83618278719151018194376769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222982076584402715185004717 83618278719151018194376769)
    ·
      refine ⟨62713709039363263645782577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83618278719151018194376769 62713709039363263645782577)
      ·
        refine ⟨47035281779522447734336933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62713709039363263645782577 47035281779522447734336933)
        ·
          refine ⟨8819115333660458950188175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47035281779522447734336933 8819115333660458950188175)
          ·
            refine ⟨13228673000490688425282263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8819115333660458950188175 13228673000490688425282263)
            ·
              refine ⟨19843009500736032637923395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13228673000490688425282263 19843009500736032637923395)
              ·
                refine ⟨29764514251104048956885093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19843009500736032637923395 29764514251104048956885093)
                ·
                  refine ⟨5580846422082009179415955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29764514251104048956885093 5580846422082009179415955)
                  ·
                    refine ⟨8371269633123013769123933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5580846422082009179415955 8371269633123013769123933)
                    ·
                      refine ⟨3139226112421130163421475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8371269633123013769123933 3139226112421130163421475)
                      ·
                        rfl

theorem cell23_6113621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_6113621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113621 prefixEnd_6113621 := by exact prefixLift 6113621
  have htrace : WordTrace (prefixWord ++ tailWord_6113621) baseStart_6113621 baseEnd_6113621 := by
    simpa [prefixWord, tailWord_6113621, baseEnd_6113621] using wordTrace_append hprefix tailTrace_6113621
  have hstable : (prefixWord ++ tailWord_6113621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113621).length < 2 ^ (prefixWord ++ tailWord_6113621).sum := by decide
  have hdescent : baseEnd_6113621 < baseStart_6113621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113637 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 2, 6]
def baseStart_6113637 : Nat := 118140960795 + 6113637 * 2 ^ 59
def prefixEnd_6113637 : Nat := 4983230072969 + 3 ^ 40 * 6113637 * 2
def baseEnd_6113637 : Nat := 1046411442703867366940467

theorem tailTrace_6113637 : CollatzResearch.WordTrace tailWord_6113637 prefixEnd_6113637 1046411442703867366940467 := by
  unfold tailWord_6113637
  simp only [CollatzResearch.WordTrace]
  refine ⟨222982660152344749917587165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148655106768229833278391443 222982660152344749917587165)
  ·
    refine ⟨83618497557129281219095187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222982660152344749917587165 83618497557129281219095187)
    ·
      refine ⟨125427746335693921828642781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83618497557129281219095187 125427746335693921828642781)
      ·
        refine ⟨47035404875885220685741043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125427746335693921828642781 47035404875885220685741043)
        ·
          refine ⟨70553107313827831028611565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47035404875885220685741043 70553107313827831028611565)
          ·
            refine ⟨26457415242685436635729337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70553107313827831028611565 26457415242685436635729337)
            ·
              refine ⟨19843061432014077476797003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26457415242685436635729337 19843061432014077476797003)
              ·
                refine ⟨29764592148021116215195505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19843061432014077476797003 29764592148021116215195505)
                ·
                  refine ⟨22323444111015837161396629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29764592148021116215195505 22323444111015837161396629)
                  ·
                    refine ⟨1046411442703867366940467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22323444111015837161396629 1046411442703867366940467)
                    ·
                      rfl

theorem cell23_6113637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_6113637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113637 prefixEnd_6113637 := by exact prefixLift 6113637
  have htrace : WordTrace (prefixWord ++ tailWord_6113637) baseStart_6113637 baseEnd_6113637 := by
    simpa [prefixWord, tailWord_6113637, baseEnd_6113637] using wordTrace_append hprefix tailTrace_6113637
  have hstable : (prefixWord ++ tailWord_6113637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113637).length < 2 ^ (prefixWord ++ tailWord_6113637).sum := by decide
  have hdescent : baseEnd_6113637 < baseStart_6113637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113661 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 4, 2, 2]
def baseStart_6113661 : Nat := 118140960795 + 6113661 * 2 ^ 59
def prefixEnd_6113661 : Nat := 4983230072969 + 3 ^ 40 * 6113661 * 2
def baseEnd_6113661 : Nat := 3139246651647310006921291

theorem tailTrace_6113661 : CollatzResearch.WordTrace tailWord_6113661 prefixEnd_6113661 3139246651647310006921291 := by
  unfold tailWord_6113661
  simp only [CollatzResearch.WordTrace]
  refine ⟨222983535504257802016460837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148655690336171868010973891 222983535504257802016460837)
  ·
    refine ⟨41809412907048337878086407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222983535504257802016460837 41809412907048337878086407)
    ·
      refine ⟨62714119360572506817129611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41809412907048337878086407 62714119360572506817129611)
      ·
        refine ⟨94071179040858760225694417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62714119360572506817129611 94071179040858760225694417)
        ·
          refine ⟨70553384280644070169270813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94071179040858760225694417 70553384280644070169270813)
          ·
            refine ⟨26457519105241526313476555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70553384280644070169270813 26457519105241526313476555)
            ·
              refine ⟨39686278657862289470214833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26457519105241526313476555 39686278657862289470214833)
              ·
                refine ⟨29764708993396717102661125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39686278657862289470214833 29764708993396717102661125)
                ·
                  refine ⟨5580882936261884456748961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29764708993396717102661125 5580882936261884456748961)
                  ·
                    refine ⟨4185662202196413342561721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5580882936261884456748961 4185662202196413342561721)
                    ·
                      refine ⟨3139246651647310006921291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4185662202196413342561721 3139246651647310006921291)
                      ·
                        rfl

theorem cell23_6113661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_6113661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113661 prefixEnd_6113661 := by exact prefixLift 6113661
  have htrace : WordTrace (prefixWord ++ tailWord_6113661) baseStart_6113661 baseEnd_6113661 := by
    simpa [prefixWord, tailWord_6113661, baseEnd_6113661] using wordTrace_append hprefix tailTrace_6113661
  have hstable : (prefixWord ++ tailWord_6113661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113661).length < 2 ^ (prefixWord ++ tailWord_6113661).sum := by decide
  have hdescent : baseEnd_6113661 < baseStart_6113661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113678 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2]
def baseStart_6113678 : Nat := 118140960795 + 6113678 * 2 ^ 59
def prefixEnd_6113678 : Nat := 4983230072969 + 3 ^ 40 * 6113678 * 2
def baseEnd_6113678 : Nat := 3139255380818436440408713

theorem tailTrace_6113678 : CollatzResearch.WordTrace tailWord_6113678 prefixEnd_6113678 3139255380818436440408713 := by
  unfold tailWord_6113678
  simp only [CollatzResearch.WordTrace]
  refine ⟨27873019443149526739978711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148656103696797475946553125 27873019443149526739978711)
  ·
    refine ⟨41809529164724290109968067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27873019443149526739978711 41809529164724290109968067)
    ·
      refine ⟨62714293747086435164952101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41809529164724290109968067 62714293747086435164952101)
      ·
        refine ⟨11758930077578706593428519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62714293747086435164952101 11758930077578706593428519)
        ·
          refine ⟨17638395116368059890142779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11758930077578706593428519 17638395116368059890142779)
          ·
            refine ⟨26457592674552089835214169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17638395116368059890142779 26457592674552089835214169)
            ·
              refine ⟨19843194505914067376410627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26457592674552089835214169 19843194505914067376410627)
              ·
                refine ⟨29764791758871101064615941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19843194505914067376410627 29764791758871101064615941)
                ·
                  refine ⟨5580898454788331449615489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29764791758871101064615941 5580898454788331449615489)
                  ·
                    refine ⟨4185673841091248587211617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5580898454788331449615489 4185673841091248587211617)
                    ·
                      refine ⟨3139255380818436440408713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4185673841091248587211617 3139255380818436440408713)
                      ·
                        rfl

theorem cell23_6113678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_6113678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113678 prefixEnd_6113678 := by exact prefixLift 6113678
  have htrace : WordTrace (prefixWord ++ tailWord_6113678) baseStart_6113678 baseEnd_6113678 := by
    simpa [prefixWord, tailWord_6113678, baseEnd_6113678] using wordTrace_append hprefix tailTrace_6113678
  have hstable : (prefixWord ++ tailWord_6113678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113678).length < 2 ^ (prefixWord ++ tailWord_6113678).sum := by decide
  have hdescent : baseEnd_6113678 < baseStart_6113678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113714 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 2, 5]
def baseStart_6113714 : Nat := 118140960795 + 6113714 * 2 ^ 59
def prefixEnd_6113714 : Nat := 4983230072969 + 3 ^ 40 * 6113714 * 2
def baseEnd_6113714 : Nat := 1046424622040666099852849

theorem tailTrace_6113714 : CollatzResearch.WordTrace tailWord_6113714 prefixEnd_6113714 1046424622040666099852849 := by
  unfold tailWord_6113714
  simp only [CollatzResearch.WordTrace]
  refine ⟨55746367143266448017035049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148656979048710528045426797 55746367143266448017035049)
  ·
    refine ⟨41809775357449836012776287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55746367143266448017035049 41809775357449836012776287)
    ·
      refine ⟨62714663036174754019164431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41809775357449836012776287 62714663036174754019164431)
      ·
        refine ⟨94071994554262131028746647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62714663036174754019164431 94071994554262131028746647)
        ·
          refine ⟨141107991831393196543119971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94071994554262131028746647 141107991831393196543119971)
          ·
            refine ⟨211661987747089794814679957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141107991831393196543119971 211661987747089794814679957)
            ·
              refine ⟨9921655675644834131938123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 211661987747089794814679957 9921655675644834131938123)
              ·
                refine ⟨14882483513467251197907185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9921655675644834131938123 14882483513467251197907185)
                ·
                  refine ⟨11161862635100438398430389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14882483513467251197907185 11161862635100438398430389)
                  ·
                    refine ⟨1046424622040666099852849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11161862635100438398430389 1046424622040666099852849)
                    ·
                      rfl

theorem cell23_6113714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_6113714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113714 prefixEnd_6113714 := by exact prefixLift 6113714
  have htrace : WordTrace (prefixWord ++ tailWord_6113714) baseStart_6113714 baseEnd_6113714 := by
    simpa [prefixWord, tailWord_6113714, baseEnd_6113714] using wordTrace_append hprefix tailTrace_6113714
  have hstable : (prefixWord ++ tailWord_6113714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113714).length < 2 ^ (prefixWord ++ tailWord_6113714).sum := by decide
  have hdescent : baseEnd_6113714 < baseStart_6113714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113724 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_6113724 : Nat := 118140960795 + 6113724 * 2 ^ 59
def prefixEnd_6113724 : Nat := 4983230072969 + 3 ^ 40 * 6113724 * 2
def baseEnd_6113724 : Nat := 3139279000928543260433501

theorem tailTrace_6113724 : CollatzResearch.WordTrace tailWord_6113724 prefixEnd_6113724 3139279000928543260433501 := by
  unfold tailWord_6113724
  simp only [CollatzResearch.WordTrace]
  refine ⟨111492916651514781888002113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148657222202019709184002817 111492916651514781888002113)
  ·
    refine ⟨83619687488636086416001585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111492916651514781888002113 83619687488636086416001585)
    ·
      refine ⟨62714765616477064812001189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83619687488636086416001585 62714765616477064812001189)
      ·
        refine ⟨11759018553089449652250223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62714765616477064812001189 11759018553089449652250223)
        ·
          refine ⟨17638527829634174478375335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11759018553089449652250223 17638527829634174478375335)
          ·
            refine ⟨26457791744451261717563003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17638527829634174478375335 26457791744451261717563003)
            ·
              refine ⟨39686687616676892576344505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26457791744451261717563003 39686687616676892576344505)
              ·
                refine ⟨29765015712507669432258379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39686687616676892576344505 29765015712507669432258379)
                ·
                  refine ⟨44647523568761504148387569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29765015712507669432258379 44647523568761504148387569)
                  ·
                    refine ⟨33485642676571128111290677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44647523568761504148387569 33485642676571128111290677)
                    ·
                      refine ⟨3139279000928543260433501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33485642676571128111290677 3139279000928543260433501)
                      ·
                        rfl

theorem cell23_6113724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_6113724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113724 prefixEnd_6113724 := by exact prefixLift 6113724
  have htrace : WordTrace (prefixWord ++ tailWord_6113724) baseStart_6113724 baseEnd_6113724 := by
    simpa [prefixWord, tailWord_6113724, baseEnd_6113724] using wordTrace_append hprefix tailTrace_6113724
  have hstable : (prefixWord ++ tailWord_6113724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113724).length < 2 ^ (prefixWord ++ tailWord_6113724).sum := by decide
  have hdescent : baseEnd_6113724 < baseStart_6113724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113729 : List Nat := [1, 2, 7, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_6113729 : Nat := 118140960795 + 6113729 * 2 ^ 59
def prefixEnd_6113729 : Nat := 4983230072969 + 3 ^ 40 * 6113729 * 2
def baseEnd_6113729 : Nat := 3139281568331815740870979

theorem tailTrace_6113729 : CollatzResearch.WordTrace tailWord_6113729 prefixEnd_6113729 3139281568331815740870979 := by
  unfold tailWord_6113729
  simp only [CollatzResearch.WordTrace]
  refine ⟨222986015668011449629936241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148657343778674299753290827 222986015668011449629936241)
  ·
    refine ⟨167239511751008587222452181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222986015668011449629936241 167239511751008587222452181)
    ·
      refine ⟨3919676056664263763026223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 167239511751008587222452181 3919676056664263763026223)
      ·
        refine ⟨5879514084996395644539335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3919676056664263763026223 5879514084996395644539335)
        ·
          refine ⟨8819271127494593466809003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5879514084996395644539335 8819271127494593466809003)
          ·
            refine ⟨13228906691241890200213505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8819271127494593466809003 13228906691241890200213505)
            ·
              refine ⟨9921680018431417650160129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13228906691241890200213505 9921680018431417650160129)
              ·
                refine ⟨7441260013823563237620097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9921680018431417650160129 7441260013823563237620097)
                ·
                  refine ⟨5580945010367672428215073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7441260013823563237620097 5580945010367672428215073)
                  ·
                    refine ⟨4185708757775754321161305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5580945010367672428215073 4185708757775754321161305)
                    ·
                      refine ⟨3139281568331815740870979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4185708757775754321161305 3139281568331815740870979)
                      ·
                        rfl

theorem cell23_6113729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_6113729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113729 prefixEnd_6113729 := by exact prefixLift 6113729
  have htrace : WordTrace (prefixWord ++ tailWord_6113729) baseStart_6113729 baseEnd_6113729 := by
    simpa [prefixWord, tailWord_6113729, baseEnd_6113729] using wordTrace_append hprefix tailTrace_6113729
  have hstable : (prefixWord ++ tailWord_6113729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113729).length < 2 ^ (prefixWord ++ tailWord_6113729).sum := by decide
  have hdescent : baseEnd_6113729 < baseStart_6113729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113754 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3]
def baseStart_6113754 : Nat := 118140960795 + 6113754 * 2 ^ 59
def prefixEnd_6113754 : Nat := 4983230072969 + 3 ^ 40 * 6113754 * 2
def baseEnd_6113754 : Nat := 3139294405348178143058363

theorem tailTrace_6113754 : CollatzResearch.WordTrace tailWord_6113754 prefixEnd_6113754 3139294405348178143058363 := by
  unfold tailWord_6113754
  simp only [CollatzResearch.WordTrace]
  refine ⟨55746731873230219724899079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148657951661947252599730877 55746731873230219724899079)
  ·
    refine ⟨83620097809845329587348619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55746731873230219724899079 83620097809845329587348619)
    ·
      refine ⟨125430146714767994381022929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83620097809845329587348619 125430146714767994381022929)
      ·
        refine ⟨94072610036075995785767197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125430146714767994381022929 94072610036075995785767197)
        ·
          refine ⟨35277228763528498419662699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94072610036075995785767197 35277228763528498419662699)
          ·
            refine ⟨52915843145292747629494049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35277228763528498419662699 52915843145292747629494049)
            ·
              refine ⟨39686882358969560722120537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52915843145292747629494049 39686882358969560722120537)
              ·
                refine ⟨29765161769227170541590403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39686882358969560722120537 29765161769227170541590403)
                ·
                  refine ⟨44647742653840755812385605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29765161769227170541590403 44647742653840755812385605)
                  ·
                    refine ⟨8371451747595141714822301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44647742653840755812385605 8371451747595141714822301)
                    ·
                      refine ⟨3139294405348178143058363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8371451747595141714822301 3139294405348178143058363)
                      ·
                        rfl

theorem cell23_6113754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_6113754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113754 prefixEnd_6113754 := by exact prefixLift 6113754
  have htrace : WordTrace (prefixWord ++ tailWord_6113754) baseStart_6113754 baseEnd_6113754 := by
    simpa [prefixWord, tailWord_6113754, baseEnd_6113754] using wordTrace_append hprefix tailTrace_6113754
  have hstable : (prefixWord ++ tailWord_6113754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113754).length < 2 ^ (prefixWord ++ tailWord_6113754).sum := by decide
  have hdescent : baseEnd_6113754 < baseStart_6113754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113821 : List Nat := [1, 4, 2, 2, 1, 2, 1, 4, 1, 5]
def baseStart_6113821 : Nat := 118140960795 + 6113821 * 2 ^ 59
def prefixEnd_6113821 : Nat := 4983230072969 + 3 ^ 40 * 6113821 * 2
def baseEnd_6113821 : Nat := 1046442936184009793640185

theorem tailTrace_6113821 : CollatzResearch.WordTrace tailWord_6113821 prefixEnd_6113821 1046442936184009793640185 := by
  unfold tailWord_6113821
  simp only [CollatzResearch.WordTrace]
  refine ⟨222989371183678149342285317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148659580789118766228190211 222989371183678149342285317)
  ·
    refine ⟨41810507096939653001678497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222989371183678149342285317 41810507096939653001678497)
    ·
      refine ⟨31357880322704739751258873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41810507096939653001678497 31357880322704739751258873)
      ·
        refine ⟨23518410242028554813444155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31357880322704739751258873 23518410242028554813444155)
        ·
          refine ⟨35277615363042832220166233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23518410242028554813444155 35277615363042832220166233)
          ·
            refine ⟨26458211522282124165124675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35277615363042832220166233 26458211522282124165124675)
            ·
              refine ⟨39687317283423186247687013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26458211522282124165124675 39687317283423186247687013)
              ·
                refine ⟨7441371990641847421441315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39687317283423186247687013 7441371990641847421441315)
                ·
                  refine ⟨11162057985962771132161973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7441371990641847421441315 11162057985962771132161973)
                  ·
                    refine ⟨1046442936184009793640185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11162057985962771132161973 1046442936184009793640185)
                    ·
                      rfl

theorem cell23_6113821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_6113821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113821 prefixEnd_6113821 := by exact prefixLift 6113821
  have htrace : WordTrace (prefixWord ++ tailWord_6113821) baseStart_6113821 baseEnd_6113821 := by
    simpa [prefixWord, tailWord_6113821, baseEnd_6113821] using wordTrace_append hprefix tailTrace_6113821
  have hstable : (prefixWord ++ tailWord_6113821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113821).length < 2 ^ (prefixWord ++ tailWord_6113821).sum := by decide
  have hdescent : baseEnd_6113821 < baseStart_6113821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113841 : List Nat := [1, 2, 2, 3, 1, 1, 4, 3, 1, 1, 4]
def baseStart_6113841 : Nat := 118140960795 + 6113841 * 2 ^ 59
def prefixEnd_6113841 : Nat := 4983230072969 + 3 ^ 40 * 6113841 * 2
def baseEnd_6113841 : Nat := 3139339078165119302670463

theorem tailTrace_6113841 : CollatzResearch.WordTrace tailWord_6113841 prefixEnd_6113841 3139339078165119302670463 := by
  unfold tailWord_6113841
  simp only [CollatzResearch.WordTrace]
  refine ⟨222990100643605692758013377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148660067095737128505342251 222990100643605692758013377)
  ·
    refine ⟨167242575482704269568510033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222990100643605692758013377 167242575482704269568510033)
    ·
      refine ⟨125431931612028202176382525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167242575482704269568510033 125431931612028202176382525)
      ·
        refine ⟨47036974354510575816143447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125431931612028202176382525 47036974354510575816143447)
        ·
          refine ⟨70555461531765863724215171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47036974354510575816143447 70555461531765863724215171)
          ·
            refine ⟨105833192297648795586322757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70555461531765863724215171 105833192297648795586322757)
            ·
              refine ⟨19843723555809149172435517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105833192297648795586322757 19843723555809149172435517)
              ·
                refine ⟨7441396333428430939663319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19843723555809149172435517 7441396333428430939663319)
                ·
                  refine ⟨11162094500142646409494979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7441396333428430939663319 11162094500142646409494979)
                  ·
                    refine ⟨16743141750213969614242469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11162094500142646409494979 16743141750213969614242469)
                    ·
                      refine ⟨3139339078165119302670463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16743141750213969614242469 3139339078165119302670463)
                      ·
                        rfl

theorem cell23_6113841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_6113841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113841 prefixEnd_6113841 := by exact prefixLift 6113841
  have htrace : WordTrace (prefixWord ++ tailWord_6113841) baseStart_6113841 baseEnd_6113841 := by
    simpa [prefixWord, tailWord_6113841, baseEnd_6113841] using wordTrace_append hprefix tailTrace_6113841
  have hstable : (prefixWord ++ tailWord_6113841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113841).length < 2 ^ (prefixWord ++ tailWord_6113841).sum := by decide
  have hdescent : baseEnd_6113841 < baseStart_6113841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113852 : List Nat := [2, 2, 2, 2, 3, 2, 3, 2, 1, 1, 3]
def baseStart_6113852 : Nat := 118140960795 + 6113852 * 2 ^ 59
def prefixEnd_6113852 : Nat := 4983230072969 + 3 ^ 40 * 6113852 * 2
def baseEnd_6113852 : Nat := 3139344726452318759632913

theorem tailTrace_6113852 : CollatzResearch.WordTrace tailWord_6113852 prefixEnd_6113852 3139344726452318759632913 := by
  unfold tailWord_6113852
  simp only [CollatzResearch.WordTrace]
  refine ⟨111495250923282920818331905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148660334564377227757775873 111495250923282920818331905)
  ·
    refine ⟨83621438192462190613748929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111495250923282920818331905 83621438192462190613748929)
    ·
      refine ⟨62716078644346642960311697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83621438192462190613748929 62716078644346642960311697)
      ·
        refine ⟨47037058983259982220233773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62716078644346642960311697 47037058983259982220233773)
        ·
          refine ⟨17638897118722493332587665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47037058983259982220233773 17638897118722493332587665)
          ·
            refine ⟨13229172839041869999440749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17638897118722493332587665 13229172839041869999440749)
            ·
              refine ⟨4960939814640701249790281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13229172839041869999440749 4960939814640701249790281)
              ·
                refine ⟨3720704860980525937342711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4960939814640701249790281 3720704860980525937342711)
                ·
                  refine ⟨5581057291470788906014067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3720704860980525937342711 5581057291470788906014067)
                  ·
                    refine ⟨8371585937206183359021101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5581057291470788906014067 8371585937206183359021101)
                    ·
                      refine ⟨3139344726452318759632913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8371585937206183359021101 3139344726452318759632913)
                      ·
                        rfl

theorem cell23_6113852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_6113852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113852 prefixEnd_6113852 := by exact prefixLift 6113852
  have htrace : WordTrace (prefixWord ++ tailWord_6113852) baseStart_6113852 baseEnd_6113852 := by
    simpa [prefixWord, tailWord_6113852, baseEnd_6113852] using wordTrace_append hprefix tailTrace_6113852
  have hstable : (prefixWord ++ tailWord_6113852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113852).length < 2 ^ (prefixWord ++ tailWord_6113852).sum := by decide
  have hdescent : baseEnd_6113852 < baseStart_6113852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113891 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 3]
def baseStart_6113891 : Nat := 118140960795 + 6113891 * 2 ^ 59
def prefixEnd_6113891 : Nat := 4983230072969 + 3 ^ 40 * 6113891 * 2
def baseEnd_6113891 : Nat := 3139364752197844107045233

theorem tailTrace_6113891 : CollatzResearch.WordTrace tailWord_6113891 prefixEnd_6113891 3139364752197844107045233 := by
  unfold tailWord_6113891
  simp only [CollatzResearch.WordTrace]
  refine ⟨222991924293424551297333527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148661282862283034198222351 222991924293424551297333527)
  ·
    refine ⟨334487886440136826946000291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222991924293424551297333527 334487886440136826946000291)
    ·
      refine ⟨501731829660205240419000437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334487886440136826946000291 501731829660205240419000437)
      ·
        refine ⟨47037359030644241289281291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 501731829660205240419000437 47037359030644241289281291)
        ·
          refine ⟨70556038545966361933921937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47037359030644241289281291 70556038545966361933921937)
          ·
            refine ⟨52917028909474771450441453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70556038545966361933921937 52917028909474771450441453)
            ·
              refine ⟨19843885841053039293915545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52917028909474771450441453 19843885841053039293915545)
              ·
                refine ⟨14882914380789779470436659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19843885841053039293915545 14882914380789779470436659)
                ·
                  refine ⟨22324371571184669205654989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14882914380789779470436659 22324371571184669205654989)
                  ·
                    refine ⟨8371639339194250952120621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22324371571184669205654989 8371639339194250952120621)
                    ·
                      refine ⟨3139364752197844107045233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8371639339194250952120621 3139364752197844107045233)
                      ·
                        rfl

theorem cell23_6113891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_6113891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113891 prefixEnd_6113891 := by exact prefixLift 6113891
  have htrace : WordTrace (prefixWord ++ tailWord_6113891) baseStart_6113891 baseEnd_6113891 := by
    simpa [prefixWord, tailWord_6113891, baseEnd_6113891] using wordTrace_append hprefix tailTrace_6113891
  have hstable : (prefixWord ++ tailWord_6113891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113891).length < 2 ^ (prefixWord ++ tailWord_6113891).sum := by decide
  have hdescent : baseEnd_6113891 < baseStart_6113891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113909 : List Nat := [1, 3, 4, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_6113909 : Nat := 118140960795 + 6113909 * 2 ^ 59
def prefixEnd_6113909 : Nat := 4983230072969 + 3 ^ 40 * 6113909 * 2
def baseEnd_6113909 : Nat := 3139373994849625036620151

theorem tailTrace_6113909 : CollatzResearch.WordTrace tailWord_6113909 prefixEnd_6113909 3139373994849625036620151 := by
  unfold tailWord_6113909
  simp only [CollatzResearch.WordTrace]
  refine ⟨222992580807359340371488781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148661720538239560247659187 222992580807359340371488781)
  ·
    refine ⟨83622217802759752639308293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222992580807359340371488781 83622217802759752639308293)
    ·
      refine ⟨15679165838017453619870305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83622217802759752639308293 15679165838017453619870305)
      ·
        refine ⟨11759374378513090214902729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15679165838017453619870305 11759374378513090214902729)
        ·
          refine ⟨8819530783884817661177047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11759374378513090214902729 8819530783884817661177047)
          ·
            refine ⟨13229296175827226491765571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8819530783884817661177047 13229296175827226491765571)
            ·
              refine ⟨19843944263740839737648357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13229296175827226491765571 19843944263740839737648357)
              ·
                refine ⟨3720739549451407450809067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19843944263740839737648357 3720739549451407450809067)
                ·
                  refine ⟨5581109324177111176213601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3720739549451407450809067 5581109324177111176213601)
                  ·
                    refine ⟨4185831993132833382160201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5581109324177111176213601 4185831993132833382160201)
                    ·
                      refine ⟨3139373994849625036620151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4185831993132833382160201 3139373994849625036620151)
                      ·
                        rfl

theorem cell23_6113909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_6113909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113909 prefixEnd_6113909 := by exact prefixLift 6113909
  have htrace : WordTrace (prefixWord ++ tailWord_6113909) baseStart_6113909 baseEnd_6113909 := by
    simpa [prefixWord, tailWord_6113909, baseEnd_6113909] using wordTrace_append hprefix tailTrace_6113909
  have hstable : (prefixWord ++ tailWord_6113909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113909).length < 2 ^ (prefixWord ++ tailWord_6113909).sum := by decide
  have hdescent : baseEnd_6113909 < baseStart_6113909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113959 : List Nat := [1, 1, 6, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_6113959 : Nat := 118140960795 + 6113959 * 2 ^ 59
def prefixEnd_6113959 : Nat := 4983230072969 + 3 ^ 40 * 6113959 * 2
def baseEnd_6113959 : Nat := 3139399668882349840994921

theorem tailTrace_6113959 : CollatzResearch.WordTrace tailWord_6113959 prefixEnd_6113959 3139399668882349840994921 := by
  unfold tailWord_6113959
  simp only [CollatzResearch.WordTrace]
  refine ⟨222994404457178198910808931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148662936304785465940539287 222994404457178198910808931)
  ·
    refine ⟨334491606685767298366213397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222994404457178198910808931 334491606685767298366213397)
    ·
      refine ⟨15679294063395342110916253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 334491606685767298366213397 15679294063395342110916253)
      ·
        refine ⟨5879735273773253291593595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15679294063395342110916253 5879735273773253291593595)
        ·
          refine ⟨8819602910659879937390393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5879735273773253291593595 8819602910659879937390393)
          ·
            refine ⟨6614702182994909953042795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8819602910659879937390393 6614702182994909953042795)
            ·
              refine ⟨9922053274492364929564193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6614702182994909953042795 9922053274492364929564193)
              ·
                refine ⟨7441539955869273697173145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9922053274492364929564193 7441539955869273697173145)
                ·
                  refine ⟨5581154966901955272879859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7441539955869273697173145 5581154966901955272879859)
                  ·
                    refine ⟨8371732450352932909319789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5581154966901955272879859 8371732450352932909319789)
                    ·
                      refine ⟨3139399668882349840994921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8371732450352932909319789 3139399668882349840994921)
                      ·
                        rfl

theorem cell23_6113959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_6113959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113959 prefixEnd_6113959 := by exact prefixLift 6113959
  have htrace : WordTrace (prefixWord ++ tailWord_6113959) baseStart_6113959 baseEnd_6113959 := by
    simpa [prefixWord, tailWord_6113959, baseEnd_6113959] using wordTrace_append hprefix tailTrace_6113959
  have hstable : (prefixWord ++ tailWord_6113959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113959).length < 2 ^ (prefixWord ++ tailWord_6113959).sum := by decide
  have hdescent : baseEnd_6113959 < baseStart_6113959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6113971 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 7]
def baseStart_6113971 : Nat := 118140960795 + 6113971 * 2 ^ 59
def prefixEnd_6113971 : Nat := 4983230072969 + 3 ^ 40 * 6113971 * 2
def baseEnd_6113971 : Nat := 348822870072244866004985

theorem tailTrace_6113971 : CollatzResearch.WordTrace tailWord_6113971 prefixEnd_6113971 348822870072244866004985 := by
  unfold tailWord_6113971
  simp only [CollatzResearch.WordTrace]
  refine ⟨222994842133134724960245767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148663228088756483306830511 222994842133134724960245767)
  ·
    refine ⟨334492263199702087440368651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222994842133134724960245767 334492263199702087440368651)
    ·
      refine ⟨501738394799553131160552977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334492263199702087440368651 501738394799553131160552977)
      ·
        refine ⟨376303796099664848370414733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501738394799553131160552977 376303796099664848370414733)
        ·
          refine ⟨141113923537374318138905525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376303796099664848370414733 141113923537374318138905525)
          ·
            refine ⟨13229430331628842325522393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141113923537374318138905525 13229430331628842325522393)
            ·
              refine ⟨9922072748721631744141795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13229430331628842325522393 9922072748721631744141795)
              ·
                refine ⟨14883109123082447616212693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9922072748721631744141795 14883109123082447616212693)
                ·
                  refine ⟨348822870072244866004985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14883109123082447616212693 348822870072244866004985)
                  ·
                    rfl

theorem cell23_6113971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 7].length) (baseStart_6113971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6113971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6113971 prefixEnd_6113971 := by exact prefixLift 6113971
  have htrace : WordTrace (prefixWord ++ tailWord_6113971) baseStart_6113971 baseEnd_6113971 := by
    simpa [prefixWord, tailWord_6113971, baseEnd_6113971] using wordTrace_append hprefix tailTrace_6113971
  have hstable : (prefixWord ++ tailWord_6113971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6113971).length < 2 ^ (prefixWord ++ tailWord_6113971).sum := by decide
  have hdescent : baseEnd_6113971 < baseStart_6113971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6113971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114001 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 2, 5]
def baseStart_6114001 : Nat := 118140960795 + 6114001 * 2 ^ 59
def prefixEnd_6114001 : Nat := 4983230072969 + 3 ^ 40 * 6114001 * 2
def baseEnd_6114001 : Nat := 1046473745023279558889909

theorem tailTrace_6114001 : CollatzResearch.WordTrace tailWord_6114001 prefixEnd_6114001 1046473745023279558889909 := by
  unfold tailWord_6114001
  simp only [CollatzResearch.WordTrace]
  refine ⟨222995936323026040083837857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148663957548684026722558571 222995936323026040083837857)
  ·
    refine ⟨167246952242269530062878393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222995936323026040083837857 167246952242269530062878393)
    ·
      refine ⟨125435214181702147547158795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167246952242269530062878393 125435214181702147547158795)
      ·
        refine ⟨188152821272553221320738193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125435214181702147547158795 188152821272553221320738193)
        ·
          refine ⟨141114615954414915990553645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188152821272553221320738193 141114615954414915990553645)
          ·
            refine ⟨52917980982905593496457617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141114615954414915990553645 52917980982905593496457617)
            ·
              refine ⟨39688485737179195122343213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52917980982905593496457617 39688485737179195122343213)
              ·
                refine ⟨14883182151442198170878705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39688485737179195122343213 14883182151442198170878705)
                ·
                  refine ⟨11162386613581648628159029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14883182151442198170878705 11162386613581648628159029)
                  ·
                    refine ⟨1046473745023279558889909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11162386613581648628159029 1046473745023279558889909)
                    ·
                      rfl

theorem cell23_6114001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_6114001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114001 prefixEnd_6114001 := by exact prefixLift 6114001
  have htrace : WordTrace (prefixWord ++ tailWord_6114001) baseStart_6114001 baseEnd_6114001 := by
    simpa [prefixWord, tailWord_6114001, baseEnd_6114001] using wordTrace_append hprefix tailTrace_6114001
  have hstable : (prefixWord ++ tailWord_6114001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114001).length < 2 ^ (prefixWord ++ tailWord_6114001).sum := by decide
  have hdescent : baseEnd_6114001 < baseStart_6114001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114038 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_6114038 : Nat := 118140960795 + 6114038 * 2 ^ 59
def prefixEnd_6114038 : Nat := 4983230072969 + 3 ^ 40 * 6114038 * 2
def baseEnd_6114038 : Nat := 3139440233854055031907057

theorem tailTrace_6114038 : CollatzResearch.WordTrace tailWord_6114038 prefixEnd_6114038 3139440233854055031907057 := by
  unfold tailWord_6114038
  simp only [CollatzResearch.WordTrace]
  refine ⟨13937330363993249712683423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148664857215927996935289845 13937330363993249712683423)
  ·
    refine ⟨20905995545989874569025135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13937330363993249712683423 20905995545989874569025135)
    ·
      refine ⟨31358993318984811853537703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20905995545989874569025135 31358993318984811853537703)
      ·
        refine ⟨47038489978477217780306555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31358993318984811853537703 47038489978477217780306555)
        ·
          refine ⟨70557734967715826670459833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47038489978477217780306555 70557734967715826670459833)
          ·
            refine ⟨52918301225786870002844875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70557734967715826670459833 52918301225786870002844875)
            ·
              refine ⟨79377451838680305004267313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52918301225786870002844875 79377451838680305004267313)
              ·
                refine ⟨59533088879010228753200485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79377451838680305004267313 59533088879010228753200485)
                ·
                  refine ⟨11162454164814417891225091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59533088879010228753200485 11162454164814417891225091)
                  ·
                    refine ⟨16743681247221626836837637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11162454164814417891225091 16743681247221626836837637)
                    ·
                      refine ⟨3139440233854055031907057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16743681247221626836837637 3139440233854055031907057)
                      ·
                        rfl

theorem cell23_6114038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_6114038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114038 prefixEnd_6114038 := by exact prefixLift 6114038
  have htrace : WordTrace (prefixWord ++ tailWord_6114038) baseStart_6114038 baseEnd_6114038 := by
    simpa [prefixWord, tailWord_6114038, baseEnd_6114038] using wordTrace_append hprefix tailTrace_6114038
  have hstable : (prefixWord ++ tailWord_6114038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114038).length < 2 ^ (prefixWord ++ tailWord_6114038).sum := by decide
  have hdescent : baseEnd_6114038 < baseStart_6114038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114041 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 3, 4, 3]
def baseStart_6114041 : Nat := 118140960795 + 6114041 * 2 ^ 59
def prefixEnd_6114041 : Nat := 4983230072969 + 3 ^ 40 * 6114041 * 2
def baseEnd_6114041 : Nat := 3139441774296018520169543

theorem tailTrace_6114041 : CollatzResearch.WordTrace tailWord_6114041 prefixEnd_6114041 3139441774296018520169543 := by
  unfold tailWord_6114041
  simp only [CollatzResearch.WordTrace]
  refine ⟨222997395242881126915293977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148664930161920751276862651 222997395242881126915293977)
  ·
    refine ⟨167248046432160845186470483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222997395242881126915293977 167248046432160845186470483)
    ·
      refine ⟨250872069648241267779705725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167248046432160845186470483 250872069648241267779705725)
      ·
        refine ⟨94077026118090475417389647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250872069648241267779705725 94077026118090475417389647)
        ·
          refine ⟨141115539177135713126084471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94077026118090475417389647 141115539177135713126084471)
          ·
            refine ⟨211673308765703569689126707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141115539177135713126084471 211673308765703569689126707)
            ·
              refine ⟨317509963148555354533690061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211673308765703569689126707 317509963148555354533690061)
              ·
                refine ⟨119066236180708257950133773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317509963148555354533690061 119066236180708257950133773)
                ·
                  refine ⟨44649838567765596731300165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119066236180708257950133773 44649838567765596731300165)
                  ·
                    refine ⟨8371844731456049387118781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44649838567765596731300165 8371844731456049387118781)
                    ·
                      refine ⟨3139441774296018520169543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8371844731456049387118781 3139441774296018520169543)
                      ·
                        rfl

theorem cell23_6114041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_6114041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114041 prefixEnd_6114041 := by exact prefixLift 6114041
  have htrace : WordTrace (prefixWord ++ tailWord_6114041) baseStart_6114041 baseEnd_6114041 := by
    simpa [prefixWord, tailWord_6114041, baseEnd_6114041] using wordTrace_append hprefix tailTrace_6114041
  have hstable : (prefixWord ++ tailWord_6114041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114041).length < 2 ^ (prefixWord ++ tailWord_6114041).sum := by decide
  have hdescent : baseEnd_6114041 < baseStart_6114041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114055 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 4]
def baseStart_6114055 : Nat := 118140960795 + 6114055 * 2 ^ 59
def prefixEnd_6114055 : Nat := 4983230072969 + 3 ^ 40 * 6114055 * 2
def baseEnd_6114055 : Nat := 3139448963025181465394479

theorem tailTrace_6114055 : CollatzResearch.WordTrace tailWord_6114055 prefixEnd_6114055 3139448963025181465394479 := by
  unfold tailWord_6114055
  simp only [CollatzResearch.WordTrace]
  refine ⟨222997905864830407306303619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148665270576553604870869079 222997905864830407306303619)
  ·
    refine ⟨334496858797245610959455429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222997905864830407306303619 334496858797245610959455429)
    ·
      refine ⟨62718161024483552054897893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 334496858797245610959455429 62718161024483552054897893)
      ·
        refine ⟨11759655192090666010293355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62718161024483552054897893 11759655192090666010293355)
        ·
          refine ⟨17639482788135999015440033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11759655192090666010293355 17639482788135999015440033)
          ·
            refine ⟨13229612091101999261580025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17639482788135999015440033 13229612091101999261580025)
            ·
              refine ⟨9922209068326499446185019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13229612091101999261580025 9922209068326499446185019)
              ·
                refine ⟨14883313602489749169277529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9922209068326499446185019 14883313602489749169277529)
                ·
                  refine ⟨11162485201867311876958147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14883313602489749169277529 11162485201867311876958147)
                  ·
                    refine ⟨16743727802800967815437221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11162485201867311876958147 16743727802800967815437221)
                    ·
                      refine ⟨3139448963025181465394479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16743727802800967815437221 3139448963025181465394479)
                      ·
                        rfl

theorem cell23_6114055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_6114055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114055 prefixEnd_6114055 := by exact prefixLift 6114055
  have htrace : WordTrace (prefixWord ++ tailWord_6114055) baseStart_6114055 baseEnd_6114055 := by
    simpa [prefixWord, tailWord_6114055, baseEnd_6114055] using wordTrace_append hprefix tailTrace_6114055
  have hstable : (prefixWord ++ tailWord_6114055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114055).length < 2 ^ (prefixWord ++ tailWord_6114055).sum := by decide
  have hdescent : baseEnd_6114055 < baseStart_6114055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114081 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_6114081 : Nat := 118140960795 + 6114081 * 2 ^ 59
def prefixEnd_6114081 : Nat := 4983230072969 + 3 ^ 40 * 6114081 * 2
def baseEnd_6114081 : Nat := 3139462313522198363669359

theorem tailTrace_6114081 : CollatzResearch.WordTrace tailWord_6114081 prefixEnd_6114081 3139462313522198363669359 := by
  unfold tailWord_6114081
  simp only [CollatzResearch.WordTrace]
  refine ⟨222998854162736213746750097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148665902775157475831166731 222998854162736213746750097)
  ·
    refine ⟨167249140622052160310062573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222998854162736213746750097 167249140622052160310062573)
    ·
      refine ⟨62718427733269560116273465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167249140622052160310062573 62718427733269560116273465)
      ·
        refine ⟨47038820799952170087205099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62718427733269560116273465 47038820799952170087205099)
        ·
          refine ⟨70558231199928255130807649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47038820799952170087205099 70558231199928255130807649)
          ·
            refine ⟨52918673399946191348105737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70558231199928255130807649 52918673399946191348105737)
            ·
              refine ⟨39689005049959643511079303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52918673399946191348105737 39689005049959643511079303)
              ·
                refine ⟨59533507574939465266618955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39689005049959643511079303 59533507574939465266618955)
                ·
                  refine ⟨89300261362409197899928433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59533507574939465266618955 89300261362409197899928433)
                  ·
                    refine ⟨66975196021806898424946325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89300261362409197899928433 66975196021806898424946325)
                    ·
                      refine ⟨3139462313522198363669359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66975196021806898424946325 3139462313522198363669359)
                      ·
                        rfl

theorem cell23_6114081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_6114081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114081 prefixEnd_6114081 := by exact prefixLift 6114081
  have htrace : WordTrace (prefixWord ++ tailWord_6114081) baseStart_6114081 baseEnd_6114081 := by
    simpa [prefixWord, tailWord_6114081, baseEnd_6114081] using wordTrace_append hprefix tailTrace_6114081
  have hstable : (prefixWord ++ tailWord_6114081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114081).length < 2 ^ (prefixWord ++ tailWord_6114081).sum := by decide
  have hdescent : baseEnd_6114081 < baseStart_6114081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114082 : List Nat := [3, 3, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_6114082 : Nat := 118140960795 + 6114082 * 2 ^ 59
def prefixEnd_6114082 : Nat := 4983230072969 + 3 ^ 40 * 6114082 * 2
def baseEnd_6114082 : Nat := 1046487609000950953252285

theorem tailTrace_6114082 : CollatzResearch.WordTrace tailWord_6114082 prefixEnd_6114082 1046487609000950953252285 := by
  unfold tailWord_6114082
  simp only [CollatzResearch.WordTrace]
  refine ⟨55749722658933147729384125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148665927090488393945024333 55749722658933147729384125)
  ·
    refine ⟨20906145997099930398519047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55749722658933147729384125 20906145997099930398519047)
    ·
      refine ⟨31359218995649895597778571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20906145997099930398519047 31359218995649895597778571)
      ·
        refine ⟨47038828493474843396667857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31359218995649895597778571 47038828493474843396667857)
        ·
          refine ⟨35279121370106132547500893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47038828493474843396667857 35279121370106132547500893)
          ·
            refine ⟨13229670513789799705312835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35279121370106132547500893 13229670513789799705312835)
            ·
              refine ⟨19844505770684699557969253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13229670513789799705312835 19844505770684699557969253)
              ·
                refine ⟨3720844832003381167119235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19844505770684699557969253 3720844832003381167119235)
                ·
                  refine ⟨5581267248005071750678853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3720844832003381167119235 5581267248005071750678853)
                  ·
                    refine ⟨1046487609000950953252285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5581267248005071750678853 1046487609000950953252285)
                    ·
                      rfl

theorem cell23_6114082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_6114082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114082 prefixEnd_6114082 := by exact prefixLift 6114082
  have htrace : WordTrace (prefixWord ++ tailWord_6114082) baseStart_6114082 baseEnd_6114082 := by
    simpa [prefixWord, tailWord_6114082, baseEnd_6114082] using wordTrace_append hprefix tailTrace_6114082
  have hstable : (prefixWord ++ tailWord_6114082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114082).length < 2 ^ (prefixWord ++ tailWord_6114082).sum := by decide
  have hdescent : baseEnd_6114082 < baseStart_6114082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114091 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 3, 5]
def baseStart_6114091 : Nat := 118140960795 + 6114091 * 2 ^ 59
def prefixEnd_6114091 : Nat := 4983230072969 + 3 ^ 40 * 6114091 * 2
def baseEnd_6114091 : Nat := 1046489149442914441514771

theorem tailTrace_6114091 : CollatzResearch.WordTrace tailWord_6114091 prefixEnd_6114091 1046489149442914441514771 := by
  unfold tailWord_6114091
  simp only [CollatzResearch.WordTrace]
  refine ⟨222999218892699985454614127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148666145928466656969742751 222999218892699985454614127)
  ·
    refine ⟨334498828339049978181921191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222999218892699985454614127 334498828339049978181921191)
    ·
      refine ⟨501748242508574967272881787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334498828339049978181921191 501748242508574967272881787)
      ·
        refine ⟨752622363762862450909322681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501748242508574967272881787 752622363762862450909322681)
        ·
          refine ⟨564466772822146838181992011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 752622363762862450909322681 564466772822146838181992011)
          ·
            refine ⟨846700159233220257272988017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564466772822146838181992011 846700159233220257272988017)
            ·
              refine ⟨635025119424915192954741013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 846700159233220257272988017 635025119424915192954741013)
              ·
                refine ⟨29766802473042899669753485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 635025119424915192954741013 29766802473042899669753485)
                ·
                  refine ⟨11162550927391087376157557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29766802473042899669753485 11162550927391087376157557)
                  ·
                    refine ⟨1046489149442914441514771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11162550927391087376157557 1046489149442914441514771)
                    ·
                      rfl

theorem cell23_6114091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 5].length) (baseStart_6114091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114091 prefixEnd_6114091 := by exact prefixLift 6114091
  have htrace : WordTrace (prefixWord ++ tailWord_6114091) baseStart_6114091 baseEnd_6114091 := by
    simpa [prefixWord, tailWord_6114091, baseEnd_6114091] using wordTrace_append hprefix tailTrace_6114091
  have hstable : (prefixWord ++ tailWord_6114091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114091).length < 2 ^ (prefixWord ++ tailWord_6114091).sum := by decide
  have hdescent : baseEnd_6114091 < baseStart_6114091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114108 : List Nat := [2, 2, 2, 2, 1, 1, 1, 6, 1, 5]
def baseStart_6114108 : Nat := 118140960795 + 6114108 * 2 ^ 59
def prefixEnd_6114108 : Nat := 4983230072969 + 3 ^ 40 * 6114108 * 2
def baseEnd_6114108 : Nat := 1046492059166623252677245

theorem tailTrace_6114108 : CollatzResearch.WordTrace tailWord_6114108 prefixEnd_6114108 1046492059166623252677245 := by
  unfold tailWord_6114108
  simp only [CollatzResearch.WordTrace]
  refine ⟨111499919466819198678991489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148666559289092264905321985 111499919466819198678991489)
  ·
    refine ⟨83624939600114399009243617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111499919466819198678991489 83624939600114399009243617)
    ·
      refine ⟨62718704700085799256932713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83624939600114399009243617 62718704700085799256932713)
      ·
        refine ⟨47039028525064349442699535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62718704700085799256932713 47039028525064349442699535)
        ·
          refine ⟨70558542787596524164049303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47039028525064349442699535 70558542787596524164049303)
          ·
            refine ⟨105837814181394786246073955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70558542787596524164049303 105837814181394786246073955)
            ·
              refine ⟨158756721272092179369110933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105837814181394786246073955 158756721272092179369110933)
              ·
                refine ⟨7441721309629320907927075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 158756721272092179369110933 7441721309629320907927075)
                ·
                  refine ⟨11162581964443981361890613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7441721309629320907927075 11162581964443981361890613)
                  ·
                    refine ⟨1046492059166623252677245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11162581964443981361890613 1046492059166623252677245)
                    ·
                      rfl

theorem cell23_6114108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_6114108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114108 prefixEnd_6114108 := by exact prefixLift 6114108
  have htrace : WordTrace (prefixWord ++ tailWord_6114108) baseStart_6114108 baseEnd_6114108 := by
    simpa [prefixWord, tailWord_6114108, baseEnd_6114108] using wordTrace_append hprefix tailTrace_6114108
  have hstable : (prefixWord ++ tailWord_6114108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114108).length < 2 ^ (prefixWord ++ tailWord_6114108).sum := by decide
  have hdescent : baseEnd_6114108 < baseStart_6114108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114109 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 2, 2, 3]
def baseStart_6114109 : Nat := 118140960795 + 6114109 * 2 ^ 59
def prefixEnd_6114109 : Nat := 4983230072969 + 3 ^ 40 * 6114109 * 2
def baseEnd_6114109 : Nat := 3139476690980524254119231

theorem tailTrace_6114109 : CollatzResearch.WordTrace tailWord_6114109 prefixEnd_6114109 3139476690980524254119231 := by
  unfold tailWord_6114109
  simp only [CollatzResearch.WordTrace]
  refine ⟨222999875406634774528769381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148666583604423183019179587 222999875406634774528769381)
  ·
    refine ⟨41812476638744020224144259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222999875406634774528769381 41812476638744020224144259)
    ·
      refine ⟨62718714958116030336216389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41812476638744020224144259 62718714958116030336216389)
      ·
        refine ⟨11759759054646755688040573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62718714958116030336216389 11759759054646755688040573)
        ·
          refine ⟨4409909645492533383015215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11759759054646755688040573 4409909645492533383015215)
          ·
            refine ⟨6614864468238800074522823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4409909645492533383015215 6614864468238800074522823)
            ·
              refine ⟨9922296702358200111784235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6614864468238800074522823 9922296702358200111784235)
              ·
                refine ⟨14883445053537300167676353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9922296702358200111784235 14883445053537300167676353)
                ·
                  refine ⟨11162583790152975125757265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14883445053537300167676353 11162583790152975125757265)
                  ·
                    refine ⟨8371937842614731344317949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11162583790152975125757265 8371937842614731344317949)
                    ·
                      refine ⟨3139476690980524254119231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8371937842614731344317949 3139476690980524254119231)
                      ·
                        rfl

theorem cell23_6114109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_6114109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114109 prefixEnd_6114109 := by exact prefixLift 6114109
  have htrace : WordTrace (prefixWord ++ tailWord_6114109) baseStart_6114109 baseEnd_6114109 := by
    simpa [prefixWord, tailWord_6114109, baseEnd_6114109] using wordTrace_append hprefix tailTrace_6114109
  have hstable : (prefixWord ++ tailWord_6114109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114109).length < 2 ^ (prefixWord ++ tailWord_6114109).sum := by decide
  have hdescent : baseEnd_6114109 < baseStart_6114109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114116 : List Nat := [2, 3, 4, 2, 1, 1, 2, 3, 1, 4]
def baseStart_6114116 : Nat := 118140960795 + 6114116 * 2 ^ 59
def prefixEnd_6114116 : Nat := 4983230072969 + 3 ^ 40 * 6114116 * 2
def baseEnd_6114116 : Nat := 1046493428448368575577233

theorem tailTrace_6114116 : CollatzResearch.WordTrace tailWord_6114116 prefixEnd_6114116 1046493428448368575577233 := by
  unfold tailWord_6114116
  simp only [CollatzResearch.WordTrace]
  refine ⟨111500065358804707362137101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148666753811739609816182801 111500065358804707362137101)
  ·
    refine ⟨41812524509551765260801413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111500065358804707362137101 41812524509551765260801413)
    ·
      refine ⟨7839848345540955986400265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41812524509551765260801413 7839848345540955986400265)
      ·
        refine ⟨5879886259155716989800199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7839848345540955986400265 5879886259155716989800199)
        ·
          refine ⟨8819829388733575484700299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5879886259155716989800199 8819829388733575484700299)
          ·
            refine ⟨13229744083100363227050449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8819829388733575484700299 13229744083100363227050449)
            ·
              refine ⟨9922308062325272420287837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13229744083100363227050449 9922308062325272420287837)
              ·
                refine ⟨3720865523371977157607939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9922308062325272420287837 3720865523371977157607939)
                ·
                  refine ⟨5581298285057965736411909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3720865523371977157607939 5581298285057965736411909)
                  ·
                    refine ⟨1046493428448368575577233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5581298285057965736411909 1046493428448368575577233)
                    ·
                      rfl

theorem cell23_6114116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_6114116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114116 prefixEnd_6114116 := by exact prefixLift 6114116
  have htrace : WordTrace (prefixWord ++ tailWord_6114116) baseStart_6114116 baseEnd_6114116 := by
    simpa [prefixWord, tailWord_6114116, baseEnd_6114116] using wordTrace_append hprefix tailTrace_6114116
  have hstable : (prefixWord ++ tailWord_6114116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114116).length < 2 ^ (prefixWord ++ tailWord_6114116).sum := by decide
  have hdescent : baseEnd_6114116 < baseStart_6114116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114131 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 5]
def baseStart_6114131 : Nat := 118140960795 + 6114131 * 2 ^ 59
def prefixEnd_6114131 : Nat := 4983230072969 + 3 ^ 40 * 6114131 * 2
def baseEnd_6114131 : Nat := 3139487987554923168044129

theorem tailTrace_6114131 : CollatzResearch.WordTrace tailWord_6114131 prefixEnd_6114131 3139487987554923168044129 := by
  unfold tailWord_6114131
  simp only [CollatzResearch.WordTrace]
  refine ⟨223000677812555072286070247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148667118541703381524046831 223000677812555072286070247)
  ·
    refine ⟨334501016718832608429105371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223000677812555072286070247 334501016718832608429105371)
    ·
      refine ⟨501751525078248912643658057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334501016718832608429105371 501751525078248912643658057)
      ·
        refine ⟨376313643808686684482743543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501751525078248912643658057 376313643808686684482743543)
        ·
          refine ⟨564470465713030026724115315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376313643808686684482743543 564470465713030026724115315)
          ·
            refine ⟨846705698569545040086172973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564470465713030026724115315 846705698569545040086172973)
            ·
              refine ⟨317514636963579390032314865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 846705698569545040086172973 317514636963579390032314865)
              ·
                refine ⟨238135977722684542524236149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317514636963579390032314865 238135977722684542524236149)
                ·
                  refine ⟨22325247911501675861647139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 238135977722684542524236149 22325247911501675861647139)
                  ·
                    refine ⟨33487871867252513792470709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22325247911501675861647139 33487871867252513792470709)
                    ·
                      refine ⟨3139487987554923168044129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33487871867252513792470709 3139487987554923168044129)
                      ·
                        rfl

theorem cell23_6114131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_6114131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114131 prefixEnd_6114131 := by exact prefixLift 6114131
  have htrace : WordTrace (prefixWord ++ tailWord_6114131) baseStart_6114131 baseEnd_6114131 := by
    simpa [prefixWord, tailWord_6114131, baseEnd_6114131] using wordTrace_append hprefix tailTrace_6114131
  have hstable : (prefixWord ++ tailWord_6114131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114131).length < 2 ^ (prefixWord ++ tailWord_6114131).sum := by decide
  have hdescent : baseEnd_6114131 < baseStart_6114131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114148 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_6114148 : Nat := 118140960795 + 6114148 * 2 ^ 59
def prefixEnd_6114148 : Nat := 4983230072969 + 3 ^ 40 * 6114148 * 2
def baseEnd_6114148 : Nat := 3139496716726049601531551

theorem tailTrace_6114148 : CollatzResearch.WordTrace tailWord_6114148 prefixEnd_6114148 3139496716726049601531551 := by
  unfold tailWord_6114148
  simp only [CollatzResearch.WordTrace]
  refine ⟨111500648926746742094719549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148667531902328989459626065 111500648926746742094719549)
  ·
    refine ⟨41812743347530028285519831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111500648926746742094719549 41812743347530028285519831)
    ·
      refine ⟨62719115021295042428279747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41812743347530028285519831 62719115021295042428279747)
      ·
        refine ⟨94078672531942563642419621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62719115021295042428279747 94078672531942563642419621)
        ·
          refine ⟨17639751099739230682953679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94078672531942563642419621 17639751099739230682953679)
          ·
            refine ⟨26459626649608846024430519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17639751099739230682953679 26459626649608846024430519)
            ·
              refine ⟨39689439974413269036645779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26459626649608846024430519 39689439974413269036645779)
              ·
                refine ⟨59534159961619903554968669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39689439974413269036645779 59534159961619903554968669)
                ·
                  refine ⟨22325309985607463833113251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59534159961619903554968669 22325309985607463833113251)
                  ·
                    refine ⟨33487964978411195749669877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22325309985607463833113251 33487964978411195749669877)
                    ·
                      refine ⟨3139496716726049601531551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33487964978411195749669877 3139496716726049601531551)
                      ·
                        rfl

theorem cell23_6114148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_6114148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114148 prefixEnd_6114148 := by exact prefixLift 6114148
  have htrace : WordTrace (prefixWord ++ tailWord_6114148) baseStart_6114148 baseEnd_6114148 := by
    simpa [prefixWord, tailWord_6114148, baseEnd_6114148] using wordTrace_append hprefix tailTrace_6114148
  have hstable : (prefixWord ++ tailWord_6114148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114148).length < 2 ^ (prefixWord ++ tailWord_6114148).sum := by decide
  have hdescent : baseEnd_6114148 < baseStart_6114148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114162 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 3, 2, 2]
def baseStart_6114162 : Nat := 118140960795 + 6114162 * 2 ^ 59
def prefixEnd_6114162 : Nat := 4983230072969 + 3 ^ 40 * 6114162 * 2
def baseEnd_6114162 : Nat := 3139503905455212546756487

theorem tailTrace_6114162 : CollatzResearch.WordTrace tailWord_6114162 prefixEnd_6114162 3139503905455212546756487 := by
  unfold tailWord_6114162
  simp only [CollatzResearch.WordTrace]
  refine ⟨55750452118860691145112185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148667872316961843053632493 55750452118860691145112185)
  ·
    refine ⟨41812839089145518358834139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55750452118860691145112185 41812839089145518358834139)
    ·
      refine ⟨62719258633718277538251209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41812839089145518358834139 62719258633718277538251209)
      ·
        refine ⟨47039443975288708153688407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62719258633718277538251209 47039443975288708153688407)
        ·
          refine ⟨70559165962933062230532611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47039443975288708153688407 70559165962933062230532611)
          ·
            refine ⟨105838748944399593345798917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70559165962933062230532611 105838748944399593345798917)
            ·
              refine ⟨19844765427074923752337297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105838748944399593345798917 19844765427074923752337297)
              ·
                refine ⟨14883574070306192814252973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19844765427074923752337297 14883574070306192814252973)
                ·
                  refine ⟨5581340276364822305344865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14883574070306192814252973 5581340276364822305344865)
                  ·
                    refine ⟨4186005207273616729008649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5581340276364822305344865 4186005207273616729008649)
                    ·
                      refine ⟨3139503905455212546756487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4186005207273616729008649 3139503905455212546756487)
                      ·
                        rfl

theorem cell23_6114162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_6114162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114162 prefixEnd_6114162 := by exact prefixLift 6114162
  have htrace : WordTrace (prefixWord ++ tailWord_6114162) baseStart_6114162 baseEnd_6114162 := by
    simpa [prefixWord, tailWord_6114162, baseEnd_6114162] using wordTrace_append hprefix tailTrace_6114162
  have hstable : (prefixWord ++ tailWord_6114162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114162).length < 2 ^ (prefixWord ++ tailWord_6114162).sum := by decide
  have hdescent : baseEnd_6114162 < baseStart_6114162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114212 : List Nat := [2, 3, 1, 2, 1, 2, 3, 3, 2, 1, 3]
def baseStart_6114212 : Nat := 118140960795 + 6114212 * 2 ^ 59
def prefixEnd_6114212 : Nat := 4983230072969 + 3 ^ 40 * 6114212 * 2
def baseEnd_6114212 : Nat := 3139529579487937351131257

theorem tailTrace_6114212 : CollatzResearch.WordTrace tailWord_6114212 prefixEnd_6114212 3139529579487937351131257 := by
  unfold tailWord_6114212
  simp only [CollatzResearch.WordTrace]
  refine ⟨111501816062630811559884445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148669088083507748746512593 111501816062630811559884445)
  ·
    refine ⟨41813181023486554334956667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111501816062630811559884445 41813181023486554334956667)
    ·
      refine ⟨62719771535229831502435001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41813181023486554334956667 62719771535229831502435001)
      ·
        refine ⟨47039828651422373626826251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62719771535229831502435001 47039828651422373626826251)
        ·
          refine ⟨70559742977133560440239377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47039828651422373626826251 70559742977133560440239377)
          ·
            refine ⟨52919807232850170330179533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70559742977133560440239377 52919807232850170330179533)
            ·
              refine ⟨19844927712318813873817325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52919807232850170330179533 19844927712318813873817325)
              ·
                refine ⟨7441847892119555202681497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19844927712318813873817325 7441847892119555202681497)
                ·
                  refine ⟨5581385919089666402011123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7441847892119555202681497 5581385919089666402011123)
                  ·
                    refine ⟨8372078878634499603016685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5581385919089666402011123 8372078878634499603016685)
                    ·
                      refine ⟨3139529579487937351131257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8372078878634499603016685 3139529579487937351131257)
                      ·
                        rfl

theorem cell23_6114212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_6114212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114212 prefixEnd_6114212 := by exact prefixLift 6114212
  have htrace : WordTrace (prefixWord ++ tailWord_6114212) baseStart_6114212 baseEnd_6114212 := by
    simpa [prefixWord, tailWord_6114212, baseEnd_6114212] using wordTrace_append hprefix tailTrace_6114212
  have hstable : (prefixWord ++ tailWord_6114212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114212).length < 2 ^ (prefixWord ++ tailWord_6114212).sum := by decide
  have hdescent : baseEnd_6114212 < baseStart_6114212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114262 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_6114262 : Nat := 118140960795 + 6114262 * 2 ^ 59
def prefixEnd_6114262 : Nat := 4983230072969 + 3 ^ 40 * 6114262 * 2
def baseEnd_6114262 : Nat := 1046518417840220718502009

theorem tailTrace_6114262 : CollatzResearch.WordTrace tailWord_6114262 prefixEnd_6114262 1046518417840220718502009 := by
  unfold tailWord_6114262
  simp only [CollatzResearch.WordTrace]
  refine ⟨13937840985942530103693065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148670303850053654439392693 13937840985942530103693065)
  ·
    refine ⟨10453380739456897577769799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13937840985942530103693065 10453380739456897577769799)
    ·
      refine ⟨15680071109185346366654699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10453380739456897577769799 15680071109185346366654699)
      ·
        refine ⟨23520106663778019549982049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15680071109185346366654699 23520106663778019549982049)
        ·
          refine ⟨17640079997833514662486537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23520106663778019549982049 17640079997833514662486537)
          ·
            refine ⟨13230059998375135996864903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17640079997833514662486537 13230059998375135996864903)
            ·
              refine ⟨19845089997562703995297355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13230059998375135996864903 19845089997562703995297355)
              ·
                refine ⟨29767634996344055992946033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19845089997562703995297355 29767634996344055992946033)
                ·
                  refine ⟨22325726247258041994709525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29767634996344055992946033 22325726247258041994709525)
                  ·
                    refine ⟨1046518417840220718502009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22325726247258041994709525 1046518417840220718502009)
                    ·
                      rfl

theorem cell23_6114262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_6114262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114262 prefixEnd_6114262 := by exact prefixLift 6114262
  have htrace : WordTrace (prefixWord ++ tailWord_6114262) baseStart_6114262 baseEnd_6114262 := by
    simpa [prefixWord, tailWord_6114262, baseEnd_6114262] using wordTrace_append hprefix tailTrace_6114262
  have hstable : (prefixWord ++ tailWord_6114262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114262).length < 2 ^ (prefixWord ++ tailWord_6114262).sum := by decide
  have hdescent : baseEnd_6114262 < baseStart_6114262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114265 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 2, 2, 4]
def baseStart_6114265 : Nat := 118140960795 + 6114265 * 2 ^ 59
def prefixEnd_6114265 : Nat := 4983230072969 + 3 ^ 40 * 6114265 * 2
def baseEnd_6114265 : Nat := 3139556793962625643768513

theorem tailTrace_6114265 : CollatzResearch.WordTrace tailWord_6114265 prefixEnd_6114265 3139556793962625643768513 := by
  unfold tailWord_6114265
  simp only [CollatzResearch.WordTrace]
  refine ⟨223005565194069613171448249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148670376796046408780965499 223005565194069613171448249)
  ·
    refine ⟨167254173895552209878586187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223005565194069613171448249 167254173895552209878586187)
    ·
      refine ⟨250881260843328314817879281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167254173895552209878586187 250881260843328314817879281)
      ·
        refine ⟨188160945632496236113409461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250881260843328314817879281 188160945632496236113409461)
        ·
          refine ⟨17640088653046522135632137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188160945632496236113409461 17640088653046522135632137)
          ·
            refine ⟨13230066489784891601724103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17640088653046522135632137 13230066489784891601724103)
            ·
              refine ⟨19845099734677337402586155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13230066489784891601724103 19845099734677337402586155)
              ·
                refine ⟨29767649602016006103879233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19845099734677337402586155 29767649602016006103879233)
                ·
                  refine ⟨22325737201512004577909425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29767649602016006103879233 22325737201512004577909425)
                  ·
                    refine ⟨16744302901134003433432069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22325737201512004577909425 16744302901134003433432069)
                    ·
                      refine ⟨3139556793962625643768513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16744302901134003433432069 3139556793962625643768513)
                      ·
                        rfl

theorem cell23_6114265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_6114265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114265 prefixEnd_6114265 := by exact prefixLift 6114265
  have htrace : WordTrace (prefixWord ++ tailWord_6114265) baseStart_6114265 baseEnd_6114265 := by
    simpa [prefixWord, tailWord_6114265, baseEnd_6114265] using wordTrace_append hprefix tailTrace_6114265
  have hstable : (prefixWord ++ tailWord_6114265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114265).length < 2 ^ (prefixWord ++ tailWord_6114265).sum := by decide
  have hdescent : baseEnd_6114265 < baseStart_6114265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114269 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_6114269 : Nat := 118140960795 + 6114269 * 2 ^ 59
def prefixEnd_6114269 : Nat := 4983230072969 + 3 ^ 40 * 6114269 * 2
def baseEnd_6114269 : Nat := 3139558847885243628118495

theorem tailTrace_6114269 : CollatzResearch.WordTrace tailWord_6114269 prefixEnd_6114269 3139558847885243628118495 := by
  unfold tailWord_6114269
  simp only [CollatzResearch.WordTrace]
  refine ⟨223005711086055121854593861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148670474057370081236395907 223005711086055121854593861)
  ·
    refine ⟨41813570828635335347736349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223005711086055121854593861 41813570828635335347736349)
    ·
      refine ⟨15680089060738250755401131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41813570828635335347736349 15680089060738250755401131)
      ·
        refine ⟨23520133591107376133101697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15680089060738250755401131 23520133591107376133101697)
        ·
          refine ⟨17640100193330532099826273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23520133591107376133101697 17640100193330532099826273)
          ·
            refine ⟨13230075144997899074869705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17640100193330532099826273 13230075144997899074869705)
            ·
              refine ⟨9922556358748424306152279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13230075144997899074869705 9922556358748424306152279)
              ·
                refine ⟨14883834538122636459228419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9922556358748424306152279 14883834538122636459228419)
                ·
                  refine ⟨22325751807183954688842629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14883834538122636459228419 22325751807183954688842629)
                  ·
                    refine ⟨4186078463846991504157993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22325751807183954688842629 4186078463846991504157993)
                    ·
                      refine ⟨3139558847885243628118495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4186078463846991504157993 3139558847885243628118495)
                      ·
                        rfl

theorem cell23_6114269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_6114269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114269 prefixEnd_6114269 := by exact prefixLift 6114269
  have htrace : WordTrace (prefixWord ++ tailWord_6114269) baseStart_6114269 baseEnd_6114269 := by
    simpa [prefixWord, tailWord_6114269, baseEnd_6114269] using wordTrace_append hprefix tailTrace_6114269
  have hstable : (prefixWord ++ tailWord_6114269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114269).length < 2 ^ (prefixWord ++ tailWord_6114269).sum := by decide
  have hdescent : baseEnd_6114269 < baseStart_6114269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114290 : List Nat := [3, 2, 1, 5, 2, 1, 2, 1, 1, 3, 2]
def baseStart_6114290 : Nat := 118140960795 + 6114290 * 2 ^ 59
def prefixEnd_6114290 : Nat := 4983230072969 + 3 ^ 40 * 6114290 * 2
def baseEnd_6114290 : Nat := 3139569630978988045955899

theorem tailTrace_6114290 : CollatzResearch.WordTrace tailWord_6114290 prefixEnd_6114290 3139569630978988045955899 := by
  unfold tailWord_6114290
  simp only [CollatzResearch.WordTrace]
  refine ⟨55751619254744760610277081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148670984679319361627405549 55751619254744760610277081)
  ·
    refine ⟨41813714441058570457707811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55751619254744760610277081 41813714441058570457707811)
    ·
      refine ⟨62720571661587855686561717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41813714441058570457707811 62720571661587855686561717)
      ·
        refine ⟨5880053593273861470615161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62720571661587855686561717 5880053593273861470615161)
        ·
          refine ⟨4410040194955396102961371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5880053593273861470615161 4410040194955396102961371)
          ·
            refine ⟨6615060292433094154442057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4410040194955396102961371 6615060292433094154442057)
            ·
              refine ⟨4961295219324820615831543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6615060292433094154442057 4961295219324820615831543)
              ·
                refine ⟨7441942828987230923747315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4961295219324820615831543 7441942828987230923747315)
                ·
                  refine ⟨11162914243480846385620973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7441942828987230923747315 11162914243480846385620973)
                  ·
                    refine ⟨4186092841305317394607865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11162914243480846385620973 4186092841305317394607865)
                    ·
                      refine ⟨3139569630978988045955899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4186092841305317394607865 3139569630978988045955899)
                      ·
                        rfl

theorem cell23_6114290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_6114290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114290 prefixEnd_6114290 := by exact prefixLift 6114290
  have htrace : WordTrace (prefixWord ++ tailWord_6114290) baseStart_6114290 baseEnd_6114290 := by
    simpa [prefixWord, tailWord_6114290, baseEnd_6114290] using wordTrace_append hprefix tailTrace_6114290
  have hstable : (prefixWord ++ tailWord_6114290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114290).length < 2 ^ (prefixWord ++ tailWord_6114290).sum := by decide
  have hdescent : baseEnd_6114290 < baseStart_6114290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114298 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5]
def baseStart_6114298 : Nat := 118140960795 + 6114298 * 2 ^ 59
def prefixEnd_6114298 : Nat := 4983230072969 + 3 ^ 40 * 6114298 * 2
def baseEnd_6114298 : Nat := 3139573738824224014655861

theorem tailTrace_6114298 : CollatzResearch.WordTrace tailWord_6114298 prefixEnd_6114298 3139573738824224014655861 := by
  unfold tailWord_6114298
  simp only [CollatzResearch.WordTrace]
  refine ⟨55751692200737514951849887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148671179201966706538266365 55751692200737514951849887)
  ·
    refine ⟨83627538301106272427774831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55751692200737514951849887 83627538301106272427774831)
    ·
      refine ⟨125441307451659408641662247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83627538301106272427774831 125441307451659408641662247)
      ·
        refine ⟨188161961177489112962493371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125441307451659408641662247 188161961177489112962493371)
        ·
          refine ⟨282242941766233669443740057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188161961177489112962493371 282242941766233669443740057)
          ·
            refine ⟨211682206324675252082805043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282242941766233669443740057 211682206324675252082805043)
            ·
              refine ⟨317523309487012878124207565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211682206324675252082805043 317523309487012878124207565)
              ·
                refine ⟨119071241057629829296577837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317523309487012878124207565 119071241057629829296577837)
                ·
                  refine ⟨44651715396611185986216689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119071241057629829296577837 44651715396611185986216689)
                  ·
                    refine ⟨33488786547458389489662517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44651715396611185986216689 33488786547458389489662517)
                    ·
                      refine ⟨3139573738824224014655861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33488786547458389489662517 3139573738824224014655861)
                      ·
                        rfl

theorem cell23_6114298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_6114298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114298 prefixEnd_6114298 := by exact prefixLift 6114298
  have htrace : WordTrace (prefixWord ++ tailWord_6114298) baseStart_6114298 baseEnd_6114298 := by
    simpa [prefixWord, tailWord_6114298, baseEnd_6114298] using wordTrace_append hprefix tailTrace_6114298
  have hstable : (prefixWord ++ tailWord_6114298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114298).length < 2 ^ (prefixWord ++ tailWord_6114298).sum := by decide
  have hdescent : baseEnd_6114298 < baseStart_6114298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114325 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_6114325 : Nat := 118140960795 + 6114325 * 2 ^ 59
def prefixEnd_6114325 : Nat := 4983230072969 + 3 ^ 40 * 6114325 * 2
def baseEnd_6114325 : Nat := 3139587602801895409018237

theorem tailTrace_6114325 : CollatzResearch.WordTrace tailWord_6114325 prefixEnd_6114325 3139587602801895409018237 := by
  unfold tailWord_6114325
  simp only [CollatzResearch.WordTrace]
  refine ⟨223007753573852243418632429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148671835715901495612421619 223007753573852243418632429)
  ·
    refine ⟨83627907590194591281987161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223007753573852243418632429 83627907590194591281987161)
    ·
      refine ⟨62720930692645943461490371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83627907590194591281987161 62720930692645943461490371)
      ·
        refine ⟨94081396038968915192235557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62720930692645943461490371 94081396038968915192235557)
        ·
          refine ⟨17640261757306671598544167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94081396038968915192235557 17640261757306671598544167)
          ·
            refine ⟨26460392635960007397816251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17640261757306671598544167 26460392635960007397816251)
            ·
              refine ⟨39690588953940011096724377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26460392635960007397816251 39690588953940011096724377)
              ·
                refine ⟨29767941715455008322543283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39690588953940011096724377 29767941715455008322543283)
                ·
                  refine ⟨44651912573182512483814925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29767941715455008322543283 44651912573182512483814925)
                  ·
                    refine ⟨16744467214943442181430597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44651912573182512483814925 16744467214943442181430597)
                    ·
                      refine ⟨3139587602801895409018237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16744467214943442181430597 3139587602801895409018237)
                      ·
                        rfl

theorem cell23_6114325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_6114325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114325 prefixEnd_6114325 := by exact prefixLift 6114325
  have htrace : WordTrace (prefixWord ++ tailWord_6114325) baseStart_6114325 baseEnd_6114325 := by
    simpa [prefixWord, tailWord_6114325, baseEnd_6114325] using wordTrace_append hprefix tailTrace_6114325
  have hstable : (prefixWord ++ tailWord_6114325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114325).length < 2 ^ (prefixWord ++ tailWord_6114325).sum := by decide
  have hdescent : baseEnd_6114325 < baseStart_6114325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114348 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 10]
def baseStart_6114348 : Nat := 118140960795 + 6114348 * 2 ^ 59
def prefixEnd_6114348 : Nat := 4983230072969 + 3 ^ 40 * 6114348 * 2
def baseEnd_6114348 : Nat := 348844379206327646558959

theorem tailTrace_6114348 : CollatzResearch.WordTrace tailWord_6114348 prefixEnd_6114348 348844379206327646558959 := by
  unfold tailWord_6114348
  simp only [CollatzResearch.WordTrace]
  refine ⟨111504296226384459173359849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148672394968512612231146465 111504296226384459173359849)
  ·
    refine ⟨83628222169788344380019887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111504296226384459173359849 83628222169788344380019887)
    ·
      refine ⟨125442333254682516570029831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83628222169788344380019887 125442333254682516570029831)
      ·
        refine ⟨188163499882023774855044747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125442333254682516570029831 188163499882023774855044747)
        ·
          refine ⟨282245249823035662282567121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188163499882023774855044747 282245249823035662282567121)
          ·
            refine ⟨211683937367276746711925341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282245249823035662282567121 211683937367276746711925341)
            ·
              refine ⟨79381476512728780016972003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211683937367276746711925341 79381476512728780016972003)
              ·
                refine ⟨119072214769093170025458005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79381476512728780016972003 119072214769093170025458005)
                ·
                  refine ⟨348844379206327646558959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 119072214769093170025458005 348844379206327646558959)
                  ·
                    rfl

theorem cell23_6114348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 10].length) (baseStart_6114348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114348 prefixEnd_6114348 := by exact prefixLift 6114348
  have htrace : WordTrace (prefixWord ++ tailWord_6114348) baseStart_6114348 baseEnd_6114348 := by
    simpa [prefixWord, tailWord_6114348, baseEnd_6114348] using wordTrace_append hprefix tailTrace_6114348
  have hstable : (prefixWord ++ tailWord_6114348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114348).length < 2 ^ (prefixWord ++ tailWord_6114348).sum := by decide
  have hdescent : baseEnd_6114348 < baseStart_6114348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114365 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 8]
def baseStart_6114365 : Nat := 118140960795 + 6114365 * 2 ^ 59
def prefixEnd_6114365 : Nat := 4983230072969 + 3 ^ 40 * 6114365 * 2
def baseEnd_6114365 : Nat := 348845349114230583613117

theorem tailTrace_6114365 : CollatzResearch.WordTrace tailWord_6114365 prefixEnd_6114365 348845349114230583613117 := by
  unfold tailWord_6114365
  simp only [CollatzResearch.WordTrace]
  refine ⟨223009212493707330250088549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148672808329138220166725699 223009212493707330250088549)
  ·
    refine ⟨41814227342570124421891603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223009212493707330250088549 41814227342570124421891603)
    ·
      refine ⟨62721341013855186632837405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41814227342570124421891603 62721341013855186632837405)
      ·
        refine ⟨23520502880195694987314027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62721341013855186632837405 23520502880195694987314027)
        ·
          refine ⟨35280754320293542480971041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23520502880195694987314027 35280754320293542480971041)
          ·
            refine ⟨26460565740220156860728281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35280754320293542480971041 26460565740220156860728281)
            ·
              refine ⟨19845424305165117645546211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26460565740220156860728281 19845424305165117645546211)
              ·
                refine ⟨29768136457747676468319317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19845424305165117645546211 29768136457747676468319317)
                ·
                  refine ⟨348845349114230583613117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29768136457747676468319317 348845349114230583613117)
                  ·
                    rfl

theorem cell23_6114365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_6114365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114365 prefixEnd_6114365 := by exact prefixLift 6114365
  have htrace : WordTrace (prefixWord ++ tailWord_6114365) baseStart_6114365 baseEnd_6114365 := by
    simpa [prefixWord, tailWord_6114365, baseEnd_6114365] using wordTrace_append hprefix tailTrace_6114365
  have hstable : (prefixWord ++ tailWord_6114365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114365).length < 2 ^ (prefixWord ++ tailWord_6114365).sum := by decide
  have hdescent : baseEnd_6114365 < baseStart_6114365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114392 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 5, 1, 3]
def baseStart_6114392 : Nat := 118140960795 + 6114392 * 2 ^ 59
def prefixEnd_6114392 : Nat := 4983230072969 + 3 ^ 40 * 6114392 * 2
def baseEnd_6114392 : Nat := 3139622006005746646880429

theorem tailTrace_6114392 : CollatzResearch.WordTrace tailWord_6114392 prefixEnd_6114392 3139622006005746646880429 := by
  unfold tailWord_6114392
  simp only [CollatzResearch.WordTrace]
  refine ⟨111505098632304756930660715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148673464843073009240880953 111505098632304756930660715)
  ·
    refine ⟨167257647948457135395991073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111505098632304756930660715 167257647948457135395991073)
    ·
      refine ⟨125443235961342851546993305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167257647948457135395991073 125443235961342851546993305)
      ·
        refine ⟨94082426971007138660244979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125443235961342851546993305 94082426971007138660244979)
        ·
          refine ⟨141123640456510707990367469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94082426971007138660244979 141123640456510707990367469)
          ·
            refine ⟨52921365171191515496387801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141123640456510707990367469 52921365171191515496387801)
            ·
              refine ⟨39691023878393636622290851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52921365171191515496387801 39691023878393636622290851)
              ·
                refine ⟨59536535817590454933436277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39691023878393636622290851 59536535817590454933436277)
                ·
                  refine ⟨5581550232899105150009651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59536535817590454933436277 5581550232899105150009651)
                  ·
                    refine ⟨8372325349348657725014477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5581550232899105150009651 8372325349348657725014477)
                    ·
                      refine ⟨3139622006005746646880429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8372325349348657725014477 3139622006005746646880429)
                      ·
                        rfl

theorem cell23_6114392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_6114392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114392 prefixEnd_6114392 := by exact prefixLift 6114392
  have htrace : WordTrace (prefixWord ++ tailWord_6114392) baseStart_6114392 baseEnd_6114392 := by
    simpa [prefixWord, tailWord_6114392, baseEnd_6114392] using wordTrace_append hprefix tailTrace_6114392
  have hstable : (prefixWord ++ tailWord_6114392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114392).length < 2 ^ (prefixWord ++ tailWord_6114392).sum := by decide
  have hdescent : baseEnd_6114392 < baseStart_6114392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114435 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 5]
def baseStart_6114435 : Nat := 118140960795 + 6114435 * 2 ^ 59
def prefixEnd_6114435 : Nat := 4983230072969 + 3 ^ 40 * 6114435 * 2
def baseEnd_6114435 : Nat := 3139644085673889978642731

theorem tailTrace_6114435 : CollatzResearch.WordTrace tailWord_6114435 prefixEnd_6114435 3139644085673889978642731 := by
  unfold tailWord_6114435
  simp only [CollatzResearch.WordTrace]
  refine ⟨223011765603453732205136759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148674510402302488136757839 223011765603453732205136759)
  ·
    refine ⟨334517648405180598307705139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223011765603453732205136759 334517648405180598307705139)
    ·
      refine ⟨501776472607770897461557709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334517648405180598307705139 501776472607770897461557709)
      ·
        refine ⟨188166177227914086548084141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 501776472607770897461557709 188166177227914086548084141)
        ·
          refine ⟨70562316460467782455531553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188166177227914086548084141 70562316460467782455531553)
          ·
            refine ⟨52921737345350836841648665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70562316460467782455531553 52921737345350836841648665)
            ·
              refine ⟨39691303009013127631236499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52921737345350836841648665 39691303009013127631236499)
              ·
                refine ⟨59536954513519691446854749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39691303009013127631236499 59536954513519691446854749)
                ·
                  refine ⟨22326357942569884292570531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59536954513519691446854749 22326357942569884292570531)
                  ·
                    refine ⟨33489536913854826438855797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22326357942569884292570531 33489536913854826438855797)
                    ·
                      refine ⟨3139644085673889978642731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33489536913854826438855797 3139644085673889978642731)
                      ·
                        rfl

theorem cell23_6114435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_6114435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114435 prefixEnd_6114435 := by exact prefixLift 6114435
  have htrace : WordTrace (prefixWord ++ tailWord_6114435) baseStart_6114435 baseEnd_6114435 := by
    simpa [prefixWord, tailWord_6114435, baseEnd_6114435] using wordTrace_append hprefix tailTrace_6114435
  have hstable : (prefixWord ++ tailWord_6114435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114435).length < 2 ^ (prefixWord ++ tailWord_6114435).sum := by decide
  have hdescent : baseEnd_6114435 < baseStart_6114435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114442 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 1, 6]
def baseStart_6114442 : Nat := 118140960795 + 6114442 * 2 ^ 59
def prefixEnd_6114442 : Nat := 4983230072969 + 3 ^ 40 * 6114442 * 2
def baseEnd_6114442 : Nat := 1046549226679490483751733

theorem tailTrace_6114442 : CollatzResearch.WordTrace tailWord_6114442 prefixEnd_6114442 1046549226679490483751733 := by
  unfold tailWord_6114442
  simp only [CollatzResearch.WordTrace]
  refine ⟨55753005228607093100160395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148674680609618914933761053 55753005228607093100160395)
  ·
    refine ⟨83629507842910639650240593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55753005228607093100160395 83629507842910639650240593)
    ·
      refine ⟨62722130882182979737680445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83629507842910639650240593 62722130882182979737680445)
      ·
        refine ⟨23520799080818617401630167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62722130882182979737680445 23520799080818617401630167)
        ·
          refine ⟨35281198621227926102445251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23520799080818617401630167 35281198621227926102445251)
          ·
            refine ⟨52921797931841889153667877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35281198621227926102445251 52921797931841889153667877)
            ·
              refine ⟨9922837112220354216312727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52921797931841889153667877 9922837112220354216312727)
              ·
                refine ⟨14884255668330531324469091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9922837112220354216312727 14884255668330531324469091)
                ·
                  refine ⟨22326383502495796986703637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14884255668330531324469091 22326383502495796986703637)
                  ·
                    refine ⟨1046549226679490483751733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22326383502495796986703637 1046549226679490483751733)
                    ·
                      rfl

theorem cell23_6114442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_6114442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114442 prefixEnd_6114442 := by exact prefixLift 6114442
  have htrace : WordTrace (prefixWord ++ tailWord_6114442) baseStart_6114442 baseEnd_6114442 := by
    simpa [prefixWord, tailWord_6114442, baseEnd_6114442] using wordTrace_append hprefix tailTrace_6114442
  have hstable : (prefixWord ++ tailWord_6114442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114442).length < 2 ^ (prefixWord ++ tailWord_6114442).sum := by decide
  have hdescent : baseEnd_6114442 < baseStart_6114442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114463 : List Nat := [1, 1, 2, 6, 3, 1, 2, 1, 1, 5]
def baseStart_6114463 : Nat := 118140960795 + 6114463 * 2 ^ 59
def prefixEnd_6114463 : Nat := 4983230072969 + 3 ^ 40 * 6114463 * 2
def baseEnd_6114463 : Nat := 1046552821044071956364201

theorem tailTrace_6114463 : CollatzResearch.WordTrace tailWord_6114463 prefixEnd_6114463 1046552821044071956364201 := by
  unfold tailWord_6114463
  simp only [CollatzResearch.WordTrace]
  refine ⟨223012786847352292987156043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148675191231568195324770695 223012786847352292987156043)
  ·
    refine ⟨334519180271028439480734065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223012786847352292987156043 334519180271028439480734065)
    ·
      refine ⟨250889385203271329610550549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334519180271028439480734065 250889385203271329610550549)
      ·
        refine ⟨11760439931403343575494557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 250889385203271329610550549 11760439931403343575494557)
        ·
          refine ⟨4410164974276253840810459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11760439931403343575494557 4410164974276253840810459)
          ·
            refine ⟨6615247461414380761215689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4410164974276253840810459 6615247461414380761215689)
            ·
              refine ⟨4961435596060785570911767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6615247461414380761215689 4961435596060785570911767)
              ·
                refine ⟨7442153394091178356367651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4961435596060785570911767 7442153394091178356367651)
                ·
                  refine ⟨11163230091136767534551477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7442153394091178356367651 11163230091136767534551477)
                  ·
                    refine ⟨1046552821044071956364201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11163230091136767534551477 1046552821044071956364201)
                    ·
                      rfl

theorem cell23_6114463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 1, 5].length) (baseStart_6114463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114463 prefixEnd_6114463 := by exact prefixLift 6114463
  have htrace : WordTrace (prefixWord ++ tailWord_6114463) baseStart_6114463 baseEnd_6114463 := by
    simpa [prefixWord, tailWord_6114463, baseEnd_6114463] using wordTrace_append hprefix tailTrace_6114463
  have hstable : (prefixWord ++ tailWord_6114463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114463).length < 2 ^ (prefixWord ++ tailWord_6114463).sum := by decide
  have hdescent : baseEnd_6114463 < baseStart_6114463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114466 : List Nat := [3, 3, 1, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_6114466 : Nat := 118140960795 + 6114466 * 2 ^ 59
def prefixEnd_6114466 : Nat := 4983230072969 + 3 ^ 40 * 6114466 * 2
def baseEnd_6114466 : Nat := 3139660003574179357355089

theorem tailTrace_6114466 : CollatzResearch.WordTrace tailWord_6114466 prefixEnd_6114466 3139660003574179357355089 := by
  unfold tailWord_6114466
  simp only [CollatzResearch.WordTrace]
  refine ⟨55753224066585356124878813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148675264177560949666343501 55753224066585356124878813)
  ·
    refine ⟨20907459024969508546829555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55753224066585356124878813 20907459024969508546829555)
    ·
      refine ⟨31361188537454262820244333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20907459024969508546829555 31361188537454262820244333)
      ·
        refine ⟨11760445701545348557591625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31361188537454262820244333 11760445701545348557591625)
        ·
          refine ⟨8820334276159011418193719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11760445701545348557591625 8820334276159011418193719)
          ·
            refine ⟨13230501414238517127290579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8820334276159011418193719 13230501414238517127290579)
            ·
              refine ⟨19845752121357775690935869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13230501414238517127290579 19845752121357775690935869)
              ·
                refine ⟨7442157045509165884100951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19845752121357775690935869 7442157045509165884100951)
                ·
                  refine ⟨11163235568263748826151427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7442157045509165884100951 11163235568263748826151427)
                  ·
                    refine ⟨16744853352395623239227141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11163235568263748826151427 16744853352395623239227141)
                    ·
                      refine ⟨3139660003574179357355089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16744853352395623239227141 3139660003574179357355089)
                      ·
                        rfl

theorem cell23_6114466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_6114466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114466 prefixEnd_6114466 := by exact prefixLift 6114466
  have htrace : WordTrace (prefixWord ++ tailWord_6114466) baseStart_6114466 baseEnd_6114466 := by
    simpa [prefixWord, tailWord_6114466, baseEnd_6114466] using wordTrace_append hprefix tailTrace_6114466
  have hstable : (prefixWord ++ tailWord_6114466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114466).length < 2 ^ (prefixWord ++ tailWord_6114466).sum := by decide
  have hdescent : baseEnd_6114466 < baseStart_6114466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114469 : List Nat := [1, 3, 1, 2, 1, 5, 1, 3, 1, 2, 3]
def baseStart_6114469 : Nat := 118140960795 + 6114469 * 2 ^ 59
def prefixEnd_6114469 : Nat := 4983230072969 + 3 ^ 40 * 6114469 * 2
def baseEnd_6114469 : Nat := 3139661544016142845617575

theorem tailTrace_6114469 : CollatzResearch.WordTrace tailWord_6114469 prefixEnd_6114469 3139661544016142845617575 := by
  unfold tailWord_6114469
  simp only [CollatzResearch.WordTrace]
  refine ⟨223013005685330556011874461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148675337123553704007916307 223013005685330556011874461)
  ·
    refine ⟨83629877131998958504452923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223013005685330556011874461 83629877131998958504452923)
    ·
      refine ⟨125444815697998437756679385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83629877131998958504452923 125444815697998437756679385)
      ·
        refine ⟨94083611773498828317509539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125444815697998437756679385 94083611773498828317509539)
        ·
          refine ⟨141125417660248242476264309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94083611773498828317509539 141125417660248242476264309)
          ·
            refine ⟨13230507905648272732149779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141125417660248242476264309 13230507905648272732149779)
            ·
              refine ⟨19845761858472409098224669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13230507905648272732149779 19845761858472409098224669)
              ·
                refine ⟨7442160696927153411834251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19845761858472409098224669 7442160696927153411834251)
                ·
                  refine ⟨11163241045390730117751377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7442160696927153411834251 11163241045390730117751377)
                  ·
                    refine ⟨8372430784043047588313533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11163241045390730117751377 8372430784043047588313533)
                    ·
                      refine ⟨3139661544016142845617575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8372430784043047588313533 3139661544016142845617575)
                      ·
                        rfl

theorem cell23_6114469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_6114469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114469 prefixEnd_6114469 := by exact prefixLift 6114469
  have htrace : WordTrace (prefixWord ++ tailWord_6114469) baseStart_6114469 baseEnd_6114469 := by
    simpa [prefixWord, tailWord_6114469, baseEnd_6114469] using wordTrace_append hprefix tailTrace_6114469
  have hstable : (prefixWord ++ tailWord_6114469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114469).length < 2 ^ (prefixWord ++ tailWord_6114469).sum := by decide
  have hdescent : baseEnd_6114469 < baseStart_6114469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114496 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 1, 2, 4]
def baseStart_6114496 : Nat := 118140960795 + 6114496 * 2 ^ 59
def prefixEnd_6114496 : Nat := 4983230072969 + 3 ^ 40 * 6114496 * 2
def baseEnd_6114496 : Nat := 3139675407993814239979951

theorem tailTrace_6114496 : CollatzResearch.WordTrace tailWord_6114496 prefixEnd_6114496 3139675407993814239979951 := by
  unfold tailWord_6114496
  simp only [CollatzResearch.WordTrace]
  refine ⟨111506995228116369811553671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148675993637488493082071561 111506995228116369811553671)
  ·
    refine ⟨167260492842174554717330507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111506995228116369811553671 167260492842174554717330507)
    ·
      refine ⟨250890739263261832075995761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167260492842174554717330507 250890739263261832075995761)
      ·
        refine ⟨188168054447446374056996821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250890739263261832075995761 188168054447446374056996821)
        ·
          refine ⟨4410188776112024391960863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 188168054447446374056996821 4410188776112024391960863)
          ·
            refine ⟨6615283164168036587941295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4410188776112024391960863 6615283164168036587941295)
            ·
              refine ⟨9922924746252054881911943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6615283164168036587941295 9922924746252054881911943)
              ·
                refine ⟨14884387119378082322867915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9922924746252054881911943 14884387119378082322867915)
                ·
                  refine ⟨22326580679067123484301873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14884387119378082322867915 22326580679067123484301873)
                  ·
                    refine ⟨16744935509300342613226405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22326580679067123484301873 16744935509300342613226405)
                    ·
                      refine ⟨3139675407993814239979951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16744935509300342613226405 3139675407993814239979951)
                      ·
                        rfl

theorem cell23_6114496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 1, 2, 4].length) (baseStart_6114496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114496 prefixEnd_6114496 := by exact prefixLift 6114496
  have htrace : WordTrace (prefixWord ++ tailWord_6114496) baseStart_6114496 baseEnd_6114496 := by
    simpa [prefixWord, tailWord_6114496, baseEnd_6114496] using wordTrace_append hprefix tailTrace_6114496
  have hstable : (prefixWord ++ tailWord_6114496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114496).length < 2 ^ (prefixWord ++ tailWord_6114496).sum := by decide
  have hdescent : baseEnd_6114496 < baseStart_6114496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114505 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 3, 5, 4]
def baseStart_6114505 : Nat := 118140960795 + 6114505 * 2 ^ 59
def prefixEnd_6114505 : Nat := 4983230072969 + 3 ^ 40 * 6114505 * 2
def baseEnd_6114505 : Nat := 3139680029319704704767409

theorem tailTrace_6114505 : CollatzResearch.WordTrace tailWord_6114505 prefixEnd_6114505 3139680029319704704767409 := by
  unfold tailWord_6114505
  simp only [CollatzResearch.WordTrace]
  refine ⟨223014318713200134160184969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148676212475466756106789979 223014318713200134160184969)
  ·
    refine ⟨167260739034900100620138727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223014318713200134160184969 167260739034900100620138727)
    ·
      refine ⟨250891108552350150930208091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167260739034900100620138727 250891108552350150930208091)
      ·
        refine ⟨376336662828525226395312137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250891108552350150930208091 376336662828525226395312137)
        ·
          refine ⟨282252497121393919796484103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376336662828525226395312137 282252497121393919796484103)
          ·
            refine ⟨423378745682090879694726155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282252497121393919796484103 423378745682090879694726155)
            ·
              refine ⟨635068118523136319542089233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423378745682090879694726155 635068118523136319542089233)
              ·
                refine ⟨476301088892352239656566925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635068118523136319542089233 476301088892352239656566925)
                ·
                  refine ⟨178612908334632089871212597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 476301088892352239656566925 178612908334632089871212597)
                  ·
                    refine ⟨16744960156371758425426181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 178612908334632089871212597 16744960156371758425426181)
                    ·
                      refine ⟨3139680029319704704767409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16744960156371758425426181 3139680029319704704767409)
                      ·
                        rfl

theorem cell23_6114505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_6114505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114505 prefixEnd_6114505 := by exact prefixLift 6114505
  have htrace : WordTrace (prefixWord ++ tailWord_6114505) baseStart_6114505 baseEnd_6114505 := by
    simpa [prefixWord, tailWord_6114505, baseEnd_6114505] using wordTrace_append hprefix tailTrace_6114505
  have hstable : (prefixWord ++ tailWord_6114505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114505).length < 2 ^ (prefixWord ++ tailWord_6114505).sum := by decide
  have hdescent : baseEnd_6114505 < baseStart_6114505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114649 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 2, 2, 3]
def baseStart_6114649 : Nat := 118140960795 + 6114649 * 2 ^ 59
def prefixEnd_6114649 : Nat := 4983230072969 + 3 ^ 40 * 6114649 * 2
def baseEnd_6114649 : Nat := 3139753970533952141366747

theorem tailTrace_6114649 : CollatzResearch.WordTrace tailWord_6114649 prefixEnd_6114649 3139753970533952141366747 := by
  unfold tailWord_6114649
  simp only [CollatzResearch.WordTrace]
  refine ⟨223019570824678446753427001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148679713883118964502284667 223019570824678446753427001)
  ·
    refine ⟨167264678118508835065070251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223019570824678446753427001 167264678118508835065070251)
    ·
      refine ⟨250897017177763252597605377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167264678118508835065070251 250897017177763252597605377)
      ·
        refine ⟨188172762883322439448204033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250897017177763252597605377 188172762883322439448204033)
        ·
          refine ⟨141129572162491829586153025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188172762883322439448204033 141129572162491829586153025)
          ·
            refine ⟨105847179121868872189614769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141129572162491829586153025 105847179121868872189614769)
            ·
              refine ⟨79385384341401654142211077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105847179121868872189614769 79385384341401654142211077)
              ·
                refine ⟨14884759564012810151664577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79385384341401654142211077 14884759564012810151664577)
                ·
                  refine ⟨11163569673009607613748433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14884759564012810151664577 11163569673009607613748433)
                  ·
                    refine ⟨8372677254757205710311325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11163569673009607613748433 8372677254757205710311325)
                    ·
                      refine ⟨3139753970533952141366747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8372677254757205710311325 3139753970533952141366747)
                      ·
                        rfl

theorem cell23_6114649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_6114649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114649 prefixEnd_6114649 := by exact prefixLift 6114649
  have htrace : WordTrace (prefixWord ++ tailWord_6114649) baseStart_6114649 baseEnd_6114649 := by
    simpa [prefixWord, tailWord_6114649, baseEnd_6114649] using wordTrace_append hprefix tailTrace_6114649
  have hstable : (prefixWord ++ tailWord_6114649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114649).length < 2 ^ (prefixWord ++ tailWord_6114649).sum := by decide
  have hdescent : baseEnd_6114649 < baseStart_6114649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114656 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 3, 4]
def baseStart_6114656 : Nat := 118140960795 + 6114656 * 2 ^ 59
def prefixEnd_6114656 : Nat := 4983230072969 + 3 ^ 40 * 6114656 * 2
def baseEnd_6114656 : Nat := 1046585854966177871326405

theorem tailTrace_6114656 : CollatzResearch.WordTrace tailWord_6114656 prefixEnd_6114656 1046585854966177871326405 := by
  unfold tailWord_6114656
  simp only [CollatzResearch.WordTrace]
  refine ⟨111509913067826543474465911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148679884090435391299287881 111509913067826543474465911)
  ·
    refine ⟨167264869601739815211698867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111509913067826543474465911 167264869601739815211698867)
    ·
      refine ⟨250897304402609722817548301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167264869601739815211698867 250897304402609722817548301)
      ·
        refine ⟨94086489150978646056580613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250897304402609722817548301 94086489150978646056580613)
        ·
          refine ⟨17641216715808496135608865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94086489150978646056580613 17641216715808496135608865)
          ·
            refine ⟨13230912536856372101706649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17641216715808496135608865 13230912536856372101706649)
            ·
              refine ⟨9923184402642279076279987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13230912536856372101706649 9923184402642279076279987)
              ·
                refine ⟨14884776603963418614419981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9923184402642279076279987 14884776603963418614419981)
                ·
                  refine ⟨5581791226486281980407493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14884776603963418614419981 5581791226486281980407493)
                  ·
                    refine ⟨1046585854966177871326405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5581791226486281980407493 1046585854966177871326405)
                    ·
                      rfl

theorem cell23_6114656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 3, 4].length) (baseStart_6114656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114656 prefixEnd_6114656 := by exact prefixLift 6114656
  have htrace : WordTrace (prefixWord ++ tailWord_6114656) baseStart_6114656 baseEnd_6114656 := by
    simpa [prefixWord, tailWord_6114656, baseEnd_6114656] using wordTrace_append hprefix tailTrace_6114656
  have hstable : (prefixWord ++ tailWord_6114656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114656).length < 2 ^ (prefixWord ++ tailWord_6114656).sum := by decide
  have hdescent : baseEnd_6114656 < baseStart_6114656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114672 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 6]
def baseStart_6114672 : Nat := 118140960795 + 6114672 * 2 ^ 59
def prefixEnd_6114672 : Nat := 4983230072969 + 3 ^ 40 * 6114672 * 2
def baseEnd_6114672 : Nat := 3139765780589005551379141

theorem tailTrace_6114672 : CollatzResearch.WordTrace tailWord_6114672 prefixEnd_6114672 3139765780589005551379141 := by
  unfold tailWord_6114672
  simp only [CollatzResearch.WordTrace]
  refine ⟨111510204851797560840757135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148680273135730081121009513 111510204851797560840757135)
  ·
    refine ⟨167265307277696341261135703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111510204851797560840757135 167265307277696341261135703)
    ·
      refine ⟨250897960916544511891703555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167265307277696341261135703 250897960916544511891703555)
      ·
        refine ⟨376346941374816767837555333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250897960916544511891703555 376346941374816767837555333)
        ·
          refine ⟨70565051507778143969541625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 376346941374816767837555333 70565051507778143969541625)
          ·
            refine ⟨52923788630833607977156219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70565051507778143969541625 52923788630833607977156219)
            ·
              refine ⟨79385682946250411965734329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52923788630833607977156219 79385682946250411965734329)
              ·
                refine ⟨59539262209687808974300747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79385682946250411965734329 59539262209687808974300747)
                ·
                  refine ⟨89308893314531713461451121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59539262209687808974300747 89308893314531713461451121)
                  ·
                    refine ⟨66981669985898785096088341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89308893314531713461451121 66981669985898785096088341)
                    ·
                      refine ⟨3139765780589005551379141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66981669985898785096088341 3139765780589005551379141)
                      ·
                        rfl

theorem cell23_6114672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_6114672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114672 prefixEnd_6114672 := by exact prefixLift 6114672
  have htrace : WordTrace (prefixWord ++ tailWord_6114672) baseStart_6114672 baseEnd_6114672 := by
    simpa [prefixWord, tailWord_6114672, baseEnd_6114672] using wordTrace_append hprefix tailTrace_6114672
  have hstable : (prefixWord ++ tailWord_6114672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114672).length < 2 ^ (prefixWord ++ tailWord_6114672).sum := by decide
  have hdescent : baseEnd_6114672 < baseStart_6114672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114699 : List Nat := [1, 1, 1, 1, 4, 3, 1, 5, 1, 5]
def baseStart_6114699 : Nat := 118140960795 + 6114699 * 2 ^ 59
def prefixEnd_6114699 : Nat := 4983230072969 + 3 ^ 40 * 6114699 * 2
def baseEnd_6114699 : Nat := 1046593214855558981913839

theorem tailTrace_6114699 : CollatzResearch.WordTrace tailWord_6114699 prefixEnd_6114699 1046593214855558981913839 := by
  unfold tailWord_6114699
  simp only [CollatzResearch.WordTrace]
  refine ⟨223021394474497305292747151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148680929649664870195164767 223021394474497305292747151)
  ·
    refine ⟨334532091711745957939120727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223021394474497305292747151 334532091711745957939120727)
    ·
      refine ⟨501798137567618936908681091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334532091711745957939120727 501798137567618936908681091)
      ·
        refine ⟨752697206351428405363021637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501798137567618936908681091 752697206351428405363021637)
        ·
          refine ⟨141130726190892826005566557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 752697206351428405363021637 141130726190892826005566557)
          ·
            refine ⟨52924022321584809752087459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141130726190892826005566557 52924022321584809752087459)
            ·
              refine ⟨79386033482377214628131189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52924022321584809752087459 79386033482377214628131189)
              ·
                refine ⟨7442440638972863871387299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79386033482377214628131189 7442440638972863871387299)
                ·
                  refine ⟨11163660958459295807080949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7442440638972863871387299 11163660958459295807080949)
                  ·
                    refine ⟨1046593214855558981913839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11163660958459295807080949 1046593214855558981913839)
                    ·
                      rfl

theorem cell23_6114699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 5].length) (baseStart_6114699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114699 prefixEnd_6114699 := by exact prefixLift 6114699
  have htrace : WordTrace (prefixWord ++ tailWord_6114699) baseStart_6114699 baseEnd_6114699 := by
    simpa [prefixWord, tailWord_6114699, baseEnd_6114699] using wordTrace_append hprefix tailTrace_6114699
  have hstable : (prefixWord ++ tailWord_6114699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114699).length < 2 ^ (prefixWord ++ tailWord_6114699).sum := by decide
  have hdescent : baseEnd_6114699 < baseStart_6114699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114713 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 3, 1, 3]
def baseStart_6114713 : Nat := 118140960795 + 6114713 * 2 ^ 59
def prefixEnd_6114713 : Nat := 4983230072969 + 3 ^ 40 * 6114713 * 2
def baseEnd_6114713 : Nat := 3139786833295839890966453

theorem tailTrace_6114713 : CollatzResearch.WordTrace tailWord_6114713 prefixEnd_6114713 3139786833295839890966453 := by
  unfold tailWord_6114713
  simp only [CollatzResearch.WordTrace]
  refine ⟨223021905096446585683756793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148681270064297723789171195 223021905096446585683756793)
  ·
    refine ⟨167266428822334939262817595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223021905096446585683756793 167266428822334939262817595)
    ·
      refine ⟨250899643233502408894226393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167266428822334939262817595 250899643233502408894226393)
      ·
        refine ⟨188174732425126806670669795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250899643233502408894226393 188174732425126806670669795)
        ·
          refine ⟨282262098637690210006004693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188174732425126806670669795 282262098637690210006004693)
          ·
            refine ⟨6615517936820864297015735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 282262098637690210006004693 6615517936820864297015735)
            ·
              refine ⟨9923276905231296445523603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6615517936820864297015735 9923276905231296445523603)
              ·
                refine ⟨14884915357846944668285405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9923276905231296445523603 14884915357846944668285405)
                ·
                  refine ⟨5581843259192604250607027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14884915357846944668285405 5581843259192604250607027)
                  ·
                    refine ⟨8372764888788906375910541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5581843259192604250607027 8372764888788906375910541)
                    ·
                      refine ⟨3139786833295839890966453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8372764888788906375910541 3139786833295839890966453)
                      ·
                        rfl

theorem cell23_6114713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_6114713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114713 prefixEnd_6114713 := by exact prefixLift 6114713
  have htrace : WordTrace (prefixWord ++ tailWord_6114713) baseStart_6114713 baseEnd_6114713 := by
    simpa [prefixWord, tailWord_6114713, baseEnd_6114713] using wordTrace_append hprefix tailTrace_6114713
  have hstable : (prefixWord ++ tailWord_6114713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114713).length < 2 ^ (prefixWord ++ tailWord_6114713).sum := by decide
  have hdescent : baseEnd_6114713 < baseStart_6114713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114733 : List Nat := [1, 5, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_6114733 : Nat := 118140960795 + 6114733 * 2 ^ 59
def prefixEnd_6114733 : Nat := 4983230072969 + 3 ^ 40 * 6114733 * 2
def baseEnd_6114733 : Nat := 1046599034302976604238787

theorem tailTrace_6114733 : CollatzResearch.WordTrace tailWord_6114733 prefixEnd_6114733 1046599034302976604238787 := by
  unfold tailWord_6114733
  simp only [CollatzResearch.WordTrace]
  refine ⟨223022634556374129099484853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148681756370916086066323235 223022634556374129099484853)
  ·
    refine ⟨20908371989660074603076705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223022634556374129099484853 20908371989660074603076705)
    ·
      refine ⟨15681278992245055952307529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20908371989660074603076705 15681278992245055952307529)
      ·
        refine ⟨11760959244183791964230647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15681278992245055952307529 11760959244183791964230647)
        ·
          refine ⟨17641438866275687946345971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11760959244183791964230647 17641438866275687946345971)
          ·
            refine ⟨26462158299413531919518957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17641438866275687946345971 26462158299413531919518957)
            ·
              refine ⟨9923309362280074469819609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26462158299413531919518957 9923309362280074469819609)
              ·
                refine ⟨7442482021710055852364707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9923309362280074469819609 7442482021710055852364707)
                ·
                  refine ⟨11163723032565083778547061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7442482021710055852364707 11163723032565083778547061)
                  ·
                    refine ⟨1046599034302976604238787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11163723032565083778547061 1046599034302976604238787)
                    ·
                      rfl

theorem cell23_6114733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_6114733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114733 prefixEnd_6114733 := by exact prefixLift 6114733
  have htrace : WordTrace (prefixWord ++ tailWord_6114733) baseStart_6114733 baseEnd_6114733 := by
    simpa [prefixWord, tailWord_6114733, baseEnd_6114733] using wordTrace_append hprefix tailTrace_6114733
  have hstable : (prefixWord ++ tailWord_6114733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114733).length < 2 ^ (prefixWord ++ tailWord_6114733).sum := by decide
  have hdescent : baseEnd_6114733 < baseStart_6114733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114814 : List Nat := [4, 2, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_6114814 : Nat := 118140960795 + 6114814 * 2 ^ 59
def prefixEnd_6114814 : Nat := 4983230072969 + 3 ^ 40 * 6114814 * 2
def baseEnd_6114814 : Nat := 1046612898280647998601163

theorem tailTrace_6114814 : CollatzResearch.WordTrace tailWord_6114814 prefixEnd_6114814 1046612898280647998601163 := by
  unfold tailWord_6114814
  simp only [CollatzResearch.WordTrace]
  refine ⟨27878198608635084991647937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148683725912720453288788997 27878198608635084991647937)
  ·
    refine ⟨20908648956476313743735953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27878198608635084991647937 20908648956476313743735953)
    ·
      refine ⟨15681486717357235307801965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20908648956476313743735953 15681486717357235307801965)
      ·
        refine ⟨5880557519008963240425737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15681486717357235307801965 5880557519008963240425737)
        ·
          refine ⟨4410418139256722430319303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5880557519008963240425737 4410418139256722430319303)
          ·
            refine ⟨6615627208885083645478955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4410418139256722430319303 6615627208885083645478955)
            ·
              refine ⟨9923440813327625468218433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6615627208885083645478955 9923440813327625468218433)
              ·
                refine ⟨7442580609995719101163825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9923440813327625468218433 7442580609995719101163825)
                ·
                  refine ⟨5581935457496789325872869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7442580609995719101163825 5581935457496789325872869)
                  ·
                    refine ⟨1046612898280647998601163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5581935457496789325872869 1046612898280647998601163)
                    ·
                      rfl

theorem cell23_6114814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_6114814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114814 prefixEnd_6114814 := by exact prefixLift 6114814
  have htrace : WordTrace (prefixWord ++ tailWord_6114814) baseStart_6114814 baseEnd_6114814 := by
    simpa [prefixWord, tailWord_6114814, baseEnd_6114814] using wordTrace_append hprefix tailTrace_6114814
  have hstable : (prefixWord ++ tailWord_6114814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114814).length < 2 ^ (prefixWord ++ tailWord_6114814).sum := by decide
  have hdescent : baseEnd_6114814 < baseStart_6114814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114820 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_6114820 : Nat := 118140960795 + 6114820 * 2 ^ 59
def prefixEnd_6114820 : Nat := 4983230072969 + 3 ^ 40 * 6114820 * 2
def baseEnd_6114820 : Nat := 3139841775725870972328461

theorem tailTrace_6114820 : CollatzResearch.WordTrace tailWord_6114820 prefixEnd_6114820 3139841775725870972328461 := by
  unfold tailWord_6114820
  simp only [CollatzResearch.WordTrace]
  refine ⟨111512903853529471478950957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148683871804705961971934609 111512903853529471478950957)
  ·
    refine ⟨41817338945073551804606609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111512903853529471478950957 41817338945073551804606609)
    ·
      refine ⟨31363004208805163853454957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41817338945073551804606609 31363004208805163853454957)
      ·
        refine ⟨11761126578301936445045609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31363004208805163853454957 11761126578301936445045609)
        ·
          refine ⟨8820844933726452333784207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11761126578301936445045609 8820844933726452333784207)
          ·
            refine ⟨13231267400589678500676311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8820844933726452333784207 13231267400589678500676311)
            ·
              refine ⟨19846901100884517751014467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13231267400589678500676311 19846901100884517751014467)
              ·
                refine ⟨29770351651326776626521701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19846901100884517751014467 29770351651326776626521701)
                ·
                  refine ⟨5581940934623770617472819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29770351651326776626521701 5581940934623770617472819)
                  ·
                    refine ⟨8372911401935655926209229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5581940934623770617472819 8372911401935655926209229)
                    ·
                      refine ⟨3139841775725870972328461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8372911401935655926209229 3139841775725870972328461)
                      ·
                        rfl

theorem cell23_6114820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_6114820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114820 prefixEnd_6114820 := by exact prefixLift 6114820
  have htrace : WordTrace (prefixWord ++ tailWord_6114820) baseStart_6114820 baseEnd_6114820 := by
    simpa [prefixWord, tailWord_6114820, baseEnd_6114820] using wordTrace_append hprefix tailTrace_6114820
  have hstable : (prefixWord ++ tailWord_6114820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114820).length < 2 ^ (prefixWord ++ tailWord_6114820).sum := by decide
  have hdescent : baseEnd_6114820 < baseStart_6114820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114956 : List Nat := [2, 2, 1, 2, 1, 1, 3, 5, 6]
def baseStart_6114956 : Nat := 118140960795 + 6114956 * 2 ^ 59
def prefixEnd_6114956 : Nat := 4983230072969 + 3 ^ 40 * 6114956 * 2
def baseEnd_6114956 : Nat := 348879067677209160025315

theorem tailTrace_6114956 : CollatzResearch.WordTrace tailWord_6114956 prefixEnd_6114956 348879067677209160025315 := by
  unfold tailWord_6114956
  simp only [CollatzResearch.WordTrace]
  refine ⟨111515384017283119092426361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148687178689710825456568481 111515384017283119092426361)
  ·
    refine ⟨83636538012962339319319771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111515384017283119092426361 83636538012962339319319771)
    ·
      refine ⟨125454807019443508978979657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83636538012962339319319771 125454807019443508978979657)
      ·
        refine ⟨94091105264582631734234743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125454807019443508978979657 94091105264582631734234743)
        ·
          refine ⟨141136657896873947601352115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94091105264582631734234743 141136657896873947601352115)
          ·
            refine ⟨211704986845310921402028173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141136657896873947601352115 211704986845310921402028173)
            ·
              refine ⟨79389370066991595525760565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211704986845310921402028173 79389370066991595525760565)
              ·
                refine ⟨7442753443780462080540053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79389370066991595525760565 7442753443780462080540053)
                ·
                  refine ⟨348879067677209160025315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7442753443780462080540053 348879067677209160025315)
                  ·
                    rfl

theorem cell23_6114956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 6].length) (baseStart_6114956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114956 prefixEnd_6114956 := by exact prefixLift 6114956
  have htrace : WordTrace (prefixWord ++ tailWord_6114956) baseStart_6114956 baseEnd_6114956 := by
    simpa [prefixWord, tailWord_6114956, baseEnd_6114956] using wordTrace_append hprefix tailTrace_6114956
  have hstable : (prefixWord ++ tailWord_6114956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114956).length < 2 ^ (prefixWord ++ tailWord_6114956).sum := by decide
  have hdescent : baseEnd_6114956 < baseStart_6114956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114977 : List Nat := [1, 2, 3, 3, 2, 2, 2, 3, 1, 4]
def baseStart_6114977 : Nat := 118140960795 + 6114977 * 2 ^ 59
def prefixEnd_6114977 : Nat := 4983230072969 + 3 ^ 40 * 6114977 * 2
def baseEnd_6114977 : Nat := 1046640797396208952688413

theorem tailTrace_6114977 : CollatzResearch.WordTrace tailWord_6114977 prefixEnd_6114977 1046640797396208952688413 := by
  unfold tailWord_6114977
  simp only [CollatzResearch.WordTrace]
  refine ⟨223031533967490158771367185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148687689311660105847578123 223031533967490158771367185)
  ·
    refine ⟨167273650475617619078525389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223031533967490158771367185 167273650475617619078525389)
    ·
      refine ⟨62727618928356607154447021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167273650475617619078525389 62727618928356607154447021)
      ·
        refine ⟨23522857098133727682917633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62727618928356607154447021 23522857098133727682917633)
        ·
          refine ⟨17642142823600295762188225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23522857098133727682917633 17642142823600295762188225)
          ·
            refine ⟨13231607117700221821641169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17642142823600295762188225 13231607117700221821641169)
            ·
              refine ⟨9923705338275166366230877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13231607117700221821641169 9923705338275166366230877)
              ·
                refine ⟨3721389501853187387336579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9923705338275166366230877 3721389501853187387336579)
                ·
                  refine ⟨5582084252779781081004869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721389501853187387336579 5582084252779781081004869)
                  ·
                    refine ⟨1046640797396208952688413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5582084252779781081004869 1046640797396208952688413)
                    ·
                      rfl

theorem cell23_6114977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_6114977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114977 prefixEnd_6114977 := by exact prefixLift 6114977
  have htrace : WordTrace (prefixWord ++ tailWord_6114977) baseStart_6114977 baseEnd_6114977 := by
    simpa [prefixWord, tailWord_6114977, baseEnd_6114977] using wordTrace_append hprefix tailTrace_6114977
  have hstable : (prefixWord ++ tailWord_6114977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114977).length < 2 ^ (prefixWord ++ tailWord_6114977).sum := by decide
  have hdescent : baseEnd_6114977 < baseStart_6114977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6114990 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 8]
def baseStart_6114990 : Nat := 118140960795 + 6114990 * 2 ^ 59
def prefixEnd_6114990 : Nat := 4983230072969 + 3 ^ 40 * 6114990 * 2
def baseEnd_6114990 : Nat := 348881007493015034133631

theorem tailTrace_6114990 : CollatzResearch.WordTrace tailWord_6114990 prefixEnd_6114990 348881007493015034133631 := by
  unfold tailWord_6114990
  simp only [CollatzResearch.WordTrace]
  refine ⟨27879001014555382748948803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148688005410962041327726949 27879001014555382748948803)
  ·
    refine ⟨41818501521833074123423205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27879001014555382748948803 41818501521833074123423205)
    ·
      refine ⟨7840969035343701398141851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41818501521833074123423205 7840969035343701398141851)
      ·
        refine ⟨11761453553015552097212777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7840969035343701398141851 11761453553015552097212777)
        ·
          refine ⟨8821090164761664072909583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11761453553015552097212777 8821090164761664072909583)
          ·
            refine ⟨13231635247142496109364375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8821090164761664072909583 13231635247142496109364375)
            ·
              refine ⟨19847452870713744164046563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13231635247142496109364375 19847452870713744164046563)
              ·
                refine ⟨29771179306070616246069845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19847452870713744164046563 29771179306070616246069845)
                ·
                  refine ⟨348881007493015034133631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29771179306070616246069845 348881007493015034133631)
                  ·
                    rfl

theorem cell23_6114990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_6114990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6114990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6114990 prefixEnd_6114990 := by exact prefixLift 6114990
  have htrace : WordTrace (prefixWord ++ tailWord_6114990) baseStart_6114990 baseEnd_6114990 := by
    simpa [prefixWord, tailWord_6114990, baseEnd_6114990] using wordTrace_append hprefix tailTrace_6114990
  have hstable : (prefixWord ++ tailWord_6114990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6114990).length < 2 ^ (prefixWord ++ tailWord_6114990).sum := by decide
  have hdescent : baseEnd_6114990 < baseStart_6114990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6114990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115033 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 4, 4]
def baseStart_6115033 : Nat := 118140960795 + 6115033 * 2 ^ 59
def prefixEnd_6115033 : Nat := 4983230072969 + 3 ^ 40 * 6115033 * 2
def baseEnd_6115033 : Nat := 1046650382368426212988327

theorem tailTrace_6115033 : CollatzResearch.WordTrace tailWord_6115033 prefixEnd_6115033 1046650382368426212988327 := by
  unfold tailWord_6115033
  simp only [CollatzResearch.WordTrace]
  refine ⟨223033576455287280335405753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148689050970191520223603835 223033576455287280335405753)
  ·
    refine ⟨167275182341465460251554315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223033576455287280335405753 167275182341465460251554315)
    ·
      refine ⟨250912773512198190377331473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167275182341465460251554315 250912773512198190377331473)
      ·
        refine ⟨188184580134148642782998605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250912773512198190377331473 188184580134148642782998605)
        ·
          refine ⟨70569217550305741043624477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188184580134148642782998605 70569217550305741043624477)
          ·
            refine ⟨26463456581364652891359179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70569217550305741043624477 26463456581364652891359179)
            ·
              refine ⟨39695184872046979337038769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26463456581364652891359179 39695184872046979337038769)
              ·
                refine ⟨29771388654035234502779077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39695184872046979337038769 29771388654035234502779077)
                ·
                  refine ⟨5582135372631606469271077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29771388654035234502779077 5582135372631606469271077)
                  ·
                    refine ⟨1046650382368426212988327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5582135372631606469271077 1046650382368426212988327)
                    ·
                      rfl

theorem cell23_6115033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 4].length) (baseStart_6115033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115033 prefixEnd_6115033 := by exact prefixLift 6115033
  have htrace : WordTrace (prefixWord ++ tailWord_6115033) baseStart_6115033 baseEnd_6115033 := by
    simpa [prefixWord, tailWord_6115033, baseEnd_6115033] using wordTrace_append hprefix tailTrace_6115033
  have hstable : (prefixWord ++ tailWord_6115033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115033).length < 2 ^ (prefixWord ++ tailWord_6115033).sum := by decide
  have hdescent : baseEnd_6115033 < baseStart_6115033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115034 : List Nat := [3, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3]
def baseStart_6115034 : Nat := 118140960795 + 6115034 * 2 ^ 59
def prefixEnd_6115034 : Nat := 4983230072969 + 3 ^ 40 * 6115034 * 2
def baseEnd_6115034 : Nat := 3139951660585933135052477

theorem tailTrace_6115034 : CollatzResearch.WordTrace tailWord_6115034 prefixEnd_6115034 3139951660585933135052477 := by
  unfold tailWord_6115034
  simp only [CollatzResearch.WordTrace]
  refine ⟨55758403232070914376548039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148689075285522438337461437 55758403232070914376548039)
  ·
    refine ⟨83637604848106371564822059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55758403232070914376548039 83637604848106371564822059)
    ·
      refine ⟨125456407272159557347233089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83637604848106371564822059 125456407272159557347233089)
      ·
        refine ⟨94092305454119668010424817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125456407272159557347233089 94092305454119668010424817)
        ·
          refine ⟨70569229090589751007818613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94092305454119668010424817 70569229090589751007818613)
          ·
            refine ⟨6615865227242789156982995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70569229090589751007818613 6615865227242789156982995)
            ·
              refine ⟨9923797840864183735474493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6615865227242789156982995 9923797840864183735474493)
              ·
                refine ⟨3721424190324068900802935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9923797840864183735474493 3721424190324068900802935)
                ·
                  refine ⟨5582136285486103351204403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721424190324068900802935 5582136285486103351204403)
                  ·
                    refine ⟨8373204428229155026806605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5582136285486103351204403 8373204428229155026806605)
                    ·
                      refine ⟨3139951660585933135052477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8373204428229155026806605 3139951660585933135052477)
                      ·
                        rfl

theorem cell23_6115034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_6115034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115034 prefixEnd_6115034 := by exact prefixLift 6115034
  have htrace : WordTrace (prefixWord ++ tailWord_6115034) baseStart_6115034 baseEnd_6115034 := by
    simpa [prefixWord, tailWord_6115034, baseEnd_6115034] using wordTrace_append hprefix tailTrace_6115034
  have hstable : (prefixWord ++ tailWord_6115034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115034).length < 2 ^ (prefixWord ++ tailWord_6115034).sum := by decide
  have hdescent : baseEnd_6115034 < baseStart_6115034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115040 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 5, 2, 2]
def baseStart_6115040 : Nat := 118140960795 + 6115040 * 2 ^ 59
def prefixEnd_6115040 : Nat := 4983230072969 + 3 ^ 40 * 6115040 * 2
def baseEnd_6115040 : Nat := 3139954741469860111577449

theorem tailTrace_6115040 : CollatzResearch.WordTrace tailWord_6115040 prefixEnd_6115040 3139954741469860111577449 := by
  unfold tailWord_6115040
  simp only [CollatzResearch.WordTrace]
  refine ⟨111516915883130960265455287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148689221177507947020607049 111516915883130960265455287)
  ·
    refine ⟨167275373824696440398182931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111516915883130960265455287 167275373824696440398182931)
    ·
      refine ⟨250913060737044660597274397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167275373824696440398182931 250913060737044660597274397)
      ·
        refine ⟨94092397776391747723977899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250913060737044660597274397 94092397776391747723977899)
        ·
          refine ⟨141138596664587621585966849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94092397776391747723977899 141138596664587621585966849)
          ·
            refine ⟨105853947498440716189475137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141138596664587621585966849 105853947498440716189475137)
            ·
              refine ⟨79390460623830537142106353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105853947498440716189475137 79390460623830537142106353)
              ·
                refine ⟨59542845467872902856579765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79390460623830537142106353 59542845467872902856579765)
                ·
                  refine ⟨5582141762613084642804353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59542845467872902856579765 5582141762613084642804353)
                  ·
                    refine ⟨4186606321959813482103265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5582141762613084642804353 4186606321959813482103265)
                    ·
                      refine ⟨3139954741469860111577449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4186606321959813482103265 3139954741469860111577449)
                      ·
                        rfl

theorem cell23_6115040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_6115040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115040 prefixEnd_6115040 := by exact prefixLift 6115040
  have htrace : WordTrace (prefixWord ++ tailWord_6115040) baseStart_6115040 baseEnd_6115040 := by
    simpa [prefixWord, tailWord_6115040, baseEnd_6115040] using wordTrace_append hprefix tailTrace_6115040
  have hstable : (prefixWord ++ tailWord_6115040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115040).length < 2 ^ (prefixWord ++ tailWord_6115040).sum := by decide
  have hdescent : baseEnd_6115040 < baseStart_6115040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115053 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_6115053 : Nat := 118140960795 + 6115053 * 2 ^ 59
def prefixEnd_6115053 : Nat := 4983230072969 + 3 ^ 40 * 6115053 * 2
def baseEnd_6115053 : Nat := 3139961416718368560714889

theorem tailTrace_6115053 : CollatzResearch.WordTrace tailWord_6115053 prefixEnd_6115053 3139961416718368560714889 := by
  unfold tailWord_6115053
  simp only [CollatzResearch.WordTrace]
  refine ⟨223034305915214823751133813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148689537276809882500755875 223034305915214823751133813)
  ·
    refine ⟨20909466179551389726668795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223034305915214823751133813 20909466179551389726668795)
    ·
      refine ⟨31364199269327084590003193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20909466179551389726668795 31364199269327084590003193)
      ·
        refine ⟨23523149451995313442502395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31364199269327084590003193 23523149451995313442502395)
        ·
          refine ⟨35284724177992970163753593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23523149451995313442502395 35284724177992970163753593)
          ·
            refine ⟨26463543133494727622815195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35284724177992970163753593 26463543133494727622815195)
            ·
              refine ⟨39695314700242091434222793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26463543133494727622815195 39695314700242091434222793)
              ·
                refine ⟨29771486025181568575667095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39695314700242091434222793 29771486025181568575667095)
                ·
                  refine ⟨44657229037772352863500643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29771486025181568575667095 44657229037772352863500643)
                  ·
                    refine ⟨66985843556658529295250965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44657229037772352863500643 66985843556658529295250965)
                    ·
                      refine ⟨3139961416718368560714889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66985843556658529295250965 3139961416718368560714889)
                      ·
                        rfl

theorem cell23_6115053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_6115053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115053 prefixEnd_6115053 := by exact prefixLift 6115053
  have htrace : WordTrace (prefixWord ++ tailWord_6115053) baseStart_6115053 baseEnd_6115053 := by
    simpa [prefixWord, tailWord_6115053, baseEnd_6115053] using wordTrace_append hprefix tailTrace_6115053
  have hstable : (prefixWord ++ tailWord_6115053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115053).length < 2 ^ (prefixWord ++ tailWord_6115053).sum := by decide
  have hdescent : baseEnd_6115053 < baseStart_6115053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115057 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 3, 2, 2]
def baseStart_6115057 : Nat := 118140960795 + 6115057 * 2 ^ 59
def prefixEnd_6115057 : Nat := 4983230072969 + 3 ^ 40 * 6115057 * 2
def baseEnd_6115057 : Nat := 3139963470640986545064871

theorem tailTrace_6115057 : CollatzResearch.WordTrace tailWord_6115057 prefixEnd_6115057 3139963470640986545064871 := by
  unfold tailWord_6115057
  simp only [CollatzResearch.WordTrace]
  refine ⟨223034451807200332434279425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148689634538133554956186283 223034451807200332434279425)
  ·
    refine ⟨167275838855400249325709569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223034451807200332434279425 167275838855400249325709569)
    ·
      refine ⟨125456879141550186994282177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167275838855400249325709569 125456879141550186994282177)
      ·
        refine ⟨94092659356162640245711633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125456879141550186994282177 94092659356162640245711633)
        ·
          refine ⟨70569494517121980184283725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94092659356162640245711633 70569494517121980184283725)
          ·
            refine ⟨26463560443920742569106397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70569494517121980184283725 26463560443920742569106397)
            ·
              refine ⟨9923835166470278463414899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26463560443920742569106397 9923835166470278463414899)
              ·
                refine ⟨14885752749705417695122349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9923835166470278463414899 14885752749705417695122349)
                ·
                  refine ⟨5582157281139531635670881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14885752749705417695122349 5582157281139531635670881)
                  ·
                    refine ⟨4186617960854648726753161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5582157281139531635670881 4186617960854648726753161)
                    ·
                      refine ⟨3139963470640986545064871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4186617960854648726753161 3139963470640986545064871)
                      ·
                        rfl

theorem cell23_6115057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_6115057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115057 prefixEnd_6115057 := by exact prefixLift 6115057
  have htrace : WordTrace (prefixWord ++ tailWord_6115057) baseStart_6115057 baseEnd_6115057 := by
    simpa [prefixWord, tailWord_6115057, baseEnd_6115057] using wordTrace_append hprefix tailTrace_6115057
  have hstable : (prefixWord ++ tailWord_6115057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115057).length < 2 ^ (prefixWord ++ tailWord_6115057).sum := by decide
  have hdescent : baseEnd_6115057 < baseStart_6115057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115066 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6]
def baseStart_6115066 : Nat := 118140960795 + 6115066 * 2 ^ 59
def prefixEnd_6115066 : Nat := 4983230072969 + 3 ^ 40 * 6115066 * 2
def baseEnd_6115066 : Nat := 3139968091966877009852329

theorem tailTrace_6115066 : CollatzResearch.WordTrace tailWord_6115066 prefixEnd_6115066 3139968091966877009852329 := by
  unfold tailWord_6115066
  simp only [CollatzResearch.WordTrace]
  refine ⟨55758695016041931742839263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148689853376111817980904701 55758695016041931742839263)
  ·
    refine ⟨83638042524062897614258895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55758695016041931742839263 83638042524062897614258895)
    ·
      refine ⟨125457063786094346421388343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83638042524062897614258895 125457063786094346421388343)
      ·
        refine ⟨188185595679141519632082515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125457063786094346421388343 188185595679141519632082515)
        ·
          refine ⟨282278393518712279448123773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188185595679141519632082515 282278393518712279448123773)
          ·
            refine ⟨105854397569517104793046415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282278393518712279448123773 105854397569517104793046415)
            ·
              refine ⟨158781596354275657189569623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105854397569517104793046415 158781596354275657189569623)
              ·
                refine ⟨238172394531413485784354435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158781596354275657189569623 238172394531413485784354435)
                ·
                  refine ⟨357258591797120228676531653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238172394531413485784354435 357258591797120228676531653)
                  ·
                    refine ⟨66985985961960042876849685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 357258591797120228676531653 66985985961960042876849685)
                    ·
                      refine ⟨3139968091966877009852329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66985985961960042876849685 3139968091966877009852329)
                      ·
                        rfl

theorem cell23_6115066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_6115066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115066 prefixEnd_6115066 := by exact prefixLift 6115066
  have htrace : WordTrace (prefixWord ++ tailWord_6115066) baseStart_6115066 baseEnd_6115066 := by
    simpa [prefixWord, tailWord_6115066, baseEnd_6115066] using wordTrace_append hprefix tailTrace_6115066
  have hstable : (prefixWord ++ tailWord_6115066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115066).length < 2 ^ (prefixWord ++ tailWord_6115066).sum := by decide
  have hdescent : baseEnd_6115066 < baseStart_6115066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115102 : List Nat := [4, 3, 2, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_6115102 : Nat := 118140960795 + 6115102 * 2 ^ 59
def prefixEnd_6115102 : Nat := 4983230072969 + 3 ^ 40 * 6115102 * 2
def baseEnd_6115102 : Nat := 3139986577270438869002165

theorem tailTrace_6115102 : CollatzResearch.WordTrace tailWord_6115102 prefixEnd_6115102 3139986577270438869002165 := by
  unfold tailWord_6115102
  simp only [CollatzResearch.WordTrace]
  refine ⟨27879511636504663139958445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148690728728024870079778373 27879511636504663139958445)
  ·
    refine ⟨10454816863689248677484417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27879511636504663139958445 10454816863689248677484417)
    ·
      refine ⟨7841112647766936508113313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10454816863689248677484417 7841112647766936508113313)
      ·
        refine ⟨5880834485825202381084985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7841112647766936508113313 5880834485825202381084985)
        ·
          refine ⟨4410625864368901785813739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5880834485825202381084985 4410625864368901785813739)
          ·
            refine ⟨6615938796553352678720609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4410625864368901785813739 6615938796553352678720609)
            ·
              refine ⟨4961954097415014509040457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6615938796553352678720609 4961954097415014509040457)
              ·
                refine ⟨3721465573061260881780343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4961954097415014509040457 3721465573061260881780343)
                ·
                  refine ⟨5582198359591891322670515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721465573061260881780343 5582198359591891322670515)
                  ·
                    refine ⟨8373297539387836984005773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5582198359591891322670515 8373297539387836984005773)
                    ·
                      refine ⟨3139986577270438869002165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8373297539387836984005773 3139986577270438869002165)
                      ·
                        rfl

theorem cell23_6115102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_6115102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115102 prefixEnd_6115102 := by exact prefixLift 6115102
  have htrace : WordTrace (prefixWord ++ tailWord_6115102) baseStart_6115102 baseEnd_6115102 := by
    simpa [prefixWord, tailWord_6115102, baseEnd_6115102] using wordTrace_append hprefix tailTrace_6115102
  have hstable : (prefixWord ++ tailWord_6115102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115102).length < 2 ^ (prefixWord ++ tailWord_6115102).sum := by decide
  have hdescent : baseEnd_6115102 < baseStart_6115102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115108 : List Nat := [2, 3, 1, 3, 2, 3, 2, 2, 1, 2, 2]
def baseStart_6115108 : Nat := 118140960795 + 6115108 * 2 ^ 59
def prefixEnd_6115108 : Nat := 4983230072969 + 3 ^ 40 * 6115108 * 2
def baseEnd_6115108 : Nat := 3139989658154365845527137

theorem tailTrace_6115108 : CollatzResearch.WordTrace tailWord_6115108 prefixEnd_6115108 3139989658154365845527137 := by
  unfold tailWord_6115108
  simp only [CollatzResearch.WordTrace]
  refine ⟨111518155965007784072192989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148690874620010378762923985 111518155965007784072192989)
  ·
    refine ⟨41819308486877919027072371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111518155965007784072192989 41819308486877919027072371)
    ·
      refine ⟨62728962730316878540608557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41819308486877919027072371 62728962730316878540608557)
      ·
        refine ⟨23523361023868829452728209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62728962730316878540608557 23523361023868829452728209)
        ·
          refine ⟨17642520767901622089546157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23523361023868829452728209 17642520767901622089546157)
          ·
            refine ⟨6615945287963108283579809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17642520767901622089546157 6615945287963108283579809)
            ·
              refine ⟨4961958965972331212684857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6615945287963108283579809 4961958965972331212684857)
              ·
                refine ⟨3721469224479248409513643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4961958965972331212684857 3721469224479248409513643)
                ·
                  refine ⟨5582203836718872614270465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721469224479248409513643 5582203836718872614270465)
                  ·
                    refine ⟨4186652877539154460702849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5582203836718872614270465 4186652877539154460702849)
                    ·
                      refine ⟨3139989658154365845527137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4186652877539154460702849 3139989658154365845527137)
                      ·
                        rfl

theorem cell23_6115108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_6115108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115108 prefixEnd_6115108 := by exact prefixLift 6115108
  have htrace : WordTrace (prefixWord ++ tailWord_6115108) baseStart_6115108 baseEnd_6115108 := by
    simpa [prefixWord, tailWord_6115108, baseEnd_6115108] using wordTrace_append hprefix tailTrace_6115108
  have hstable : (prefixWord ++ tailWord_6115108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115108).length < 2 ^ (prefixWord ++ tailWord_6115108).sum := by decide
  have hdescent : baseEnd_6115108 < baseStart_6115108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115124 : List Nat := [2, 5, 1, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_6115124 : Nat := 118140960795 + 6115124 * 2 ^ 59
def prefixEnd_6115124 : Nat := 4983230072969 + 3 ^ 40 * 6115124 * 2
def baseEnd_6115124 : Nat := 3139997873844837782927063

theorem tailTrace_6115124 : CollatzResearch.WordTrace tailWord_6115124 prefixEnd_6115124 3139997873844837782927063 := by
  unfold tailWord_6115124
  simp only [CollatzResearch.WordTrace]
  refine ⟨111518447748978801438484213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148691263665305068584645617 111518447748978801438484213)
  ·
    refine ⟨10454854476466762634857895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111518447748978801438484213 10454854476466762634857895)
    ·
      refine ⟨15682281714700143952286843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10454854476466762634857895 15682281714700143952286843)
      ·
        refine ⟨23523422572050215928430265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15682281714700143952286843 23523422572050215928430265)
        ·
          refine ⟨17642566929037661946322699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23523422572050215928430265 17642566929037661946322699)
          ·
            refine ⟨26463850393556492919484049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17642566929037661946322699 26463850393556492919484049)
            ·
              refine ⟨19847887795167369689613037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26463850393556492919484049 19847887795167369689613037)
              ·
                refine ⟨7442957923187763633604889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19847887795167369689613037 7442957923187763633604889)
                ·
                  refine ⟨5582218442390822725203667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7442957923187763633604889 5582218442390822725203667)
                  ·
                    refine ⟨8373327663586234087805501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5582218442390822725203667 8373327663586234087805501)
                    ·
                      refine ⟨3139997873844837782927063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8373327663586234087805501 3139997873844837782927063)
                      ·
                        rfl

theorem cell23_6115124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_6115124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115124 prefixEnd_6115124 := by exact prefixLift 6115124
  have htrace : WordTrace (prefixWord ++ tailWord_6115124) baseStart_6115124 baseEnd_6115124 := by
    simpa [prefixWord, tailWord_6115124, baseEnd_6115124] using wordTrace_append hprefix tailTrace_6115124
  have hstable : (prefixWord ++ tailWord_6115124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115124).length < 2 ^ (prefixWord ++ tailWord_6115124).sum := by decide
  have hdescent : baseEnd_6115124 < baseStart_6115124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115170 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 7]
def baseStart_6115170 : Nat := 118140960795 + 6115170 * 2 ^ 59
def prefixEnd_6115170 : Nat := 4983230072969 + 3 ^ 40 * 6115170 * 2
def baseEnd_6115170 : Nat := 348891277106104955883539

theorem tailTrace_6115170 : CollatzResearch.WordTrace tailWord_6115170 prefixEnd_6115170 348891277106104955883539 := by
  unfold tailWord_6115170
  simp only [CollatzResearch.WordTrace]
  refine ⟨55759643313947738183285741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148692382170527301822095309 55759643313947738183285741)
  ·
    refine ⟨20909866242730401818732153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55759643313947738183285741 20909866242730401818732153)
    ·
      refine ⟨15682399682047801364049115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20909866242730401818732153 15682399682047801364049115)
      ·
        refine ⟨23523599523071702046073673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15682399682047801364049115 23523599523071702046073673)
        ·
          refine ⟨17642699642303776534555255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23523599523071702046073673 17642699642303776534555255)
          ·
            refine ⟨26464049463455664801832883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17642699642303776534555255 26464049463455664801832883)
            ·
              refine ⟨39696074195183497202749325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26464049463455664801832883 39696074195183497202749325)
              ·
                refine ⟨14886027823193811451030997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39696074195183497202749325 14886027823193811451030997)
                ·
                  refine ⟨348891277106104955883539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14886027823193811451030997 348891277106104955883539)
                  ·
                    rfl

theorem cell23_6115170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_6115170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115170 prefixEnd_6115170 := by exact prefixLift 6115170
  have htrace : WordTrace (prefixWord ++ tailWord_6115170) baseStart_6115170 baseEnd_6115170 := by
    simpa [prefixWord, tailWord_6115170, baseEnd_6115170] using wordTrace_append hprefix tailTrace_6115170
  have hstable : (prefixWord ++ tailWord_6115170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115170).length < 2 ^ (prefixWord ++ tailWord_6115170).sum := by decide
  have hdescent : baseEnd_6115170 < baseStart_6115170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115180 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 3]
def baseStart_6115180 : Nat := 118140960795 + 6115180 * 2 ^ 59
def prefixEnd_6115180 : Nat := 4983230072969 + 3 ^ 40 * 6115180 * 2
def baseEnd_6115180 : Nat := 3140026628761489563826805

theorem tailTrace_6115180 : CollatzResearch.WordTrace tailWord_6115180 prefixEnd_6115180 3140026628761489563826805 := by
  unfold tailWord_6115180
  simp only [CollatzResearch.WordTrace]
  refine ⟨111519468992877362220503497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148692625323836482960671329 111519468992877362220503497)
  ·
    refine ⟨83639601744658021665377623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111519468992877362220503497 83639601744658021665377623)
    ·
      refine ⟨125459402616987032498066435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83639601744658021665377623 125459402616987032498066435)
      ·
        refine ⟨188189103925480548747099653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125459402616987032498066435 188189103925480548747099653)
        ·
          refine ⟨35285456986027602890081185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188189103925480548747099653 35285456986027602890081185)
          ·
            refine ⟨26464092739520702167560889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35285456986027602890081185 26464092739520702167560889)
            ·
              refine ⟨19848069554640526625670667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26464092739520702167560889 19848069554640526625670667)
              ·
                refine ⟨29772104331960789938506001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19848069554640526625670667 29772104331960789938506001)
                ·
                  refine ⟨22329078248970592453879501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29772104331960789938506001 22329078248970592453879501)
                  ·
                    refine ⟨8373404343363972170204813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22329078248970592453879501 8373404343363972170204813)
                    ·
                      refine ⟨3140026628761489563826805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8373404343363972170204813 3140026628761489563826805)
                      ·
                        rfl

theorem cell23_6115180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_6115180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115180 prefixEnd_6115180 := by exact prefixLift 6115180
  have htrace : WordTrace (prefixWord ++ tailWord_6115180) baseStart_6115180 baseEnd_6115180 := by
    simpa [prefixWord, tailWord_6115180, baseEnd_6115180] using wordTrace_append hprefix tailTrace_6115180
  have hstable : (prefixWord ++ tailWord_6115180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115180).length < 2 ^ (prefixWord ++ tailWord_6115180).sum := by decide
  have hdescent : baseEnd_6115180 < baseStart_6115180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115257 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 2, 2, 3]
def baseStart_6115257 : Nat := 118140960795 + 6115257 * 2 ^ 59
def prefixEnd_6115257 : Nat := 4983230072969 + 3 ^ 40 * 6115257 * 2
def baseEnd_6115257 : Nat := 3140066166771885762563951

theorem tailTrace_6115257 : CollatzResearch.WordTrace tailWord_6115257 prefixEnd_6115257 3140066166771885762563951 := by
  unfold tailWord_6115257
  simp only [CollatzResearch.WordTrace]
  refine ⟨223041746406475766591560025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148694497604317177727706683 223041746406475766591560025)
  ·
    refine ⟨167281309804856824943670019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223041746406475766591560025 167281309804856824943670019)
    ·
      refine ⟨250921964707285237415505029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167281309804856824943670019 250921964707285237415505029)
      ·
        refine ⟨47047868382615982015407193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250921964707285237415505029 47047868382615982015407193)
        ·
          refine ⟨35285901286961986511555395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47047868382615982015407193 35285901286961986511555395)
          ·
            refine ⟨52928851930442979767333093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35285901286961986511555395 52928851930442979767333093)
            ·
              refine ⟨9924159736958058706374955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52928851930442979767333093 9924159736958058706374955)
              ·
                refine ⟨14886239605437088059562433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9924159736958058706374955 14886239605437088059562433)
                ·
                  refine ⟨11164679704077816044671825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14886239605437088059562433 11164679704077816044671825)
                  ·
                    refine ⟨8373509778058362033503869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11164679704077816044671825 8373509778058362033503869)
                    ·
                      refine ⟨3140066166771885762563951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8373509778058362033503869 3140066166771885762563951)
                      ·
                        rfl

theorem cell23_6115257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_6115257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115257 prefixEnd_6115257 := by exact prefixLift 6115257
  have htrace : WordTrace (prefixWord ++ tailWord_6115257) baseStart_6115257 baseEnd_6115257 := by
    simpa [prefixWord, tailWord_6115257, baseEnd_6115257] using wordTrace_append hprefix tailTrace_6115257
  have hstable : (prefixWord ++ tailWord_6115257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115257).length < 2 ^ (prefixWord ++ tailWord_6115257).sum := by decide
  have hdescent : baseEnd_6115257 < baseStart_6115257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115287 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 3, 1, 3]
def baseStart_6115287 : Nat := 118140960795 + 6115287 * 2 ^ 59
def prefixEnd_6115287 : Nat := 4983230072969 + 3 ^ 40 * 6115287 * 2
def baseEnd_6115287 : Nat := 3140081571191520645188813

theorem tailTrace_6115287 : CollatzResearch.WordTrace tailWord_6115287 prefixEnd_6115287 3140081571191520645188813 := by
  unfold tailWord_6115287
  simp only [CollatzResearch.WordTrace]
  refine ⟨223042840596367081715152115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148695227064244721143434743 223042840596367081715152115)
  ·
    refine ⟨334564260894550622572728173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223042840596367081715152115 334564260894550622572728173)
    ·
      refine ⟨125461597835456483464773065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334564260894550622572728173 125461597835456483464773065)
      ·
        refine ⟨94096198376592362598579799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125461597835456483464773065 94096198376592362598579799)
        ·
          refine ⟨141144297564888543897869699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94096198376592362598579799 141144297564888543897869699)
          ·
            refine ⟨211716446347332815846804549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141144297564888543897869699 211716446347332815846804549)
            ·
              refine ⟨39696833690124902971275853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211716446347332815846804549 39696833690124902971275853)
              ·
                refine ⟨14886312633796838614228445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39696833690124902971275853 14886312633796838614228445)
                ·
                  refine ⟨5582367237673814480335667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14886312633796838614228445 5582367237673814480335667)
                  ·
                    refine ⟨8373550856510721720503501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5582367237673814480335667 8373550856510721720503501)
                    ·
                      refine ⟨3140081571191520645188813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8373550856510721720503501 3140081571191520645188813)
                      ·
                        rfl

theorem cell23_6115287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_6115287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115287 prefixEnd_6115287 := by exact prefixLift 6115287
  have htrace : WordTrace (prefixWord ++ tailWord_6115287) baseStart_6115287 baseEnd_6115287 := by
    simpa [prefixWord, tailWord_6115287, baseEnd_6115287] using wordTrace_append hprefix tailTrace_6115287
  have hstable : (prefixWord ++ tailWord_6115287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115287).length < 2 ^ (prefixWord ++ tailWord_6115287).sum := by decide
  have hdescent : baseEnd_6115287 < baseStart_6115287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115297 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 4, 3, 2]
def baseStart_6115297 : Nat := 118140960795 + 6115297 * 2 ^ 59
def prefixEnd_6115297 : Nat := 4983230072969 + 3 ^ 40 * 6115297 * 2
def baseEnd_6115297 : Nat := 3140086705998065606063767

theorem tailTrace_6115297 : CollatzResearch.WordTrace tailWord_6115297 prefixEnd_6115297 3140086705998065606063767 := by
  unfold tailWord_6115297
  simp only [CollatzResearch.WordTrace]
  refine ⟨223043205326330853423016145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148695470217553902282010763 223043205326330853423016145)
  ·
    refine ⟨167282403994748140067262109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223043205326330853423016145 167282403994748140067262109)
    ·
      refine ⟨62730901498030552525223291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167282403994748140067262109 62730901498030552525223291)
      ·
        refine ⟨94096352247045828787834937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62730901498030552525223291 94096352247045828787834937)
        ·
          refine ⟨70572264185284371590876203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94096352247045828787834937 70572264185284371590876203)
          ·
            refine ⟨105858396277926557386314305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70572264185284371590876203 105858396277926557386314305)
            ·
              refine ⟨79393797208444918039735729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105858396277926557386314305 79393797208444918039735729)
              ·
                refine ⟨59545347906333688529801797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79393797208444918039735729 59545347906333688529801797)
                ·
                  refine ⟨11164752732437566599337837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59545347906333688529801797 11164752732437566599337837)
                  ·
                    refine ⟨4186782274664087474751689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11164752732437566599337837 4186782274664087474751689)
                    ·
                      refine ⟨3140086705998065606063767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4186782274664087474751689 3140086705998065606063767)
                      ·
                        rfl

theorem cell23_6115297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_6115297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115297 prefixEnd_6115297 := by exact prefixLift 6115297
  have htrace : WordTrace (prefixWord ++ tailWord_6115297) baseStart_6115297 baseEnd_6115297 := by
    simpa [prefixWord, tailWord_6115297, baseEnd_6115297] using wordTrace_append hprefix tailTrace_6115297
  have hstable : (prefixWord ++ tailWord_6115297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115297).length < 2 ^ (prefixWord ++ tailWord_6115297).sum := by decide
  have hdescent : baseEnd_6115297 < baseStart_6115297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115320 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 1, 6]
def baseStart_6115320 : Nat := 118140960795 + 6115320 * 2 ^ 59
def prefixEnd_6115320 : Nat := 4983230072969 + 3 ^ 40 * 6115320 * 2
def baseEnd_6115320 : Nat := 1046699505351039672025387

theorem tailTrace_6115320 : CollatzResearch.WordTrace tailWord_6115320 prefixEnd_6115320 1046699505351039672025387 := by
  unfold tailWord_6115320
  simp only [CollatzResearch.WordTrace]
  refine ⟨111522022102623764175551707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148696029470165018900735609 111522022102623764175551707)
  ·
    refine ⟨167283033153935646263327561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111522022102623764175551707 167283033153935646263327561)
    ·
      refine ⟨125462274865451734697495671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167283033153935646263327561 125462274865451734697495671)
      ·
        refine ⟨188193412298177602046243507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125462274865451734697495671 188193412298177602046243507)
        ·
          refine ⟨282290118447266403069365261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188193412298177602046243507 282290118447266403069365261)
          ·
            refine ⟨105858794417724901151011973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282290118447266403069365261 105858794417724901151011973)
            ·
              refine ⟨19848523953323418965814745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105858794417724901151011973 19848523953323418965814745)
              ·
                refine ⟨14886392964992564224361059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19848523953323418965814745 14886392964992564224361059)
                ·
                  refine ⟨22329589447488846336541589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14886392964992564224361059 22329589447488846336541589)
                  ·
                    refine ⟨1046699505351039672025387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22329589447488846336541589 1046699505351039672025387)
                    ·
                      rfl

theorem cell23_6115320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_6115320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115320 prefixEnd_6115320 := by exact prefixLift 6115320
  have htrace : WordTrace (prefixWord ++ tailWord_6115320) baseStart_6115320 baseEnd_6115320 := by
    simpa [prefixWord, tailWord_6115320, baseEnd_6115320] using wordTrace_append hprefix tailTrace_6115320
  have hstable : (prefixWord ++ tailWord_6115320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115320).length < 2 ^ (prefixWord ++ tailWord_6115320).sum := by decide
  have hdescent : baseEnd_6115320 < baseStart_6115320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115321 : List Nat := [1, 2, 1, 3, 1, 5, 2, 3, 1, 1, 3]
def baseStart_6115321 : Nat := 118140960795 + 6115321 * 2 ^ 59
def prefixEnd_6115321 : Nat := 4983230072969 + 3 ^ 40 * 6115321 * 2
def baseEnd_6115321 : Nat := 3140099029533773512163657

theorem tailTrace_6115321 : CollatzResearch.WordTrace tailWord_6115321 prefixEnd_6115321 3140099029533773512163657 := by
  unfold tailWord_6115321
  simp only [CollatzResearch.WordTrace]
  refine ⟨223044080678243905521889817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148696053785495937014593211 223044080678243905521889817)
  ·
    refine ⟨167283060508682929141417363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223044080678243905521889817 167283060508682929141417363)
    ·
      refine ⟨250924590763024393712126045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167283060508682929141417363 250924590763024393712126045)
      ·
        refine ⟨94096721536134147642047267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250924590763024393712126045 94096721536134147642047267)
        ·
          refine ⟨141145082304201221463070901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94096721536134147642047267 141145082304201221463070901)
          ·
            refine ⟨13232351466018864512162897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141145082304201221463070901 13232351466018864512162897)
            ·
              refine ⟨9924263599514148384122173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13232351466018864512162897 9924263599514148384122173)
              ·
                refine ⟨3721598849817805644045815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9924263599514148384122173 3721598849817805644045815)
                ·
                  refine ⟨5582398274726708466068723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721598849817805644045815 5582398274726708466068723)
                  ·
                    refine ⟨8373597412090062699103085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5582398274726708466068723 8373597412090062699103085)
                    ·
                      refine ⟨3140099029533773512163657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8373597412090062699103085 3140099029533773512163657)
                      ·
                        rfl

theorem cell23_6115321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_6115321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115321 prefixEnd_6115321 := by exact prefixLift 6115321
  have htrace : WordTrace (prefixWord ++ tailWord_6115321) baseStart_6115321 baseEnd_6115321 := by
    simpa [prefixWord, tailWord_6115321, baseEnd_6115321] using wordTrace_append hprefix tailTrace_6115321
  have hstable : (prefixWord ++ tailWord_6115321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115321).length < 2 ^ (prefixWord ++ tailWord_6115321).sum := by decide
  have hdescent : baseEnd_6115321 < baseStart_6115321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115340 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 1, 1, 6]
def baseStart_6115340 : Nat := 118140960795 + 6115340 * 2 ^ 59
def prefixEnd_6115340 : Nat := 4983230072969 + 3 ^ 40 * 6115340 * 2
def baseEnd_6115340 : Nat := 3140108785666208937826069

theorem tailTrace_6115340 : CollatzResearch.WordTrace tailWord_6115340 prefixEnd_6115340 3140108785666208937826069 := by
  unfold tailWord_6115340
  simp only [CollatzResearch.WordTrace]
  refine ⟨111522386832587535883415737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148696515776783381177887649 111522386832587535883415737)
  ·
    refine ⟨83641790124440651912561803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111522386832587535883415737 83641790124440651912561803)
    ·
      refine ⟨125462685186660977868842705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83641790124440651912561803 125462685186660977868842705)
      ·
        refine ⟨94097013889995733401632029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125462685186660977868842705 94097013889995733401632029)
        ·
          refine ⟨35286380208748400025612011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94097013889995733401632029 35286380208748400025612011)
          ·
            refine ⟨52929570313122600038418017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35286380208748400025612011 52929570313122600038418017)
            ·
              refine ⟨39697177734841950028813513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52929570313122600038418017 39697177734841950028813513)
              ·
                refine ⟨29772883301131462521610135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39697177734841950028813513 29772883301131462521610135)
                ·
                  refine ⟨44659324951697193782415203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29772883301131462521610135 44659324951697193782415203)
                  ·
                    refine ⟨66988987427545790673622805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44659324951697193782415203 66988987427545790673622805)
                    ·
                      refine ⟨3140108785666208937826069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66988987427545790673622805 3140108785666208937826069)
                      ·
                        rfl

theorem cell23_6115340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_6115340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115340 prefixEnd_6115340 := by exact prefixLift 6115340
  have htrace : WordTrace (prefixWord ++ tailWord_6115340) baseStart_6115340 baseEnd_6115340 := by
    simpa [prefixWord, tailWord_6115340, baseEnd_6115340] using wordTrace_append hprefix tailTrace_6115340
  have hstable : (prefixWord ++ tailWord_6115340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115340).length < 2 ^ (prefixWord ++ tailWord_6115340).sum := by decide
  have hdescent : baseEnd_6115340 < baseStart_6115340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115357 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_6115357 : Nat := 118140960795 + 6115357 * 2 ^ 59
def prefixEnd_6115357 : Nat := 4983230072969 + 3 ^ 40 * 6115357 * 2
def baseEnd_6115357 : Nat := 3140117514837335371313491

theorem tailTrace_6115357 : CollatzResearch.WordTrace tailWord_6115357 prefixEnd_6115357 3140117514837335371313491 := by
  unfold tailWord_6115357
  simp only [CollatzResearch.WordTrace]
  refine ⟨223045393706113483670200325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148696929137408989113466883 223045393706113483670200325)
  ·
    refine ⟨41821011319896278188162561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223045393706113483670200325 41821011319896278188162561)
    ·
      refine ⟨31365758489922208641121921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41821011319896278188162561 31365758489922208641121921)
      ·
        refine ⟨23524318867441656480841441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31365758489922208641121921 23524318867441656480841441)
        ·
          refine ⟨17643239150581242360631081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23524318867441656480841441 17643239150581242360631081)
          ·
            refine ⟨13232429362935931770473311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17643239150581242360631081 13232429362935931770473311)
            ·
              refine ⟨19848644044403897655709967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13232429362935931770473311 19848644044403897655709967)
              ·
                refine ⟨29772966066605846483564951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19848644044403897655709967 29772966066605846483564951)
                ·
                  refine ⟨44659449099908769725347427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29772966066605846483564951 44659449099908769725347427)
                  ·
                    refine ⟨66989173649863154588021141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44659449099908769725347427 66989173649863154588021141)
                    ·
                      refine ⟨3140117514837335371313491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66989173649863154588021141 3140117514837335371313491)
                      ·
                        rfl

theorem cell23_6115357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_6115357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115357 prefixEnd_6115357 := by exact prefixLift 6115357
  have htrace : WordTrace (prefixWord ++ tailWord_6115357) baseStart_6115357 baseEnd_6115357 := by
    simpa [prefixWord, tailWord_6115357, baseEnd_6115357] using wordTrace_append hprefix tailTrace_6115357
  have hstable : (prefixWord ++ tailWord_6115357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115357).length < 2 ^ (prefixWord ++ tailWord_6115357).sum := by decide
  have hdescent : baseEnd_6115357 < baseStart_6115357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115378 : List Nat := [3, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2]
def baseStart_6115378 : Nat := 118140960795 + 6115378 * 2 ^ 59
def prefixEnd_6115378 : Nat := 4983230072969 + 3 ^ 40 * 6115378 * 2
def baseEnd_6115378 : Nat := 3140128297931079789150895

theorem tailTrace_6115378 : CollatzResearch.WordTrace tailWord_6115378 prefixEnd_6115378 3140128297931079789150895 := by
  unfold tailWord_6115378
  simp only [CollatzResearch.WordTrace]
  refine ⟨55761539909759351064178697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148697439759358269504476525 55761539909759351064178697)
  ·
    refine ⟨41821154932319513298134023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55761539909759351064178697 41821154932319513298134023)
    ·
      refine ⟨62731732398479269947201035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41821154932319513298134023 62731732398479269947201035)
      ·
        refine ⟨94097598597718904920801553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62731732398479269947201035 94097598597718904920801553)
        ·
          refine ⟨70573198948289178690601165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94097598597718904920801553 70573198948289178690601165)
          ·
            refine ⟨26464949605608442008975437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70573198948289178690601165 26464949605608442008975437)
            ·
              refine ⟨9924356102103165753365789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26464949605608442008975437 9924356102103165753365789)
              ·
                refine ⟨3721633538288687157512171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9924356102103165753365789 3721633538288687157512171)
                ·
                  refine ⟨5582450307433030736268257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721633538288687157512171 5582450307433030736268257)
                  ·
                    refine ⟨4186837730574773052201193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5582450307433030736268257 4186837730574773052201193)
                    ·
                      refine ⟨3140128297931079789150895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4186837730574773052201193 3140128297931079789150895)
                      ·
                        rfl

theorem cell23_6115378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_6115378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115378 prefixEnd_6115378 := by exact prefixLift 6115378
  have htrace : WordTrace (prefixWord ++ tailWord_6115378) baseStart_6115378 baseEnd_6115378 := by
    simpa [prefixWord, tailWord_6115378, baseEnd_6115378] using wordTrace_append hprefix tailTrace_6115378
  have hstable : (prefixWord ++ tailWord_6115378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115378).length < 2 ^ (prefixWord ++ tailWord_6115378).sum := by decide
  have hdescent : baseEnd_6115378 < baseStart_6115378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115437 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_6115437 : Nat := 118140960795 + 6115437 * 2 ^ 59
def prefixEnd_6115437 : Nat := 4983230072969 + 3 ^ 40 * 6115437 * 2
def baseEnd_6115437 : Nat := 3140158593289695058313123

theorem tailTrace_6115437 : CollatzResearch.WordTrace tailWord_6115437 prefixEnd_6115437 3140158593289695058313123 := by
  unfold tailWord_6115437
  simp only [CollatzResearch.WordTrace]
  refine ⟨223048311545823657333112565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148698874363882438222075043 223048311545823657333112565)
  ·
    refine ⟨20910779207420967874979303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223048311545823657333112565 20910779207420967874979303)
    ·
      refine ⟨31366168811131451812468955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20910779207420967874979303 31366168811131451812468955)
      ·
        refine ⟨47049253216697177718703433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31366168811131451812468955 47049253216697177718703433)
        ·
          refine ⟨35286939912522883289027575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47049253216697177718703433 35286939912522883289027575)
          ·
            refine ⟨52930409868784324933541363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35286939912522883289027575 52930409868784324933541363)
            ·
              refine ⟨79395614803176487400312045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52930409868784324933541363 79395614803176487400312045)
              ·
                refine ⟨29773355551191182775117017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79395614803176487400312045 29773355551191182775117017)
                ·
                  refine ⟨22330016663393387081337763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29773355551191182775117017 22330016663393387081337763)
                  ·
                    refine ⟨33495024995090080622006645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22330016663393387081337763 33495024995090080622006645)
                    ·
                      refine ⟨3140158593289695058313123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33495024995090080622006645 3140158593289695058313123)
                      ·
                        rfl

theorem cell23_6115437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_6115437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115437 prefixEnd_6115437 := by exact prefixLift 6115437
  have htrace : WordTrace (prefixWord ++ tailWord_6115437) baseStart_6115437 baseEnd_6115437 := by
    simpa [prefixWord, tailWord_6115437, baseEnd_6115437] using wordTrace_append hprefix tailTrace_6115437
  have hstable : (prefixWord ++ tailWord_6115437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115437).length < 2 ^ (prefixWord ++ tailWord_6115437).sum := by decide
  have hdescent : baseEnd_6115437 < baseStart_6115437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115438 : List Nat := [4, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2]
def baseStart_6115438 : Nat := 118140960795 + 6115438 * 2 ^ 59
def prefixEnd_6115438 : Nat := 4983230072969 + 3 ^ 40 * 6115438 * 2
def baseEnd_6115438 : Nat := 3140159106770349554400619

theorem tailTrace_6115438 : CollatzResearch.WordTrace tailWord_6115438 prefixEnd_6115438 3140159106770349554400619 := by
  unfold tailWord_6115438
  simp only [CollatzResearch.WordTrace]
  refine ⟨27881043502352504312987371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148698898679213356335932645 27881043502352504312987371)
  ·
    refine ⟨41821565253528756469481057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27881043502352504312987371 41821565253528756469481057)
    ·
      refine ⟨31366173940146567352110793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41821565253528756469481057 31366173940146567352110793)
      ·
        refine ⟨23524630455109925514083095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31366173940146567352110793 23524630455109925514083095)
        ·
          refine ⟨35286945682664888271124643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23524630455109925514083095 35286945682664888271124643)
          ·
            refine ⟨52930418523997332406686965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35286945682664888271124643 52930418523997332406686965)
            ·
              refine ⟨4962226736624749913126903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52930418523997332406686965 4962226736624749913126903)
              ·
                refine ⟨7443340104937124869690355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4962226736624749913126903 7443340104937124869690355)
                ·
                  refine ⟨11165010157405687304535533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7443340104937124869690355 11165010157405687304535533)
                  ·
                    refine ⟨4186878809027132739200825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11165010157405687304535533 4186878809027132739200825)
                    ·
                      refine ⟨3140159106770349554400619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4186878809027132739200825 3140159106770349554400619)
                      ·
                        rfl

theorem cell23_6115438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_6115438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115438 prefixEnd_6115438 := by exact prefixLift 6115438
  have htrace : WordTrace (prefixWord ++ tailWord_6115438) baseStart_6115438 baseEnd_6115438 := by
    simpa [prefixWord, tailWord_6115438, baseEnd_6115438] using wordTrace_append hprefix tailTrace_6115438
  have hstable : (prefixWord ++ tailWord_6115438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115438).length < 2 ^ (prefixWord ++ tailWord_6115438).sum := by decide
  have hdescent : baseEnd_6115438 < baseStart_6115438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115464 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_6115464 : Nat := 118140960795 + 6115464 * 2 ^ 59
def prefixEnd_6115464 : Nat := 4983230072969 + 3 ^ 40 * 6115464 * 2
def baseEnd_6115464 : Nat := 3140172457267366452675499

theorem tailTrace_6115464 : CollatzResearch.WordTrace tailWord_6115464 prefixEnd_6115464 3140172457267366452675499 := by
  unfold tailWord_6115464
  simp only [CollatzResearch.WordTrace]
  refine ⟨111524648158362920472172723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148699530877817227296230297 111524648158362920472172723)
  ·
    refine ⟨167286972237544380708259085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111524648158362920472172723 167286972237544380708259085)
    ·
      refine ⟨62732614589079142765597157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167286972237544380708259085 62732614589079142765597157)
      ·
        refine ⟨11762365235452339268549467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62732614589079142765597157 11762365235452339268549467)
        ·
          refine ⟨17643547853178508902824201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11762365235452339268549467 17643547853178508902824201)
          ·
            refine ⟨13232660889883881677118151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17643547853178508902824201 13232660889883881677118151)
            ·
              refine ⟨19848991334825822515677227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13232660889883881677118151 19848991334825822515677227)
              ·
                refine ⟨29773487002238733773515841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19848991334825822515677227 29773487002238733773515841)
                ·
                  refine ⟨22330115251679050330136881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29773487002238733773515841 22330115251679050330136881)
                  ·
                    refine ⟨16747586438759287747602661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22330115251679050330136881 16747586438759287747602661)
                    ·
                      refine ⟨3140172457267366452675499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16747586438759287747602661 3140172457267366452675499)
                      ·
                        rfl

theorem cell23_6115464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_6115464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115464 prefixEnd_6115464 := by exact prefixLift 6115464
  have htrace : WordTrace (prefixWord ++ tailWord_6115464) baseStart_6115464 baseEnd_6115464 := by
    simpa [prefixWord, tailWord_6115464, baseEnd_6115464] using wordTrace_append hprefix tailTrace_6115464
  have hstable : (prefixWord ++ tailWord_6115464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115464).length < 2 ^ (prefixWord ++ tailWord_6115464).sum := by decide
  have hdescent : baseEnd_6115464 < baseStart_6115464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115507 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 4]
def baseStart_6115507 : Nat := 118140960795 + 6115507 * 2 ^ 59
def prefixEnd_6115507 : Nat := 4983230072969 + 3 ^ 40 * 6115507 * 2
def baseEnd_6115507 : Nat := 3140194536935509784437801

theorem tailTrace_6115507 : CollatzResearch.WordTrace tailWord_6115507 prefixEnd_6115507 3140194536935509784437801 := by
  unfold tailWord_6115507
  simp only [CollatzResearch.WordTrace]
  refine ⟨223050864655570059288160775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148700576437046706192107183 223050864655570059288160775)
  ·
    refine ⟨334576296983355088932241163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223050864655570059288160775 334576296983355088932241163)
    ·
      refine ⟨501864445475032633398361745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334576296983355088932241163 501864445475032633398361745)
      ·
        refine ⟨376398334106274475048771309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501864445475032633398361745 376398334106274475048771309)
        ·
          refine ⟨141149375289852928143289241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 376398334106274475048771309 141149375289852928143289241)
          ·
            refine ⟨105862031467389696107466931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141149375289852928143289241 105862031467389696107466931)
            ·
              refine ⟨158793047201084544161200397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105862031467389696107466931 158793047201084544161200397)
              ·
                refine ⟨59547392700406704060450149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158793047201084544161200397 59547392700406704060450149)
                ·
                  refine ⟨11165136131326257011334403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59547392700406704060450149 11165136131326257011334403)
                  ·
                    refine ⟨16747704196989385517001605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11165136131326257011334403 16747704196989385517001605)
                    ·
                      refine ⟨3140194536935509784437801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16747704196989385517001605 3140194536935509784437801)
                      ·
                        rfl

theorem cell23_6115507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 4].length) (baseStart_6115507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115507 prefixEnd_6115507 := by exact prefixLift 6115507
  have htrace : WordTrace (prefixWord ++ tailWord_6115507) baseStart_6115507 baseEnd_6115507 := by
    simpa [prefixWord, tailWord_6115507, baseEnd_6115507] using wordTrace_append hprefix tailTrace_6115507
  have hstable : (prefixWord ++ tailWord_6115507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115507).length < 2 ^ (prefixWord ++ tailWord_6115507).sum := by decide
  have hdescent : baseEnd_6115507 < baseStart_6115507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115524 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_6115524 : Nat := 118140960795 + 6115524 * 2 ^ 59
def prefixEnd_6115524 : Nat := 4983230072969 + 3 ^ 40 * 6115524 * 2
def baseEnd_6115524 : Nat := 3140203266106636217925223

theorem tailTrace_6115524 : CollatzResearch.WordTrace tailWord_6115524 prefixEnd_6115524 3140203266106636217925223 := by
  unfold tailWord_6115524
  simp only [CollatzResearch.WordTrace]
  refine ⟨111525742348254235595764813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148700989797672314127686417 111525742348254235595764813)
  ·
    refine ⟨41822153380595338348411805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111525742348254235595764813 41822153380595338348411805)
    ·
      refine ⟨15683307517723251880654427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41822153380595338348411805 15683307517723251880654427)
      ·
        refine ⟨23524961276584877820981641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15683307517723251880654427 23524961276584877820981641)
        ·
          refine ⟨17643720957438658365736231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23524961276584877820981641 17643720957438658365736231)
          ·
            refine ⟨26465581436157987548604347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17643720957438658365736231 26465581436157987548604347)
            ·
              refine ⟨39698372154236981322906521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26465581436157987548604347 39698372154236981322906521)
              ·
                refine ⟨29773779115677735992179891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39698372154236981322906521 29773779115677735992179891)
                ·
                  refine ⟨44660668673516603988269837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29773779115677735992179891 44660668673516603988269837)
                  ·
                    refine ⟨16747750752568726495601189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44660668673516603988269837 16747750752568726495601189)
                    ·
                      refine ⟨3140203266106636217925223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16747750752568726495601189 3140203266106636217925223)
                      ·
                        rfl

theorem cell23_6115524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_6115524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115524 prefixEnd_6115524 := by exact prefixLift 6115524
  have htrace : WordTrace (prefixWord ++ tailWord_6115524) baseStart_6115524 baseEnd_6115524 := by
    simpa [prefixWord, tailWord_6115524, baseEnd_6115524] using wordTrace_append hprefix tailTrace_6115524
  have hstable : (prefixWord ++ tailWord_6115524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115524).length < 2 ^ (prefixWord ++ tailWord_6115524).sum := by decide
  have hdescent : baseEnd_6115524 < baseStart_6115524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115544 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 1, 4, 3]
def baseStart_6115544 : Nat := 118140960795 + 6115544 * 2 ^ 59
def prefixEnd_6115544 : Nat := 4983230072969 + 3 ^ 40 * 6115544 * 2
def baseEnd_6115544 : Nat := 3140213535719726139675131

theorem tailTrace_6115544 : CollatzResearch.WordTrace tailWord_6115544 prefixEnd_6115544 3140213535719726139675131 := by
  unfold tailWord_6115544
  simp only [CollatzResearch.WordTrace]
  refine ⟨111526107078218007303628843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148701476104290676404838457 111526107078218007303628843)
  ·
    refine ⟨167289160617327010955443265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111526107078218007303628843 167289160617327010955443265)
    ·
      refine ⟨125466870462995258216582449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167289160617327010955443265 125466870462995258216582449)
      ·
        refine ⟨94100152847246443662436837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125466870462995258216582449 94100152847246443662436837)
        ·
          refine ⟨17643778658858708186706907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94100152847246443662436837 17643778658858708186706907)
          ·
            refine ⟨26465667988288062280060361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17643778658858708186706907 26465667988288062280060361)
            ·
              refine ⟨19849250991216046710045271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26465667988288062280060361 19849250991216046710045271)
              ·
                refine ⟨29773876486824070065067907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19849250991216046710045271 29773876486824070065067907)
                ·
                  refine ⟨44660814730236105097601861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29773876486824070065067907 44660814730236105097601861)
                  ·
                    refine ⟨8373902761919269705800349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44660814730236105097601861 8373902761919269705800349)
                    ·
                      refine ⟨3140213535719726139675131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8373902761919269705800349 3140213535719726139675131)
                      ·
                        rfl

theorem cell23_6115544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_6115544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115544 prefixEnd_6115544 := by exact prefixLift 6115544
  have htrace : WordTrace (prefixWord ++ tailWord_6115544) baseStart_6115544 baseEnd_6115544 := by
    simpa [prefixWord, tailWord_6115544, baseEnd_6115544] using wordTrace_append hprefix tailTrace_6115544
  have hstable : (prefixWord ++ tailWord_6115544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115544).length < 2 ^ (prefixWord ++ tailWord_6115544).sum := by decide
  have hdescent : baseEnd_6115544 < baseStart_6115544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115584 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 3, 5, 2]
def baseStart_6115584 : Nat := 118140960795 + 6115584 * 2 ^ 59
def prefixEnd_6115584 : Nat := 4983230072969 + 3 ^ 40 * 6115584 * 2
def baseEnd_6115584 : Nat := 3140234074945905983174947

theorem tailTrace_6115584 : CollatzResearch.WordTrace tailWord_6115584 prefixEnd_6115584 3140234074945905983174947 := by
  unfold tailWord_6115584
  simp only [CollatzResearch.WordTrace]
  refine ⟨111526836538145550719356903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148702448717527400959142537 111526836538145550719356903)
  ·
    refine ⟨167290254807218326079035355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111526836538145550719356903 167290254807218326079035355)
    ·
      refine ⟨250935382210827489118553033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167290254807218326079035355 250935382210827489118553033)
      ·
        refine ⟨188201536658120616838914775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250935382210827489118553033 188201536658120616838914775)
        ·
          refine ⟨282302304987180925258372163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188201536658120616838914775 282302304987180925258372163)
          ·
            refine ⟨423453457480771387887558245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282302304987180925258372163 423453457480771387887558245)
            ·
              refine ⟨79397523277644635228917171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 423453457480771387887558245 79397523277644635228917171)
              ·
                refine ⟨119096284916466952843375757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79397523277644635228917171 119096284916466952843375757)
                ·
                  refine ⟨44661106843675107316265909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119096284916466952843375757 44661106843675107316265909)
                  ·
                    refine ⟨4186978766594541310899929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44661106843675107316265909 4186978766594541310899929)
                    ·
                      refine ⟨3140234074945905983174947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4186978766594541310899929 3140234074945905983174947)
                      ·
                        rfl

theorem cell23_6115584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 5, 2].length) (baseStart_6115584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115584 prefixEnd_6115584 := by exact prefixLift 6115584
  have htrace : WordTrace (prefixWord ++ tailWord_6115584) baseStart_6115584 baseEnd_6115584 := by
    simpa [prefixWord, tailWord_6115584, baseEnd_6115584] using wordTrace_append hprefix tailTrace_6115584
  have hstable : (prefixWord ++ tailWord_6115584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115584).length < 2 ^ (prefixWord ++ tailWord_6115584).sum := by decide
  have hdescent : baseEnd_6115584 < baseStart_6115584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115601 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 2, 3, 2]
def baseStart_6115601 : Nat := 118140960795 + 6115601 * 2 ^ 59
def prefixEnd_6115601 : Nat := 4983230072969 + 3 ^ 40 * 6115601 * 2
def baseEnd_6115601 : Nat := 3140242804117032416662369

theorem tailTrace_6115601 : CollatzResearch.WordTrace tailWord_6115601 prefixEnd_6115601 3140242804117032416662369 := by
  unfold tailWord_6115601
  simp only [CollatzResearch.WordTrace]
  refine ⟨223054293117229513342082657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148702862078153008894721771 223054293117229513342082657)
  ·
    refine ⟨167290719837922135006561993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223054293117229513342082657 167290719837922135006561993)
    ·
      refine ⟨125468039878441601254921495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167290719837922135006561993 125468039878441601254921495)
      ·
        refine ⟨188202059817662401882382243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125468039878441601254921495 188202059817662401882382243)
        ·
          refine ⟨282303089726493602823573365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188202059817662401882382243 282303089726493602823573365)
          ·
            refine ⟨26465914661858775264710003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 282303089726493602823573365 26465914661858775264710003)
            ·
              refine ⟨39698871992788162897065005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26465914661858775264710003 39698871992788162897065005)
              ·
                refine ⟨14887076997295561086399377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39698871992788162897065005 14887076997295561086399377)
                ·
                  refine ⟨11165307747971670814799533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14887076997295561086399377 11165307747971670814799533)
                  ·
                    refine ⟨4186990405489376555549825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11165307747971670814799533 4186990405489376555549825)
                    ·
                      refine ⟨3140242804117032416662369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4186990405489376555549825 3140242804117032416662369)
                      ·
                        rfl

theorem cell23_6115601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 3, 2].length) (baseStart_6115601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115601 prefixEnd_6115601 := by exact prefixLift 6115601
  have htrace : WordTrace (prefixWord ++ tailWord_6115601) baseStart_6115601 baseEnd_6115601 := by
    simpa [prefixWord, tailWord_6115601, baseEnd_6115601] using wordTrace_append hprefix tailTrace_6115601
  have hstable : (prefixWord ++ tailWord_6115601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115601).length < 2 ^ (prefixWord ++ tailWord_6115601).sum := by decide
  have hdescent : baseEnd_6115601 < baseStart_6115601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115608 : List Nat := [2, 1, 2, 3, 1, 2, 2, 5, 1, 1, 3]
def baseStart_6115608 : Nat := 118140960795 + 6115608 * 2 ^ 59
def prefixEnd_6115608 : Nat := 4983230072969 + 3 ^ 40 * 6115608 * 2
def baseEnd_6115608 : Nat := 3140246398481613889274837

theorem tailTrace_6115608 : CollatzResearch.WordTrace tailWord_6115608 prefixEnd_6115608 3140246398481613889274837 := by
  unfold tailWord_6115608
  simp only [CollatzResearch.WordTrace]
  refine ⟨111527274214102076768793739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148703032285469435691724985 111527274214102076768793739)
  ·
    refine ⟨167290911321153115153190609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111527274214102076768793739 167290911321153115153190609)
    ·
      refine ⟨125468183490864836364892957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167290911321153115153190609 125468183490864836364892957)
      ·
        refine ⟨47050568809074313636834859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125468183490864836364892957 47050568809074313636834859)
        ·
          refine ⟨70575853213611470455252289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47050568809074313636834859 70575853213611470455252289)
          ·
            refine ⟨52931889910208602841439217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70575853213611470455252289 52931889910208602841439217)
            ·
              refine ⟨39698917432656452131079413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52931889910208602841439217 39698917432656452131079413)
              ·
                refine ⟨3721773509311542387288695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39698917432656452131079413 3721773509311542387288695)
                ·
                  refine ⟨5582660263967313580933043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721773509311542387288695 5582660263967313580933043)
                  ·
                    refine ⟨8373990395950970371399565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5582660263967313580933043 8373990395950970371399565)
                    ·
                      refine ⟨3140246398481613889274837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8373990395950970371399565 3140246398481613889274837)
                      ·
                        rfl

theorem cell23_6115608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_6115608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115608 prefixEnd_6115608 := by exact prefixLift 6115608
  have htrace : WordTrace (prefixWord ++ tailWord_6115608) baseStart_6115608 baseEnd_6115608 := by
    simpa [prefixWord, tailWord_6115608, baseEnd_6115608] using wordTrace_append hprefix tailTrace_6115608
  have hstable : (prefixWord ++ tailWord_6115608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115608).length < 2 ^ (prefixWord ++ tailWord_6115608).sum := by decide
  have hdescent : baseEnd_6115608 < baseStart_6115608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115618 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 2, 3, 2]
def baseStart_6115618 : Nat := 118140960795 + 6115618 * 2 ^ 59
def prefixEnd_6115618 : Nat := 4983230072969 + 3 ^ 40 * 6115618 * 2
def baseEnd_6115618 : Nat := 3140251533288158850149791

theorem tailTrace_6115618 : CollatzResearch.WordTrace tailWord_6115618 prefixEnd_6115618 3140251533288158850149791 := by
  unfold tailWord_6115618
  simp only [CollatzResearch.WordTrace]
  refine ⟨55763728289541981311362877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148703275438778616830301005 55763728289541981311362877)
  ·
    refine ⟨20911398108578242991761079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55763728289541981311362877 20911398108578242991761079)
    ·
      refine ⟨31367097162867364487641619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20911398108578242991761079 31367097162867364487641619)
      ·
        refine ⟨47050645744301046731462429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31367097162867364487641619 47050645744301046731462429)
        ·
          refine ⟨17643992154112892524298411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47050645744301046731462429 17643992154112892524298411)
          ·
            refine ⟨26465988231169338786447617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17643992154112892524298411 26465988231169338786447617)
            ·
              refine ⟨19849491173377004089835713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26465988231169338786447617 19849491173377004089835713)
              ·
                refine ⟨14887118380032753067376785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19849491173377004089835713 14887118380032753067376785)
                ·
                  refine ⟨11165338785024564800532589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14887118380032753067376785 11165338785024564800532589)
                  ·
                    refine ⟨4187002044384211800199721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11165338785024564800532589 4187002044384211800199721)
                    ·
                      refine ⟨3140251533288158850149791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187002044384211800199721 3140251533288158850149791)
                      ·
                        rfl

theorem cell23_6115618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_6115618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115618 prefixEnd_6115618 := by exact prefixLift 6115618
  have htrace : WordTrace (prefixWord ++ tailWord_6115618) baseStart_6115618 baseEnd_6115618 := by
    simpa [prefixWord, tailWord_6115618, baseEnd_6115618] using wordTrace_append hprefix tailTrace_6115618
  have hstable : (prefixWord ++ tailWord_6115618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115618).length < 2 ^ (prefixWord ++ tailWord_6115618).sum := by decide
  have hdescent : baseEnd_6115618 < baseStart_6115618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115627 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 4]
def baseStart_6115627 : Nat := 118140960795 + 6115627 * 2 ^ 59
def prefixEnd_6115627 : Nat := 4983230072969 + 3 ^ 40 * 6115627 * 2
def baseEnd_6115627 : Nat := 3140256154614049314937249

theorem tailTrace_6115627 : CollatzResearch.WordTrace tailWord_6115627 prefixEnd_6115627 3140256154614049314937249 := by
  unfold tailWord_6115627
  simp only [CollatzResearch.WordTrace]
  refine ⟨223055241415135319782529135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148703494276756879855019423 223055241415135319782529135)
  ·
    refine ⟨334582862122702979673793703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223055241415135319782529135 334582862122702979673793703)
    ·
      refine ⟨501874293184054469510690555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334582862122702979673793703 501874293184054469510690555)
      ·
        refine ⟨752811439776081704266035833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501874293184054469510690555 752811439776081704266035833)
        ·
          refine ⟨564608579832061278199526875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 752811439776081704266035833 564608579832061278199526875)
          ·
            refine ⟨846912869748091917299290313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564608579832061278199526875 846912869748091917299290313)
            ·
              refine ⟨635184652311068937974467735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 846912869748091917299290313 635184652311068937974467735)
              ·
                refine ⟨952776978466603406961701603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635184652311068937974467735 952776978466603406961701603)
                ·
                  refine ⟨1429165467699905110442552405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 952776978466603406961701603 1429165467699905110442552405)
                  ·
                    refine ⟨16748032824608263012998661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1429165467699905110442552405 16748032824608263012998661)
                    ·
                      refine ⟨3140256154614049314937249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16748032824608263012998661 3140256154614049314937249)
                      ·
                        rfl

theorem cell23_6115627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 4].length) (baseStart_6115627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115627 prefixEnd_6115627 := by exact prefixLift 6115627
  have htrace : WordTrace (prefixWord ++ tailWord_6115627) baseStart_6115627 baseEnd_6115627 := by
    simpa [prefixWord, tailWord_6115627, baseEnd_6115627] using wordTrace_append hprefix tailTrace_6115627
  have hstable : (prefixWord ++ tailWord_6115627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115627).length < 2 ^ (prefixWord ++ tailWord_6115627).sum := by decide
  have hdescent : baseEnd_6115627 < baseStart_6115627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115641 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 1, 6]
def baseStart_6115641 : Nat := 118140960795 + 6115641 * 2 ^ 59
def prefixEnd_6115641 : Nat := 4983230072969 + 3 ^ 40 * 6115641 * 2
def baseEnd_6115641 : Nat := 1046754447781070753387395

theorem tailTrace_6115641 : CollatzResearch.WordTrace tailWord_6115641 prefixEnd_6115641 1046754447781070753387395 := by
  unfold tailWord_6115641
  simp only [CollatzResearch.WordTrace]
  refine ⟨223055752037084600173538777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148703834691389733449025851 223055752037084600173538777)
  ·
    refine ⟨167291814027813450130154083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223055752037084600173538777 167291814027813450130154083)
    ·
      refine ⟨250937721041720175195231125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167291814027813450130154083 250937721041720175195231125)
      ·
        refine ⟨11762705673830633212276459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 250937721041720175195231125 11762705673830633212276459)
        ·
          refine ⟨17644058510745949818414689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11762705673830633212276459 17644058510745949818414689)
          ·
            refine ⟨13233043883059462363811017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17644058510745949818414689 13233043883059462363811017)
            ·
              refine ⟨9924782912294596772858263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13233043883059462363811017 9924782912294596772858263)
              ·
                refine ⟨14887174368441895159287395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9924782912294596772858263 14887174368441895159287395)
                ·
                  refine ⟨22330761552662842738931093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14887174368441895159287395 22330761552662842738931093)
                  ·
                    refine ⟨1046754447781070753387395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22330761552662842738931093 1046754447781070753387395)
                    ·
                      rfl

theorem cell23_6115641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 6].length) (baseStart_6115641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115641 prefixEnd_6115641 := by exact prefixLift 6115641
  have htrace : WordTrace (prefixWord ++ tailWord_6115641) baseStart_6115641 baseEnd_6115641 := by
    simpa [prefixWord, tailWord_6115641, baseEnd_6115641] using wordTrace_append hprefix tailTrace_6115641
  have hstable : (prefixWord ++ tailWord_6115641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115641).length < 2 ^ (prefixWord ++ tailWord_6115641).sum := by decide
  have hdescent : baseEnd_6115641 < baseStart_6115641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115652 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_6115652 : Nat := 118140960795 + 6115652 * 2 ^ 59
def prefixEnd_6115652 : Nat := 4983230072969 + 3 ^ 40 * 6115652 * 2
def baseEnd_6115652 : Nat := 3140268991630411717124635

theorem tailTrace_6115652 : CollatzResearch.WordTrace tailWord_6115652 prefixEnd_6115652 3140268991630411717124635 := by
  unfold tailWord_6115652
  simp only [CollatzResearch.WordTrace]
  refine ⟨111528076620022374526094605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148704102160029832701459473 111528076620022374526094605)
  ·
    refine ⟨41823028732508390447285477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111528076620022374526094605 41823028732508390447285477)
    ·
      refine ⟨7841817887345323208866027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41823028732508390447285477 7841817887345323208866027)
      ·
        refine ⟨11762726831017984813299041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7841817887345323208866027 11762726831017984813299041)
        ·
          refine ⟨8822045123263488609974281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11762726831017984813299041 8822045123263488609974281)
          ·
            refine ⟨6616533842447616457480711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8822045123263488609974281 6616533842447616457480711)
            ·
              refine ⟨9924800763671424686221067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6616533842447616457480711 9924800763671424686221067)
              ·
                refine ⟨14887201145507137029331601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9924800763671424686221067 14887201145507137029331601)
                ·
                  refine ⟨11165400859130352771998701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14887201145507137029331601 11165400859130352771998701)
                  ·
                    refine ⟨4187025322173882289499513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11165400859130352771998701 4187025322173882289499513)
                    ·
                      refine ⟨3140268991630411717124635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4187025322173882289499513 3140268991630411717124635)
                      ·
                        rfl

theorem cell23_6115652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_6115652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6115652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6115652 prefixEnd_6115652 := by exact prefixLift 6115652
  have htrace : WordTrace (prefixWord ++ tailWord_6115652) baseStart_6115652 baseEnd_6115652 := by
    simpa [prefixWord, tailWord_6115652, baseEnd_6115652] using wordTrace_append hprefix tailTrace_6115652
  have hstable : (prefixWord ++ tailWord_6115652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115652).length < 2 ^ (prefixWord ++ tailWord_6115652).sum := by decide
  have hdescent : baseEnd_6115652 < baseStart_6115652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
