import V185TrunkScan23Chunk0282

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1672780 : List Nat := [2, 2, 1, 3, 1, 3, 2, 4, 1, 4]
def baseStart_1672780 : Nat := 118140960795 + 1672780 * 2 ^ 59
def prefixEnd_1672780 : Nat := 4983230072969 + 3 ^ 40 * 1672780 * 2
def baseEnd_1672780 : Nat := 286313389742690158085677

theorem tailTrace_1672780 : CollatzResearch.WordTrace tailWord_1672780 prefixEnd_1672780 286313389742690158085677 := by
  unfold tailWord_1672780
  simp only [CollatzResearch.WordTrace]
  refine ⟨30505649439905611462159897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40674199253207481949546529 30505649439905611462159897)
  ·
    refine ⟨22879237079929208596619923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30505649439905611462159897 22879237079929208596619923)
    ·
      refine ⟨34318855619893812894929885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22879237079929208596619923 34318855619893812894929885)
      ·
        refine ⟨12869570857460179835598707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34318855619893812894929885 12869570857460179835598707)
        ·
          refine ⟨19304356286190269753398061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12869570857460179835598707 19304356286190269753398061)
          ·
            refine ⟨7239133607321351157524273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19304356286190269753398061 7239133607321351157524273)
            ·
              refine ⟨5429350205491013368143205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7239133607321351157524273 5429350205491013368143205)
              ·
                refine ⟨1018003163529565006526851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5429350205491013368143205 1018003163529565006526851)
                ·
                  refine ⟨1527004745294347509790277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1018003163529565006526851 1527004745294347509790277)
                  ·
                    refine ⟨286313389742690158085677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1527004745294347509790277 286313389742690158085677)
                    ·
                      rfl

theorem cell23_1672780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 1, 4].length) (baseStart_1672780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672780 prefixEnd_1672780 := by exact prefixLift 1672780
  have htrace : WordTrace (prefixWord ++ tailWord_1672780) baseStart_1672780 baseEnd_1672780 := by
    simpa [prefixWord, tailWord_1672780, baseEnd_1672780] using wordTrace_append hprefix tailTrace_1672780
  have hstable : (prefixWord ++ tailWord_1672780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672780).length < 2 ^ (prefixWord ++ tailWord_1672780).sum := by decide
  have hdescent : baseEnd_1672780 < baseStart_1672780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672814 : List Nat := [4, 1, 2, 2, 3, 2, 1, 3, 1, 4]
def baseStart_1672814 : Nat := 118140960795 + 1672814 * 2 ^ 59
def prefixEnd_1672814 : Nat := 4983230072969 + 3 ^ 40 * 1672814 * 2
def baseEnd_1672814 : Nat := 286319209190107780410625

theorem tailTrace_1672814 : CollatzResearch.WordTrace tailWord_1672814 prefixEnd_1672814 286319209190107780410625 := by
  unfold tailWord_1672814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7626567370211005841382187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40675025974458697820704997 7626567370211005841382187)
  ·
    refine ⟨11439851055316508762073281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7626567370211005841382187 11439851055316508762073281)
    ·
      refine ⟨8579888291487381571554961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11439851055316508762073281 8579888291487381571554961)
      ·
        refine ⟨6434916218615536178666221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8579888291487381571554961 6434916218615536178666221)
        ·
          refine ⟨2413093581980826066999833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6434916218615536178666221 2413093581980826066999833)
          ·
            refine ⟨1809820186485619550249875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2413093581980826066999833 1809820186485619550249875)
            ·
              refine ⟨2714730279728429325374813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809820186485619550249875 2714730279728429325374813)
              ·
                refine ⟨1018023854898160997015555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2714730279728429325374813 1018023854898160997015555)
                ·
                  refine ⟨1527035782347241495523333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1018023854898160997015555 1527035782347241495523333)
                  ·
                    refine ⟨286319209190107780410625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1527035782347241495523333 286319209190107780410625)
                    ·
                      rfl

theorem cell23_1672814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_1672814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672814 prefixEnd_1672814 := by exact prefixLift 1672814
  have htrace : WordTrace (prefixWord ++ tailWord_1672814) baseStart_1672814 baseEnd_1672814 := by
    simpa [prefixWord, tailWord_1672814, baseEnd_1672814] using wordTrace_append hprefix tailTrace_1672814
  have hstable : (prefixWord ++ tailWord_1672814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672814).length < 2 ^ (prefixWord ++ tailWord_1672814).sum := by decide
  have hdescent : baseEnd_1672814 < baseStart_1672814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672860 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_1672860 : Nat := 118140960795 + 1672860 * 2 ^ 59
def prefixEnd_1672860 : Nat := 4983230072969 + 3 ^ 40 * 1672860 * 2
def baseEnd_1672860 : Nat := 858981247680430161256663

theorem tailTrace_1672860 : CollatzResearch.WordTrace tailWord_1672860 prefixEnd_1672860 858981247680430161256663 := by
  unfold tailWord_1672860
  simp only [CollatzResearch.WordTrace]
  refine ⟨30507108359760698293616017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40676144479680931058154689 30507108359760698293616017)
  ·
    refine ⟨22880331269820523720212013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30507108359760698293616017 22880331269820523720212013)
    ·
      refine ⟨8580124226182696395079505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22880331269820523720212013 8580124226182696395079505)
      ·
        refine ⟨6435093169637022296309629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8580124226182696395079505 6435093169637022296309629)
        ·
          refine ⟨2413159938613883361116111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6435093169637022296309629 2413159938613883361116111)
          ·
            refine ⟨3619739907920825041674167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413159938613883361116111 3619739907920825041674167)
            ·
              refine ⟨5429609861881237562511251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3619739907920825041674167 5429609861881237562511251)
              ·
                refine ⟨8144414792821856343766877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5429609861881237562511251 8144414792821856343766877)
                ·
                  refine ⟨3054155547308196128912579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8144414792821856343766877 3054155547308196128912579)
                  ·
                    refine ⟨4581233320962294193368869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3054155547308196128912579 4581233320962294193368869)
                    ·
                      refine ⟨858981247680430161256663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4581233320962294193368869 858981247680430161256663)
                      ·
                        rfl

theorem cell23_1672860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_1672860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672860 prefixEnd_1672860 := by exact prefixLift 1672860
  have htrace : WordTrace (prefixWord ++ tailWord_1672860) baseStart_1672860 baseEnd_1672860 := by
    simpa [prefixWord, tailWord_1672860, baseEnd_1672860] using wordTrace_append hprefix tailTrace_1672860
  have hstable : (prefixWord ++ tailWord_1672860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672860).length < 2 ^ (prefixWord ++ tailWord_1672860).sum := by decide
  have hdescent : baseEnd_1672860 < baseStart_1672860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672877 : List Nat := [1, 5, 2, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_1672877 : Nat := 118140960795 + 1672877 * 2 ^ 59
def prefixEnd_1672877 : Nat := 4983230072969 + 3 ^ 40 * 1672877 * 2
def baseEnd_1672877 : Nat := 858989976851556594744085

theorem tailTrace_1672877 : CollatzResearch.WordTrace tailWord_1672877 prefixEnd_1672877 858989976851556594744085 := by
  unfold tailWord_1672877
  simp only [CollatzResearch.WordTrace]
  refine ⟨61014836760459808490600885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40676557840306538993733923 61014836760459808490600885)
  ·
    refine ⟨5720140946293107045993833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61014836760459808490600885 5720140946293107045993833)
    ·
      refine ⟨4290105709719830284495375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5720140946293107045993833 4290105709719830284495375)
      ·
        refine ⟨6435158564579745426743063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4290105709719830284495375 6435158564579745426743063)
        ·
          refine ⟨9652737846869618140114595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6435158564579745426743063 9652737846869618140114595)
          ·
            refine ⟨14479106770304427210171893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9652737846869618140114595 14479106770304427210171893)
            ·
              refine ⟨1357416259716040050953615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14479106770304427210171893 1357416259716040050953615)
              ·
                refine ⟨2036124389574060076430423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357416259716040050953615 2036124389574060076430423)
                ·
                  refine ⟨3054186584361090114645635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036124389574060076430423 3054186584361090114645635)
                  ·
                    refine ⟨4581279876541635171968453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3054186584361090114645635 4581279876541635171968453)
                    ·
                      refine ⟨858989976851556594744085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4581279876541635171968453 858989976851556594744085)
                      ·
                        rfl

theorem cell23_1672877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_1672877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672877 prefixEnd_1672877 := by exact prefixLift 1672877
  have htrace : WordTrace (prefixWord ++ tailWord_1672877) baseStart_1672877 baseEnd_1672877 := by
    simpa [prefixWord, tailWord_1672877, baseEnd_1672877] using wordTrace_append hprefix tailTrace_1672877
  have hstable : (prefixWord ++ tailWord_1672877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672877).length < 2 ^ (prefixWord ++ tailWord_1672877).sum := by decide
  have hdescent : baseEnd_1672877 < baseStart_1672877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672893 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 3, 3, 3]
def baseStart_1672893 : Nat := 118140960795 + 1672893 * 2 ^ 59
def prefixEnd_1672893 : Nat := 4983230072969 + 3 ^ 40 * 1672893 * 2
def baseEnd_1672893 : Nat := 858998192542028532144011

theorem tailTrace_1672893 : CollatzResearch.WordTrace tailWord_1672893 prefixEnd_1672893 858998192542028532144011 := by
  unfold tailWord_1672893
  simp only [CollatzResearch.WordTrace]
  refine ⟨61015420328401843223183333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40676946885601228815455555 61015420328401843223183333)
  ·
    refine ⟨11440391311575345604346875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61015420328401843223183333 11440391311575345604346875)
    ·
      refine ⟨17160586967363018406520313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11440391311575345604346875 17160586967363018406520313)
      ·
        refine ⟨12870440225522263804890235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17160586967363018406520313 12870440225522263804890235)
        ·
          refine ⟨19305660338283395707335353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12870440225522263804890235 19305660338283395707335353)
          ·
            refine ⟨14479245253712546780501515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19305660338283395707335353 14479245253712546780501515)
            ·
              refine ⟨21718867880568820170752273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14479245253712546780501515 21718867880568820170752273)
              ·
                refine ⟨16289150910426615128064205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21718867880568820170752273 16289150910426615128064205)
                ·
                  refine ⟨6108431591409980673024077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16289150910426615128064205 6108431591409980673024077)
                  ·
                    refine ⟨2290661846778742752384029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6108431591409980673024077 2290661846778742752384029)
                    ·
                      refine ⟨858998192542028532144011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2290661846778742752384029 858998192542028532144011)
                      ·
                        rfl

theorem cell23_1672893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_1672893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672893 prefixEnd_1672893 := by exact prefixLift 1672893
  have htrace : WordTrace (prefixWord ++ tailWord_1672893) baseStart_1672893 baseEnd_1672893 := by
    simpa [prefixWord, tailWord_1672893, baseEnd_1672893] using wordTrace_append hprefix tailTrace_1672893
  have hstable : (prefixWord ++ tailWord_1672893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672893).length < 2 ^ (prefixWord ++ tailWord_1672893).sum := by decide
  have hdescent : baseEnd_1672893 < baseStart_1672893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672896 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 1, 9]
def baseStart_1672896 : Nat := 118140960795 + 1672896 * 2 ^ 59
def prefixEnd_1672896 : Nat := 4983230072969 + 3 ^ 40 * 1672896 * 2
def baseEnd_1672896 : Nat := 286333244327997340135499

theorem tailTrace_1672896 : CollatzResearch.WordTrace tailWord_1672896 prefixEnd_1672896 286333244327997340135499 := by
  unfold tailWord_1672896
  simp only [CollatzResearch.WordTrace]
  refine ⟨30507764873695487367771271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40677019831593983157028361 30507764873695487367771271)
  ·
    refine ⟨45761647310543231051656907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30507764873695487367771271 45761647310543231051656907)
    ·
      refine ⟨68642470965814846577485361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45761647310543231051656907 68642470965814846577485361)
      ·
        refine ⟨51481853224361134933114021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68642470965814846577485361 51481853224361134933114021)
        ·
          refine ⟨9652847479567712799958879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51481853224361134933114021 9652847479567712799958879)
          ·
            refine ⟨14479271219351569199938319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9652847479567712799958879 14479271219351569199938319)
            ·
              refine ⟨21718906829027353799907479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14479271219351569199938319 21718906829027353799907479)
              ·
                refine ⟨32578360243541030699861219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21718906829027353799907479 32578360243541030699861219)
                ·
                  refine ⟨48867540365311546049791829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32578360243541030699861219 48867540365311546049791829)
                  ·
                    refine ⟨286333244327997340135499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 48867540365311546049791829 286333244327997340135499)
                    ·
                      rfl

theorem cell23_1672896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 9].length) (baseStart_1672896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672896 prefixEnd_1672896 := by exact prefixLift 1672896
  have htrace : WordTrace (prefixWord ++ tailWord_1672896) baseStart_1672896 baseEnd_1672896 := by
    simpa [prefixWord, tailWord_1672896, baseEnd_1672896] using wordTrace_append hprefix tailTrace_1672896
  have hstable : (prefixWord ++ tailWord_1672896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672896).length < 2 ^ (prefixWord ++ tailWord_1672896).sum := by decide
  have hdescent : baseEnd_1672896 < baseStart_1672896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672910 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3]
def baseStart_1672910 : Nat := 118140960795 + 1672910 * 2 ^ 59
def prefixEnd_1672910 : Nat := 4983230072969 + 3 ^ 40 * 1672910 * 2
def baseEnd_1672910 : Nat := 859006921713154965631433

theorem tailTrace_1672910 : CollatzResearch.WordTrace tailWord_1672910 prefixEnd_1672910 859006921713154965631433 := by
  unfold tailWord_1672910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7627005046167531890819023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40677360246226836751034789 7627005046167531890819023)
  ·
    refine ⟨11440507569251297836228535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7627005046167531890819023 11440507569251297836228535)
    ·
      refine ⟨17160761353876946754342803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11440507569251297836228535 17160761353876946754342803)
      ·
        refine ⟨25741142030815420131514205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17160761353876946754342803 25741142030815420131514205)
        ·
          refine ⟨9652928261555782549317827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25741142030815420131514205 9652928261555782549317827)
          ·
            refine ⟨14479392392333673823976741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9652928261555782549317827 14479392392333673823976741)
            ·
              refine ⟨2714886073562563841995639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14479392392333673823976741 2714886073562563841995639)
              ·
                refine ⟨4072329110343845762993459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714886073562563841995639 4072329110343845762993459)
                ·
                  refine ⟨6108493665515768644490189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4072329110343845762993459 6108493665515768644490189)
                  ·
                    refine ⟨2290685124568413241683821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6108493665515768644490189 2290685124568413241683821)
                    ·
                      refine ⟨859006921713154965631433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2290685124568413241683821 859006921713154965631433)
                      ·
                        rfl

theorem cell23_1672910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_1672910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672910 prefixEnd_1672910 := by exact prefixLift 1672910
  have htrace : WordTrace (prefixWord ++ tailWord_1672910) baseStart_1672910 baseEnd_1672910 := by
    simpa [prefixWord, tailWord_1672910, baseEnd_1672910] using wordTrace_append hprefix tailTrace_1672910
  have hstable : (prefixWord ++ tailWord_1672910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672910).length < 2 ^ (prefixWord ++ tailWord_1672910).sum := by decide
  have hdescent : baseEnd_1672910 < baseStart_1672910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672920 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 3, 3, 2]
def baseStart_1672920 : Nat := 118140960795 + 1672920 * 2 ^ 59
def prefixEnd_1672920 : Nat := 4983230072969 + 3 ^ 40 * 1672920 * 2
def baseEnd_1672920 : Nat := 859012056519699926506387

theorem tailTrace_1672920 : CollatzResearch.WordTrace tailWord_1672920 prefixEnd_1672920 859012056519699926506387 := by
  unfold tailWord_1672920
  simp only [CollatzResearch.WordTrace]
  refine ⟨30508202549652013417208107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40677603399536017889610809 30508202549652013417208107)
  ·
    refine ⟨45762303824478020125812161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30508202549652013417208107 45762303824478020125812161)
    ·
      refine ⟨34321727868358515094359121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45762303824478020125812161 34321727868358515094359121)
      ·
        refine ⟨25741295901268886320769341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34321727868358515094359121 25741295901268886320769341)
        ·
          refine ⟨9652985962975832370288503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25741295901268886320769341 9652985962975832370288503)
          ·
            refine ⟨14479478944463748555432755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9652985962975832370288503 14479478944463748555432755)
            ·
              refine ⟨21719218416695622833149133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14479478944463748555432755 21719218416695622833149133)
              ·
                refine ⟨8144706906260858562430925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21719218416695622833149133 8144706906260858562430925)
                ·
                  refine ⟨3054265089847821960911597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8144706906260858562430925 3054265089847821960911597)
                  ·
                    refine ⟨1145349408692933235341849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3054265089847821960911597 1145349408692933235341849)
                    ·
                      refine ⟨859012056519699926506387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1145349408692933235341849 859012056519699926506387)
                      ·
                        rfl

theorem cell23_1672920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_1672920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672920 prefixEnd_1672920 := by exact prefixLift 1672920
  have htrace : WordTrace (prefixWord ++ tailWord_1672920) baseStart_1672920 baseEnd_1672920 := by
    simpa [prefixWord, tailWord_1672920, baseEnd_1672920] using wordTrace_append hprefix tailTrace_1672920
  have hstable : (prefixWord ++ tailWord_1672920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672920).length < 2 ^ (prefixWord ++ tailWord_1672920).sum := by decide
  have hdescent : baseEnd_1672920 < baseStart_1672920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672931 : List Nat := [1, 1, 1, 7, 3, 1, 2, 1, 1, 2, 3]
def baseStart_1672931 : Nat := 118140960795 + 1672931 * 2 ^ 59
def prefixEnd_1672931 : Nat := 4983230072969 + 3 ^ 40 * 1672931 * 2
def baseEnd_1672931 : Nat := 859017704806899383468837

theorem tailTrace_1672931 : CollatzResearch.WordTrace tailWord_1672931 prefixEnd_1672931 859017704806899383468837 := by
  unfold tailWord_1672931
  simp only [CollatzResearch.WordTrace]
  refine ⟨61016806302264175713066647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40677870868176117142044431 61016806302264175713066647)
  ·
    refine ⟨91525209453396263569599971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61016806302264175713066647 91525209453396263569599971)
    ·
      refine ⟨137287814180094395354399957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91525209453396263569599971 137287814180094395354399957)
      ·
        refine ⟨3217683144845962391118749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 137287814180094395354399957 3217683144845962391118749)
        ·
          refine ⟨1206631179317235896669531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3217683144845962391118749 1206631179317235896669531)
          ·
            refine ⟨1809946768975853845004297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206631179317235896669531 1809946768975853845004297)
            ·
              refine ⟨1357460076731890383753223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1809946768975853845004297 1357460076731890383753223)
              ·
                refine ⟨2036190115097835575629835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357460076731890383753223 2036190115097835575629835)
                ·
                  refine ⟨3054285172646753363444753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036190115097835575629835 3054285172646753363444753)
                  ·
                    refine ⟨2290713879485065022583565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3054285172646753363444753 2290713879485065022583565)
                    ·
                      refine ⟨859017704806899383468837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2290713879485065022583565 859017704806899383468837)
                      ·
                        rfl

theorem cell23_1672931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_1672931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672931 prefixEnd_1672931 := by exact prefixLift 1672931
  have htrace : WordTrace (prefixWord ++ tailWord_1672931) baseStart_1672931 baseEnd_1672931 := by
    simpa [prefixWord, tailWord_1672931, baseEnd_1672931] using wordTrace_append hprefix tailTrace_1672931
  have hstable : (prefixWord ++ tailWord_1672931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672931).length < 2 ^ (prefixWord ++ tailWord_1672931).sum := by decide
  have hdescent : baseEnd_1672931 < baseStart_1672931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672963 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 4]
def baseStart_1672963 : Nat := 118140960795 + 1672963 * 2 ^ 59
def prefixEnd_1672963 : Nat := 4983230072969 + 3 ^ 40 * 1672963 * 2
def baseEnd_1672963 : Nat := 859034136187843258268689

theorem tailTrace_1672963 : CollatzResearch.WordTrace tailWord_1672963 prefixEnd_1672963 859034136187843258268689 := by
  unfold tailWord_1672963
  simp only [CollatzResearch.WordTrace]
  refine ⟨61017973438148245178231543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40678648958765496785487695 61017973438148245178231543)
  ·
    refine ⟨91526960157222367767347315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61017973438148245178231543 91526960157222367767347315)
    ·
      refine ⟨137290440235833551651020973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91526960157222367767347315 137290440235833551651020973)
      ·
        refine ⟨51483915088437581869132865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137290440235833551651020973 51483915088437581869132865)
        ·
          refine ⟨38612936316328186401849649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51483915088437581869132865 38612936316328186401849649)
          ·
            refine ⟨28959702237246139801387237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38612936316328186401849649 28959702237246139801387237)
            ·
              refine ⟨5429944169483651212760107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28959702237246139801387237 5429944169483651212760107)
              ·
                refine ⟨8144916254225476819140161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5429944169483651212760107 8144916254225476819140161)
                ·
                  refine ⟨6108687190669107614355121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8144916254225476819140161 6108687190669107614355121)
                  ·
                    refine ⟨4581515393001830710766341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6108687190669107614355121 4581515393001830710766341)
                    ·
                      refine ⟨859034136187843258268689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4581515393001830710766341 859034136187843258268689)
                      ·
                        rfl

theorem cell23_1672963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_1672963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1672963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1672963 prefixEnd_1672963 := by exact prefixLift 1672963
  have htrace : WordTrace (prefixWord ++ tailWord_1672963) baseStart_1672963 baseEnd_1672963 := by
    simpa [prefixWord, tailWord_1672963, baseEnd_1672963] using wordTrace_append hprefix tailTrace_1672963
  have hstable : (prefixWord ++ tailWord_1672963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672963).length < 2 ^ (prefixWord ++ tailWord_1672963).sum := by decide
  have hdescent : baseEnd_1672963 < baseStart_1672963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673037 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_1673037 : Nat := 118140960795 + 1673037 * 2 ^ 59
def prefixEnd_1673037 : Nat := 4983230072969 + 3 ^ 40 * 1673037 * 2
def baseEnd_1673037 : Nat := 286357377918758656247783

theorem tailTrace_1673037 : CollatzResearch.WordTrace tailWord_1673037 prefixEnd_1673037 286357377918758656247783 := by
  unfold tailWord_1673037
  simp only [CollatzResearch.WordTrace]
  refine ⟨61020672439880155816425365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40680448293253437210950243 61020672439880155816425365)
  ·
    refine ⟨2860344020619382303894939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61020672439880155816425365 2860344020619382303894939)
    ·
      refine ⟨4290516030929073455842409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2860344020619382303894939 4290516030929073455842409)
      ·
        refine ⟨3217887023196805091881807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4290516030929073455842409 3217887023196805091881807)
        ·
          refine ⟨4826830534795207637822711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3217887023196805091881807 4826830534795207637822711)
          ·
            refine ⟨7240245802192811456734067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826830534795207637822711 7240245802192811456734067)
            ·
              refine ⟨10860368703289217185101101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7240245802192811456734067 10860368703289217185101101)
              ·
                refine ⟨4072638263733456444412913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10860368703289217185101101 4072638263733456444412913)
                ·
                  refine ⟨3054478697800092333309685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4072638263733456444412913 3054478697800092333309685)
                  ·
                    refine ⟨286357377918758656247783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3054478697800092333309685 286357377918758656247783)
                    ·
                      rfl

theorem cell23_1673037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_1673037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673037 prefixEnd_1673037 := by exact prefixLift 1673037
  have htrace : WordTrace (prefixWord ++ tailWord_1673037) baseStart_1673037 baseEnd_1673037 := by
    simpa [prefixWord, tailWord_1673037, baseEnd_1673037] using wordTrace_append hprefix tailTrace_1673037
  have hstable : (prefixWord ++ tailWord_1673037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673037).length < 2 ^ (prefixWord ++ tailWord_1673037).sum := by decide
  have hdescent : baseEnd_1673037 < baseStart_1673037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673040 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 4, 4, 2]
def baseStart_1673040 : Nat := 118140960795 + 1673040 * 2 ^ 59
def prefixEnd_1673040 : Nat := 4983230072969 + 3 ^ 40 * 1673040 * 2
def baseEnd_1673040 : Nat := 859073674198239457005835

theorem tailTrace_1673040 : CollatzResearch.WordTrace tailWord_1673040 prefixEnd_1673040 859073674198239457005835 := by
  unfold tailWord_1673040
  simp only [CollatzResearch.WordTrace]
  refine ⟨30510390929434643664392287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40680521239246191552523049 30510390929434643664392287)
  ·
    refine ⟨45765586394151965496588431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30510390929434643664392287 45765586394151965496588431)
    ·
      refine ⟨68648379591227948244882647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45765586394151965496588431 68648379591227948244882647)
      ·
        refine ⟨102972569386841922367323971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68648379591227948244882647 102972569386841922367323971)
        ·
          refine ⟨154458854080262883550985957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102972569386841922367323971 154458854080262883550985957)
          ·
            refine ⟨28961035140049290665809867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154458854080262883550985957 28961035140049290665809867)
            ·
              refine ⟨43441552710073935998714801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28961035140049290665809867 43441552710073935998714801)
              ·
                refine ⟨32581164532555451999036101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43441552710073935998714801 32581164532555451999036101)
                ·
                  refine ⟨6108968349854147249819269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32581164532555451999036101 6108968349854147249819269)
                  ·
                    refine ⟨1145431565597652609341113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6108968349854147249819269 1145431565597652609341113)
                    ·
                      refine ⟨859073674198239457005835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1145431565597652609341113 859073674198239457005835)
                      ·
                        rfl

theorem cell23_1673040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4, 4, 2].length) (baseStart_1673040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673040 prefixEnd_1673040 := by exact prefixLift 1673040
  have htrace : WordTrace (prefixWord ++ tailWord_1673040) baseStart_1673040 baseEnd_1673040 := by
    simpa [prefixWord, tailWord_1673040, baseEnd_1673040] using wordTrace_append hprefix tailTrace_1673040
  have hstable : (prefixWord ++ tailWord_1673040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673040).length < 2 ^ (prefixWord ++ tailWord_1673040).sum := by decide
  have hdescent : baseEnd_1673040 < baseStart_1673040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673124 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 3, 1, 3]
def baseStart_1673124 : Nat := 118140960795 + 1673124 * 2 ^ 59
def prefixEnd_1673124 : Nat := 4983230072969 + 3 ^ 40 * 1673124 * 2
def baseEnd_1673124 : Nat := 859116806573217128355449

theorem tailTrace_1673124 : CollatzResearch.WordTrace tailWord_1673124 prefixEnd_1673124 859116806573217128355449 := by
  unfold tailWord_1673124
  simp only [CollatzResearch.WordTrace]
  refine ⟨30511922795282484837421213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40682563727043313116561617 30511922795282484837421213)
  ·
    refine ⟨11441971048230931814032955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30511922795282484837421213 11441971048230931814032955)
    ·
      refine ⟨17162956572346397721049433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11441971048230931814032955 17162956572346397721049433)
      ·
        refine ⟨12872217429259798290787075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17162956572346397721049433 12872217429259798290787075)
        ·
          refine ⟨19308326143889697436180613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12872217429259798290787075 19308326143889697436180613)
          ·
            refine ⟨3620311151979318269283865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19308326143889697436180613 3620311151979318269283865)
            ·
              refine ⟨2715233363984488701962899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3620311151979318269283865 2715233363984488701962899)
              ·
                refine ⟨4072850045976733052944349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2715233363984488701962899 4072850045976733052944349)
                ·
                  refine ⟨1527318767241274894854131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4072850045976733052944349 1527318767241274894854131)
                  ·
                    refine ⟨2290978150861912342281197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1527318767241274894854131 2290978150861912342281197)
                    ·
                      refine ⟨859116806573217128355449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2290978150861912342281197 859116806573217128355449)
                      ·
                        rfl

theorem cell23_1673124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_1673124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673124 prefixEnd_1673124 := by exact prefixLift 1673124
  have htrace : WordTrace (prefixWord ++ tailWord_1673124) baseStart_1673124 baseEnd_1673124 := by
    simpa [prefixWord, tailWord_1673124, baseEnd_1673124] using wordTrace_append hprefix tailTrace_1673124
  have hstable : (prefixWord ++ tailWord_1673124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673124).length < 2 ^ (prefixWord ++ tailWord_1673124).sum := by decide
  have hdescent : baseEnd_1673124 < baseStart_1673124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673167 : List Nat := [1, 1, 2, 1, 1, 5, 1, 5, 1, 2, 3]
def baseStart_1673167 : Nat := 118140960795 + 1673167 * 2 ^ 59
def prefixEnd_1673167 : Nat := 4983230072969 + 3 ^ 40 * 1673167 * 2
def baseEnd_1673167 : Nat := 859138886241360460117751

theorem tailTrace_1673167 : CollatzResearch.WordTrace tailWord_1673167 prefixEnd_1673167 859138886241360460117751 := by
  unfold tailWord_1673167
  simp only [CollatzResearch.WordTrace]
  refine ⟨61025413929409188018657755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40683609286272792012438503 61025413929409188018657755)
  ·
    refine ⟨91538120894113782027986633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61025413929409188018657755 91538120894113782027986633)
    ·
      refine ⟨68653590670585336520989975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91538120894113782027986633 68653590670585336520989975)
      ·
        refine ⟨102980386005878004781484963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68653590670585336520989975 102980386005878004781484963)
        ·
          refine ⟨154470579008817007172227445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102980386005878004781484963 154470579008817007172227445)
          ·
            refine ⟨14481616782076594422396323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154470579008817007172227445 14481616782076594422396323)
            ·
              refine ⟨21722425173114891633594485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14481616782076594422396323 21722425173114891633594485)
              ·
                refine ⟨2036477359979521090649483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21722425173114891633594485 2036477359979521090649483)
                ·
                  refine ⟨3054716039969281635974225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036477359979521090649483 3054716039969281635974225)
                  ·
                    refine ⟨2291037029976961226980669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3054716039969281635974225 2291037029976961226980669)
                    ·
                      refine ⟨859138886241360460117751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2291037029976961226980669 859138886241360460117751)
                      ·
                        rfl

theorem cell23_1673167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 2, 3].length) (baseStart_1673167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673167 prefixEnd_1673167 := by exact prefixLift 1673167
  have htrace : WordTrace (prefixWord ++ tailWord_1673167) baseStart_1673167 baseEnd_1673167 := by
    simpa [prefixWord, tailWord_1673167, baseEnd_1673167] using wordTrace_append hprefix tailTrace_1673167
  have hstable : (prefixWord ++ tailWord_1673167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673167).length < 2 ^ (prefixWord ++ tailWord_1673167).sum := by decide
  have hdescent : baseEnd_1673167 < baseStart_1673167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673201 : List Nat := [1, 2, 2, 2, 5, 2, 1, 2, 1, 2, 3]
def baseStart_1673201 : Nat := 118140960795 + 1673201 * 2 ^ 59
def prefixEnd_1673201 : Nat := 4983230072969 + 3 ^ 40 * 1673201 * 2
def baseEnd_1673201 : Nat := 859156344583613327092595

theorem tailTrace_1673201 : CollatzResearch.WordTrace tailWord_1673201 prefixEnd_1673201 859156344583613327092595 := by
  unfold tailWord_1673201
  simp only [CollatzResearch.WordTrace]
  refine ⟨61026654011286011825395457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40684436007524007883596971 61026654011286011825395457)
  ·
    refine ⟨45769990508464508869046593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61026654011286011825395457 45769990508464508869046593)
    ·
      refine ⟨34327492881348381651784945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45769990508464508869046593 34327492881348381651784945)
      ·
        refine ⟨25745619661011286238838709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34327492881348381651784945 25745619661011286238838709)
        ·
          refine ⟨2413651843219808084891129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25745619661011286238838709 2413651843219808084891129)
          ·
            refine ⟨1810238882414856063668347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2413651843219808084891129 1810238882414856063668347)
            ·
              refine ⟨2715358323622284095502521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810238882414856063668347 2715358323622284095502521)
              ·
                refine ⟨2036518742716713071626891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2715358323622284095502521 2036518742716713071626891)
                ·
                  refine ⟨3054778114075069607440337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036518742716713071626891 3054778114075069607440337)
                  ·
                    refine ⟨2291083585556302205580253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3054778114075069607440337 2291083585556302205580253)
                    ·
                      refine ⟨859156344583613327092595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2291083585556302205580253 859156344583613327092595)
                      ·
                        rfl

theorem cell23_1673201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_1673201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673201 prefixEnd_1673201 := by exact prefixLift 1673201
  have htrace : WordTrace (prefixWord ++ tailWord_1673201) baseStart_1673201 baseEnd_1673201 := by
    simpa [prefixWord, tailWord_1673201, baseEnd_1673201] using wordTrace_append hprefix tailTrace_1673201
  have hstable : (prefixWord ++ tailWord_1673201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673201).length < 2 ^ (prefixWord ++ tailWord_1673201).sum := by decide
  have hdescent : baseEnd_1673201 < baseStart_1673201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673214 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1673214 : Nat := 118140960795 + 1673214 * 2 ^ 59
def prefixEnd_1673214 : Nat := 4983230072969 + 3 ^ 40 * 1673214 * 2
def baseEnd_1673214 : Nat := 859163019832121776230035

theorem tailTrace_1673214 : CollatzResearch.WordTrace tailWord_1673214 prefixEnd_1673214 859163019832121776230035 := by
  unfold tailWord_1673214
  simp only [CollatzResearch.WordTrace]
  refine ⟨7628391020029864380702337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40684752106825943363745797 7628391020029864380702337)
  ·
    refine ⟨5721293265022398285526753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7628391020029864380702337 5721293265022398285526753)
    ·
      refine ⟨4290969948766798714145065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5721293265022398285526753 4290969948766798714145065)
      ·
        refine ⟨3218227461575099035608799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4290969948766798714145065 3218227461575099035608799)
        ·
          refine ⟨4827341192362648553413199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3218227461575099035608799 4827341192362648553413199)
          ·
            refine ⟨7241011788543972830119799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4827341192362648553413199 7241011788543972830119799)
            ·
              refine ⟨10861517682815959245179699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7241011788543972830119799 10861517682815959245179699)
              ·
                refine ⟨16292276524223938867769549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10861517682815959245179699 16292276524223938867769549)
                ·
                  refine ⟨6109603696583977075413581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16292276524223938867769549 6109603696583977075413581)
                  ·
                    refine ⟨2291101386218991403280093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6109603696583977075413581 2291101386218991403280093)
                    ·
                      refine ⟨859163019832121776230035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2291101386218991403280093 859163019832121776230035)
                      ·
                        rfl

theorem cell23_1673214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1673214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673214 prefixEnd_1673214 := by exact prefixLift 1673214
  have htrace : WordTrace (prefixWord ++ tailWord_1673214) baseStart_1673214 baseEnd_1673214 := by
    simpa [prefixWord, tailWord_1673214, baseEnd_1673214] using wordTrace_append hprefix tailTrace_1673214
  have hstable : (prefixWord ++ tailWord_1673214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673214).length < 2 ^ (prefixWord ++ tailWord_1673214).sum := by decide
  have hdescent : baseEnd_1673214 < baseStart_1673214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673287 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 3]
def baseStart_1673287 : Nat := 118140960795 + 1673287 * 2 ^ 59
def prefixEnd_1673287 : Nat := 4983230072969 + 3 ^ 40 * 1673287 * 2
def baseEnd_1673287 : Nat := 859200503919899990617199

theorem tailTrace_1673287 : CollatzResearch.WordTrace tailWord_1673287 prefixEnd_1673287 859200503919899990617199 := by
  unfold tailWord_1673287
  simp only [CollatzResearch.WordTrace]
  refine ⟨61029790688974448513026115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40686527125982965675350743 61029790688974448513026115)
  ·
    refine ⟨91544686033461672769539173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61029790688974448513026115 91544686033461672769539173)
    ·
      refine ⟨17164628631274063644288595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91544686033461672769539173 17164628631274063644288595)
      ·
        refine ⟨25746942946911095466432893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17164628631274063644288595 25746942946911095466432893)
        ·
          refine ⟨9655103605091660799912335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25746942946911095466432893 9655103605091660799912335)
          ·
            refine ⟨14482655407637491199868503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9655103605091660799912335 14482655407637491199868503)
            ·
              refine ⟨21723983111456236799802755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14482655407637491199868503 21723983111456236799802755)
              ·
                refine ⟨32585974667184355199704133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21723983111456236799802755 32585974667184355199704133)
                ·
                  refine ⟨6109870250097066599944525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32585974667184355199704133 6109870250097066599944525)
                  ·
                    refine ⟨2291201343786399974979197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6109870250097066599944525 2291201343786399974979197)
                    ·
                      refine ⟨859200503919899990617199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2291201343786399974979197 859200503919899990617199)
                      ·
                        rfl

theorem cell23_1673287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_1673287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673287 prefixEnd_1673287 := by exact prefixLift 1673287
  have htrace : WordTrace (prefixWord ++ tailWord_1673287) baseStart_1673287 baseEnd_1673287 := by
    simpa [prefixWord, tailWord_1673287, baseEnd_1673287] using wordTrace_append hprefix tailTrace_1673287
  have hstable : (prefixWord ++ tailWord_1673287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673287).length < 2 ^ (prefixWord ++ tailWord_1673287).sum := by decide
  have hdescent : baseEnd_1673287 < baseStart_1673287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673294 : List Nat := [4, 1, 1, 1, 1, 4, 2, 4, 5]
def baseStart_1673294 : Nat := 118140960795 + 1673294 * 2 ^ 59
def prefixEnd_1673294 : Nat := 4983230072969 + 3 ^ 40 * 1673294 * 2
def baseEnd_1673294 : Nat := 95467122031609051469963

theorem tailTrace_1673294 : CollatzResearch.WordTrace tailWord_1673294 prefixEnd_1673294 95467122031609051469963 := by
  unfold tailWord_1673294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7628755749993636088566367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40686697333299392472353957 7628755749993636088566367)
  ·
    refine ⟨11443133624990454132849551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7628755749993636088566367 11443133624990454132849551)
    ·
      refine ⟨17164700437485681199274327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11443133624990454132849551 17164700437485681199274327)
      ·
        refine ⟨25747050656228521798911491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17164700437485681199274327 25747050656228521798911491)
        ·
          refine ⟨38620575984342782698367237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25747050656228521798911491 38620575984342782698367237)
          ·
            refine ⟨7241357997064271755943857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38620575984342782698367237 7241357997064271755943857)
            ·
              refine ⟨5431018497798203816957893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7241357997064271755943857 5431018497798203816957893)
              ·
                refine ⟨1018315968337163215679605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5431018497798203816957893 1018315968337163215679605)
                ·
                  refine ⟨95467122031609051469963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1018315968337163215679605 95467122031609051469963)
                  ·
                    rfl

theorem cell23_1673294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_1673294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673294 prefixEnd_1673294 := by exact prefixLift 1673294
  have htrace : WordTrace (prefixWord ++ tailWord_1673294) baseStart_1673294 baseEnd_1673294 := by
    simpa [prefixWord, tailWord_1673294, baseEnd_1673294] using wordTrace_append hprefix tailTrace_1673294
  have hstable : (prefixWord ++ tailWord_1673294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673294).length < 2 ^ (prefixWord ++ tailWord_1673294).sum := by decide
  have hdescent : baseEnd_1673294 < baseStart_1673294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673327 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 4]
def baseStart_1673327 : Nat := 118140960795 + 1673327 * 2 ^ 59
def prefixEnd_1673327 : Nat := 4983230072969 + 3 ^ 40 * 1673327 * 2
def baseEnd_1673327 : Nat := 859221043146079834117015

theorem tailTrace_1673327 : CollatzResearch.WordTrace tailWord_1673327 prefixEnd_1673327 859221043146079834117015 := by
  unfold tailWord_1673327
  simp only [CollatzResearch.WordTrace]
  refine ⟨61031249608829535344482235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40687499739219690229654823 61031249608829535344482235)
  ·
    refine ⟨91546874413244303016723353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61031249608829535344482235 91546874413244303016723353)
    ·
      refine ⟨68660155809933227262542515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91546874413244303016723353 68660155809933227262542515)
      ·
        refine ⟨102990233714899840893813773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68660155809933227262542515 102990233714899840893813773)
        ·
          refine ⟨38621337643087440335180165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102990233714899840893813773 38621337643087440335180165)
          ·
            refine ⟨7241500808078895062846281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38621337643087440335180165 7241500808078895062846281)
            ·
              refine ⟨5431125606059171297134711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7241500808078895062846281 5431125606059171297134711)
              ·
                refine ⟨8146688409088756945702067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5431125606059171297134711 8146688409088756945702067)
                ·
                  refine ⟨12220032613633135418553101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8146688409088756945702067 12220032613633135418553101)
                  ·
                    refine ⟨4582512230112425781957413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12220032613633135418553101 4582512230112425781957413)
                    ·
                      refine ⟨859221043146079834117015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4582512230112425781957413 859221043146079834117015)
                      ·
                        rfl

theorem cell23_1673327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_1673327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673327 prefixEnd_1673327 := by exact prefixLift 1673327
  have htrace : WordTrace (prefixWord ++ tailWord_1673327) baseStart_1673327 baseEnd_1673327 := by
    simpa [prefixWord, tailWord_1673327, baseEnd_1673327] using wordTrace_append hprefix tailTrace_1673327
  have hstable : (prefixWord ++ tailWord_1673327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673327).length < 2 ^ (prefixWord ++ tailWord_1673327).sum := by decide
  have hdescent : baseEnd_1673327 < baseStart_1673327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673434 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4]
def baseStart_1673434 : Nat := 118140960795 + 1673434 * 2 ^ 59
def prefixEnd_1673434 : Nat := 4983230072969 + 3 ^ 40 * 1673434 * 2
def baseEnd_1673434 : Nat := 859275985576110915479023

theorem tailTrace_1673434 : CollatzResearch.WordTrace tailWord_1673434 prefixEnd_1673434 859275985576110915479023 := by
  unfold tailWord_1673434
  simp only [CollatzResearch.WordTrace]
  refine ⟨15258788054860473154656839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40690101479627928412418237 15258788054860473154656839)
  ·
    refine ⟨22888182082290709731985259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15258788054860473154656839 22888182082290709731985259)
    ·
      refine ⟨34332273123436064597977889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22888182082290709731985259 34332273123436064597977889)
      ·
        refine ⟨25749204842577048448483417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34332273123436064597977889 25749204842577048448483417)
        ·
          refine ⟨19311903631932786336362563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25749204842577048448483417 19311903631932786336362563)
          ·
            refine ⟨28967855447899179504543845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19311903631932786336362563 28967855447899179504543845)
            ·
              refine ⟨5431472896481096157101971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28967855447899179504543845 5431472896481096157101971)
              ·
                refine ⟨8147209344721644235652957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5431472896481096157101971 8147209344721644235652957)
                ·
                  refine ⟨3055203504270616588369859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8147209344721644235652957 3055203504270616588369859)
                  ·
                    refine ⟨4582805256405924882554789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3055203504270616588369859 4582805256405924882554789)
                    ·
                      refine ⟨859275985576110915479023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4582805256405924882554789 859275985576110915479023)
                      ·
                        rfl

theorem cell23_1673434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_1673434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673434 prefixEnd_1673434 := by exact prefixLift 1673434
  have htrace : WordTrace (prefixWord ++ tailWord_1673434) baseStart_1673434 baseEnd_1673434 := by
    simpa [prefixWord, tailWord_1673434, baseEnd_1673434] using wordTrace_append hprefix tailTrace_1673434
  have hstable : (prefixWord ++ tailWord_1673434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673434).length < 2 ^ (prefixWord ++ tailWord_1673434).sum := by decide
  have hdescent : baseEnd_1673434 < baseStart_1673434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673444 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 4, 4]
def baseStart_1673444 : Nat := 118140960795 + 1673444 * 2 ^ 59
def prefixEnd_1673444 : Nat := 4983230072969 + 3 ^ 40 * 1673444 * 2
def baseEnd_1673444 : Nat := 286427040127551958784659

theorem tailTrace_1673444 : CollatzResearch.WordTrace tailWord_1673444 prefixEnd_1673444 286427040127551958784659 := by
  unfold tailWord_1673444
  simp only [CollatzResearch.WordTrace]
  refine ⟨30517758474702832163245693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40690344632937109550994257 30517758474702832163245693)
  ·
    refine ⟨11444159428013562061217135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30517758474702832163245693 11444159428013562061217135)
    ·
      refine ⟨17166239142020343091825703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11444159428013562061217135 17166239142020343091825703)
      ·
        refine ⟨25749358713030514637738555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17166239142020343091825703 25749358713030514637738555)
        ·
          refine ⟨38624038069545771956607833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25749358713030514637738555 38624038069545771956607833)
          ·
            refine ⟨28968028552159328967455875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38624038069545771956607833 28968028552159328967455875)
            ·
              refine ⟨43452042828238993451183813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28968028552159328967455875 43452042828238993451183813)
              ·
                refine ⟨8147258030294811272096965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43452042828238993451183813 8147258030294811272096965)
                ·
                  refine ⟨1527610880680277113518181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8147258030294811272096965 1527610880680277113518181)
                  ·
                    refine ⟨286427040127551958784659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1527610880680277113518181 286427040127551958784659)
                    ·
                      rfl

theorem cell23_1673444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_1673444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673444 prefixEnd_1673444 := by exact prefixLift 1673444
  have htrace : WordTrace (prefixWord ++ tailWord_1673444) baseStart_1673444 baseEnd_1673444 := by
    simpa [prefixWord, tailWord_1673444, baseEnd_1673444] using wordTrace_append hprefix tailTrace_1673444
  have hstable : (prefixWord ++ tailWord_1673444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673444).length < 2 ^ (prefixWord ++ tailWord_1673444).sum := by decide
  have hdescent : baseEnd_1673444 < baseStart_1673444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673445 : List Nat := [1, 3, 1, 4, 2, 2, 2, 3, 1, 1, 3]
def baseStart_1673445 : Nat := 118140960795 + 1673445 * 2 ^ 59
def prefixEnd_1673445 : Nat := 4983230072969 + 3 ^ 40 * 1673445 * 2
def baseEnd_1673445 : Nat := 859281633863310372441473

theorem tailTrace_1673445 : CollatzResearch.WordTrace tailWord_1673445 prefixEnd_1673445 859281633863310372441473 := by
  unfold tailWord_1673445
  simp only [CollatzResearch.WordTrace]
  refine ⟨61035553422402041497277789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40690368948268027664851859 61035553422402041497277789)
  ·
    refine ⟨22888332533400765561479171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61035553422402041497277789 22888332533400765561479171)
    ·
      refine ⟨34332498800101148342218757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22888332533400765561479171 34332498800101148342218757)
      ·
        refine ⟨6437343525018965314166017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34332498800101148342218757 6437343525018965314166017)
        ·
          refine ⟨4828007643764223985624513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6437343525018965314166017 4828007643764223985624513)
          ·
            refine ⟨3621005732823167989218385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4828007643764223985624513 3621005732823167989218385)
            ·
              refine ⟨2715754299617375991913789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3621005732823167989218385 2715754299617375991913789)
              ·
                refine ⟨1018407862356515996967671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2715754299617375991913789 1018407862356515996967671)
                ·
                  refine ⟨1527611793534773995451507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1018407862356515996967671 1527611793534773995451507)
                  ·
                    refine ⟨2291417690302160993177261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1527611793534773995451507 2291417690302160993177261)
                    ·
                      refine ⟨859281633863310372441473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2291417690302160993177261 859281633863310372441473)
                      ·
                        rfl

theorem cell23_1673445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_1673445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673445 prefixEnd_1673445 := by exact prefixLift 1673445
  have htrace : WordTrace (prefixWord ++ tailWord_1673445) baseStart_1673445 baseEnd_1673445 := by
    simpa [prefixWord, tailWord_1673445, baseEnd_1673445] using wordTrace_append hprefix tailTrace_1673445
  have hstable : (prefixWord ++ tailWord_1673445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673445).length < 2 ^ (prefixWord ++ tailWord_1673445).sum := by decide
  have hdescent : baseEnd_1673445 < baseStart_1673445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673448 : List Nat := [2, 1, 4, 1, 2, 4, 2, 1, 1, 5]
def baseStart_1673448 : Nat := 118140960795 + 1673448 * 2 ^ 59
def prefixEnd_1673448 : Nat := 4983230072969 + 3 ^ 40 * 1673448 * 2
def baseEnd_1673448 : Nat := 286427724768424620234653

theorem tailTrace_1673448 : CollatzResearch.WordTrace tailWord_1673448 prefixEnd_1673448 286427724768424620234653 := by
  unfold tailWord_1673448
  simp only [CollatzResearch.WordTrace]
  refine ⟨30517831420695586504818499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40690441894260782006424665 30517831420695586504818499)
  ·
    refine ⟨45776747131043379757227749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30517831420695586504818499 45776747131043379757227749)
    ·
      refine ⟨8583140087070633704480203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45776747131043379757227749 8583140087070633704480203)
      ·
        refine ⟨12874710130605950556720305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8583140087070633704480203 12874710130605950556720305)
        ·
          refine ⟨9656032597954462917540229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12874710130605950556720305 9656032597954462917540229)
          ·
            refine ⟨1810506112116461797038793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9656032597954462917540229 1810506112116461797038793)
            ·
              refine ⟨1357879584087346347779095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1810506112116461797038793 1357879584087346347779095)
              ·
                refine ⟨2036819376131019521668643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357879584087346347779095 2036819376131019521668643)
                ·
                  refine ⟨3055229064196529282502965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036819376131019521668643 3055229064196529282502965)
                  ·
                    refine ⟨286427724768424620234653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3055229064196529282502965 286427724768424620234653)
                    ·
                      rfl

theorem cell23_1673448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_1673448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673448 prefixEnd_1673448 := by exact prefixLift 1673448
  have htrace : WordTrace (prefixWord ++ tailWord_1673448) baseStart_1673448 baseEnd_1673448 := by
    simpa [prefixWord, tailWord_1673448, baseEnd_1673448] using wordTrace_append hprefix tailTrace_1673448
  have hstable : (prefixWord ++ tailWord_1673448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673448).length < 2 ^ (prefixWord ++ tailWord_1673448).sum := by decide
  have hdescent : baseEnd_1673448 < baseStart_1673448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673451 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 5, 2, 2]
def baseStart_1673451 : Nat := 118140960795 + 1673451 * 2 ^ 59
def prefixEnd_1673451 : Nat := 4983230072969 + 3 ^ 40 * 1673451 * 2
def baseEnd_1673451 : Nat := 859284714747237348966445

theorem tailTrace_1673451 : CollatzResearch.WordTrace tailWord_1673451 prefixEnd_1673451 859284714747237348966445 := by
  unfold tailWord_1673451
  simp only [CollatzResearch.WordTrace]
  refine ⟨61035772260380304521996207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40690514840253536347997471 61035772260380304521996207)
  ·
    refine ⟨91553658390570456782994311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61035772260380304521996207 91553658390570456782994311)
    ·
      refine ⟨137330487585855685174491467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91553658390570456782994311 137330487585855685174491467)
      ·
        refine ⟨205995731378783527761737201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137330487585855685174491467 205995731378783527761737201)
        ·
          refine ⟨154496798534087645821302901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205995731378783527761737201 154496798534087645821302901)
          ·
            refine ⟨14484074862570716795747147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154496798534087645821302901 14484074862570716795747147)
            ·
              refine ⟨21726112293856075193620721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14484074862570716795747147 21726112293856075193620721)
              ·
                refine ⟨16294584220392056395215541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21726112293856075193620721 16294584220392056395215541)
                ·
                  refine ⟨1527617270661755287051457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16294584220392056395215541 1527617270661755287051457)
                  ·
                    refine ⟨1145712952996316465288593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1527617270661755287051457 1145712952996316465288593)
                    ·
                      refine ⟨859284714747237348966445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1145712952996316465288593 859284714747237348966445)
                      ·
                        rfl

theorem cell23_1673451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 2, 2].length) (baseStart_1673451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673451 prefixEnd_1673451 := by exact prefixLift 1673451
  have htrace : WordTrace (prefixWord ++ tailWord_1673451) baseStart_1673451 baseEnd_1673451 := by
    simpa [prefixWord, tailWord_1673451, baseEnd_1673451] using wordTrace_append hprefix tailTrace_1673451
  have hstable : (prefixWord ++ tailWord_1673451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673451).length < 2 ^ (prefixWord ++ tailWord_1673451).sum := by decide
  have hdescent : baseEnd_1673451 < baseStart_1673451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673454 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_1673454 : Nat := 118140960795 + 1673454 * 2 ^ 59
def prefixEnd_1673454 : Nat := 4983230072969 + 3 ^ 40 * 1673454 * 2
def baseEnd_1673454 : Nat := 859286255189200837228931

theorem tailTrace_1673454 : CollatzResearch.WordTrace tailWord_1673454 prefixEnd_1673454 859286255189200837228931 := by
  unfold tailWord_1673454
  simp only [CollatzResearch.WordTrace]
  refine ⟨7629485209921179504294427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40690587786246290689570277 7629485209921179504294427)
  ·
    refine ⟨11444227814881769256441641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7629485209921179504294427 11444227814881769256441641)
    ·
      refine ⟨8583170861161326942331231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11444227814881769256441641 8583170861161326942331231)
      ·
        refine ⟨12874756291741990413496847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8583170861161326942331231 12874756291741990413496847)
        ·
          refine ⟨19312134437612985620245271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12874756291741990413496847 19312134437612985620245271)
          ·
            refine ⟨28968201656419478430367907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19312134437612985620245271 28968201656419478430367907)
            ·
              refine ⟨43452302484629217645551861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28968201656419478430367907 43452302484629217645551861)
              ·
                refine ⟨4073653357933989154270487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43452302484629217645551861 4073653357933989154270487)
                ·
                  refine ⟨6110480036900983731405731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4073653357933989154270487 6110480036900983731405731)
                  ·
                    refine ⟨9165720055351475597108597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6110480036900983731405731 9165720055351475597108597)
                    ·
                      refine ⟨859286255189200837228931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9165720055351475597108597 859286255189200837228931)
                      ·
                        rfl

theorem cell23_1673454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_1673454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673454 prefixEnd_1673454 := by exact prefixLift 1673454
  have htrace : WordTrace (prefixWord ++ tailWord_1673454) baseStart_1673454 baseEnd_1673454 := by
    simpa [prefixWord, tailWord_1673454, baseEnd_1673454] using wordTrace_append hprefix tailTrace_1673454
  have hstable : (prefixWord ++ tailWord_1673454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673454).length < 2 ^ (prefixWord ++ tailWord_1673454).sum := by decide
  have hdescent : baseEnd_1673454 < baseStart_1673454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673468 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 3, 2, 2]
def baseStart_1673468 : Nat := 118140960795 + 1673468 * 2 ^ 59
def prefixEnd_1673468 : Nat := 4983230072969 + 3 ^ 40 * 1673468 * 2
def baseEnd_1673468 : Nat := 859293443918363782453867

theorem tailTrace_1673468 : CollatzResearch.WordTrace tailWord_1673468 prefixEnd_1673468 859293443918363782453867 := by
  unfold tailWord_1673468
  simp only [CollatzResearch.WordTrace]
  refine ⟨30518196150659358212682529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40690928200879144283576705 30518196150659358212682529)
  ·
    refine ⟨22888647112994518659511897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30518196150659358212682529 22888647112994518659511897)
    ·
      refine ⟨17166485334745888994633923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22888647112994518659511897 17166485334745888994633923)
      ·
        refine ⟨25749728002118833491950885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17166485334745888994633923 25749728002118833491950885)
        ·
          refine ⟨4828074000397281279740791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25749728002118833491950885 4828074000397281279740791)
          ·
            refine ⟨7242111000595921919611187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4828074000397281279740791 7242111000595921919611187)
            ·
              refine ⟨10863166500893882879416781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7242111000595921919611187 10863166500893882879416781)
              ·
                refine ⟨4073687437835206079781293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10863166500893882879416781 4073687437835206079781293)
                ·
                  refine ⟨1527632789188202279917985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4073687437835206079781293 1527632789188202279917985)
                  ·
                    refine ⟨1145724591891151709938489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1527632789188202279917985 1145724591891151709938489)
                    ·
                      refine ⟨859293443918363782453867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1145724591891151709938489 859293443918363782453867)
                      ·
                        rfl

theorem cell23_1673468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_1673468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673468 prefixEnd_1673468 := by exact prefixLift 1673468
  have htrace : WordTrace (prefixWord ++ tailWord_1673468) baseStart_1673468 baseEnd_1673468 := by
    simpa [prefixWord, tailWord_1673468, baseEnd_1673468] using wordTrace_append hprefix tailTrace_1673468
  have hstable : (prefixWord ++ tailWord_1673468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673468).length < 2 ^ (prefixWord ++ tailWord_1673468).sum := by decide
  have hdescent : baseEnd_1673468 < baseStart_1673468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673477 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 1, 4, 6]
def baseStart_1673477 : Nat := 118140960795 + 1673477 * 2 ^ 59
def prefixEnd_1673477 : Nat := 4983230072969 + 3 ^ 40 * 1673477 * 2
def baseEnd_1673477 : Nat := 859298065244254247241325

theorem tailTrace_1673477 : CollatzResearch.WordTrace tailWord_1673477 prefixEnd_1673477 859298065244254247241325 := by
  unfold tailWord_1673477
  simp only [CollatzResearch.WordTrace]
  refine ⟨61036720558286110962442685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40691147038857407308295123 61036720558286110962442685)
  ·
    refine ⟨22888770209357291610916007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61036720558286110962442685 22888770209357291610916007)
    ·
      refine ⟨34333155314035937416374011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22888770209357291610916007 34333155314035937416374011)
      ·
        refine ⟨51499732971053906124561017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34333155314035937416374011 51499732971053906124561017)
        ·
          refine ⟨38624799728290429593420763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51499732971053906124561017 38624799728290429593420763)
          ·
            refine ⟨57937199592435644390131145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38624799728290429593420763 57937199592435644390131145)
            ·
              refine ⟨43452899694326733292598359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57937199592435644390131145 43452899694326733292598359)
              ·
                refine ⟨65179349541490099938897539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43452899694326733292598359 65179349541490099938897539)
                ·
                  refine ⟨97769024312235149908346309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65179349541490099938897539 97769024312235149908346309)
                  ·
                    refine ⟨18331692058544090607814933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97769024312235149908346309 18331692058544090607814933)
                    ·
                      refine ⟨859298065244254247241325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18331692058544090607814933 859298065244254247241325)
                      ·
                        rfl

theorem cell23_1673477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_1673477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673477 prefixEnd_1673477 := by exact prefixLift 1673477
  have htrace : WordTrace (prefixWord ++ tailWord_1673477) baseStart_1673477 baseEnd_1673477 := by
    simpa [prefixWord, tailWord_1673477, baseEnd_1673477] using wordTrace_append hprefix tailTrace_1673477
  have hstable : (prefixWord ++ tailWord_1673477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673477).length < 2 ^ (prefixWord ++ tailWord_1673477).sum := by decide
  have hdescent : baseEnd_1673477 < baseStart_1673477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673481 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 1, 2, 4]
def baseStart_1673481 : Nat := 118140960795 + 1673481 * 2 ^ 59
def prefixEnd_1673481 : Nat := 4983230072969 + 3 ^ 40 * 1673481 * 2
def baseEnd_1673481 : Nat := 859300119166872231591307

theorem tailTrace_1673481 : CollatzResearch.WordTrace tailWord_1673481 prefixEnd_1673481 859300119166872231591307 := by
  unfold tailWord_1673481
  simp only [CollatzResearch.WordTrace]
  refine ⟨61036866450271619645588297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40691244300181079763725531 61036866450271619645588297)
  ·
    refine ⟨45777649837703714734191223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61036866450271619645588297 45777649837703714734191223)
    ·
      refine ⟨68666474756555572101286835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45777649837703714734191223 68666474756555572101286835)
      ·
        refine ⟨102999712134833358151930253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68666474756555572101286835 102999712134833358151930253)
        ·
          refine ⟨38624892050562509306973845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102999712134833358151930253 38624892050562509306973845)
          ·
            refine ⟨1810541814870117623764399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38624892050562509306973845 1810541814870117623764399)
            ·
              refine ⟨2715812722305176435646599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810541814870117623764399 2715812722305176435646599)
              ·
                refine ⟨4073719083457764653469899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2715812722305176435646599 4073719083457764653469899)
                ·
                  refine ⟨6110578625186646980204849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4073719083457764653469899 6110578625186646980204849)
                  ·
                    refine ⟨4582933968889985235153637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6110578625186646980204849 4582933968889985235153637)
                    ·
                      refine ⟨859300119166872231591307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4582933968889985235153637 859300119166872231591307)
                      ·
                        rfl

theorem cell23_1673481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 2, 4].length) (baseStart_1673481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673481 prefixEnd_1673481 := by exact prefixLift 1673481
  have htrace : WordTrace (prefixWord ++ tailWord_1673481) baseStart_1673481 baseEnd_1673481 := by
    simpa [prefixWord, tailWord_1673481, baseEnd_1673481] using wordTrace_append hprefix tailTrace_1673481
  have hstable : (prefixWord ++ tailWord_1673481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673481).length < 2 ^ (prefixWord ++ tailWord_1673481).sum := by decide
  have hdescent : baseEnd_1673481 < baseStart_1673481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673487 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 2, 7]
def baseStart_1673487 : Nat := 118140960795 + 1673487 * 2 ^ 59
def prefixEnd_1673487 : Nat := 4983230072969 + 3 ^ 40 * 1673487 * 2
def baseEnd_1673487 : Nat := 286434400016933069372093

theorem tailTrace_1673487 : CollatzResearch.WordTrace tailWord_1673487 prefixEnd_1673487 286434400016933069372093 := by
  unfold tailWord_1673487
  simp only [CollatzResearch.WordTrace]
  refine ⟨61037085288249882670306715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40691390192166588446871143 61037085288249882670306715)
  ·
    refine ⟨91555627932374824005460073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61037085288249882670306715 91555627932374824005460073)
    ·
      refine ⟨68666720949281118004095055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91555627932374824005460073 68666720949281118004095055)
      ·
        refine ⟨103000081423921677006142583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68666720949281118004095055 103000081423921677006142583)
        ·
          refine ⟨154500122135882515509213875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103000081423921677006142583 154500122135882515509213875)
          ·
            refine ⟨231750183203823773263820813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154500122135882515509213875 231750183203823773263820813)
            ·
              refine ⟨86906318701433914973932805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231750183203823773263820813 86906318701433914973932805)
              ·
                refine ⟨16294934756518859057612401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86906318701433914973932805 16294934756518859057612401)
                ·
                  refine ⟨12221201067389144293209301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16294934756518859057612401 12221201067389144293209301)
                  ·
                    refine ⟨286434400016933069372093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12221201067389144293209301 286434400016933069372093)
                    ·
                      rfl

theorem cell23_1673487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 7].length) (baseStart_1673487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673487 prefixEnd_1673487 := by exact prefixLift 1673487
  have htrace : WordTrace (prefixWord ++ tailWord_1673487) baseStart_1673487 baseEnd_1673487 := by
    simpa [prefixWord, tailWord_1673487, baseEnd_1673487] using wordTrace_append hprefix tailTrace_1673487
  have hstable : (prefixWord ++ tailWord_1673487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673487).length < 2 ^ (prefixWord ++ tailWord_1673487).sum := by decide
  have hdescent : baseEnd_1673487 < baseStart_1673487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673544 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_1673544 : Nat := 118140960795 + 1673544 * 2 ^ 59
def prefixEnd_1673544 : Nat := 4983230072969 + 3 ^ 40 * 1673544 * 2
def baseEnd_1673544 : Nat := 859332468448105485103517

theorem tailTrace_1673544 : CollatzResearch.WordTrace tailWord_1673544 prefixEnd_1673544 859332468448105485103517 := by
  unfold tailWord_1673544
  simp only [CollatzResearch.WordTrace]
  refine ⟨30519582124521690702565843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40692776166028920936754457 30519582124521690702565843)
  ·
    refine ⟨45779373186782536053848765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30519582124521690702565843 45779373186782536053848765)
    ·
      refine ⟨17167264945043451020193287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45779373186782536053848765 17167264945043451020193287)
      ·
        refine ⟨25750897417565176530289931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17167264945043451020193287 25750897417565176530289931)
        ·
          refine ⟨38626346126347764795434897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25750897417565176530289931 38626346126347764795434897)
          ·
            refine ⟨28969759594760823596576173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38626346126347764795434897 28969759594760823596576173)
            ·
              refine ⟨10863659848035308848716065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28969759594760823596576173 10863659848035308848716065)
              ·
                refine ⟨8147744886026481636537049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10863659848035308848716065 8147744886026481636537049)
                ·
                  refine ⟨6110808664519861227402787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8147744886026481636537049 6110808664519861227402787)
                  ·
                    refine ⟨9166212996779791841104181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6110808664519861227402787 9166212996779791841104181)
                    ·
                      refine ⟨859332468448105485103517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9166212996779791841104181 859332468448105485103517)
                      ·
                        rfl

theorem cell23_1673544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_1673544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673544 prefixEnd_1673544 := by exact prefixLift 1673544
  have htrace : WordTrace (prefixWord ++ tailWord_1673544) baseStart_1673544 baseEnd_1673544 := by
    simpa [prefixWord, tailWord_1673544, baseEnd_1673544] using wordTrace_append hprefix tailTrace_1673544
  have hstable : (prefixWord ++ tailWord_1673544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673544).length < 2 ^ (prefixWord ++ tailWord_1673544).sum := by decide
  have hdescent : baseEnd_1673544 < baseStart_1673544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673575 : List Nat := [1, 1, 5, 1, 3, 1, 1, 4, 2, 2, 2]
def baseStart_1673575 : Nat := 118140960795 + 1673575 * 2 ^ 59
def prefixEnd_1673575 : Nat := 4983230072969 + 3 ^ 40 * 1673575 * 2
def baseEnd_1673575 : Nat := 859348386348394863815875

theorem tailTrace_1673575 : CollatzResearch.WordTrace tailWord_1673575 prefixEnd_1673575 859348386348394863815875 := by
  unfold tailWord_1673575
  simp only [CollatzResearch.WordTrace]
  refine ⟨61040294911931073699510179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40693529941287382466340119 61040294911931073699510179)
  ·
    refine ⟨91560442367896610549265269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61040294911931073699510179 91560442367896610549265269)
    ·
      refine ⟨8583791471990307238993619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91560442367896610549265269 8583791471990307238993619)
      ·
        refine ⟨12875687207985460858490429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8583791471990307238993619 12875687207985460858490429)
        ·
          refine ⟨4828382702994547821933911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12875687207985460858490429 4828382702994547821933911)
          ·
            refine ⟨7242574054491821732900867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4828382702994547821933911 7242574054491821732900867)
            ·
              refine ⟨10863861081737732599351301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7242574054491821732900867 10863861081737732599351301)
              ·
                refine ⟨2036973952825824862378369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10863861081737732599351301 2036973952825824862378369)
                ·
                  refine ⟨1527730464619368646783777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2036973952825824862378369 1527730464619368646783777)
                  ·
                    refine ⟨1145797848464526485087833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1527730464619368646783777 1145797848464526485087833)
                    ·
                      refine ⟨859348386348394863815875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1145797848464526485087833 859348386348394863815875)
                      ·
                        rfl

theorem cell23_1673575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_1673575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673575 prefixEnd_1673575 := by exact prefixLift 1673575
  have htrace : WordTrace (prefixWord ++ tailWord_1673575) baseStart_1673575 baseEnd_1673575 := by
    simpa [prefixWord, tailWord_1673575, baseEnd_1673575] using wordTrace_append hprefix tailTrace_1673575
  have hstable : (prefixWord ++ tailWord_1673575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673575).length < 2 ^ (prefixWord ++ tailWord_1673575).sum := by decide
  have hdescent : baseEnd_1673575 < baseStart_1673575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673611 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 2, 5]
def baseStart_1673611 : Nat := 118140960795 + 1673611 * 2 ^ 59
def prefixEnd_1673611 : Nat := 4983230072969 + 3 ^ 40 * 1673611 * 2
def baseEnd_1673611 : Nat := 286455623883985574321903

theorem tailTrace_1673611 : CollatzResearch.WordTrace tailWord_1673611 prefixEnd_1673611 286455623883985574321903 := by
  unfold tailWord_1673611
  simp only [CollatzResearch.WordTrace]
  refine ⟨61041607939800651847820687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40694405293200434565213791 61041607939800651847820687)
  ·
    refine ⟨91562411909700977771731031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61041607939800651847820687 91562411909700977771731031)
    ·
      refine ⟨137343617864551466657596547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91562411909700977771731031 137343617864551466657596547)
      ·
        refine ⟨206015426796827199986394821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137343617864551466657596547 206015426796827199986394821)
        ·
          refine ⟨38627892524405099997449029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206015426796827199986394821 38627892524405099997449029)
          ·
            refine ⟨7242729848325956249521693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38627892524405099997449029 7242729848325956249521693)
            ·
              refine ⟨2716023693122233593570635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7242729848325956249521693 2716023693122233593570635)
              ·
                refine ⟨4074035539683350390355953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2716023693122233593570635 4074035539683350390355953)
                ·
                  refine ⟨3055526654762512792766965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4074035539683350390355953 3055526654762512792766965)
                  ·
                    refine ⟨286455623883985574321903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3055526654762512792766965 286455623883985574321903)
                    ·
                      rfl

theorem cell23_1673611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 5].length) (baseStart_1673611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673611 prefixEnd_1673611 := by exact prefixLift 1673611
  have htrace : WordTrace (prefixWord ++ tailWord_1673611) baseStart_1673611 baseEnd_1673611 := by
    simpa [prefixWord, tailWord_1673611, baseEnd_1673611] using wordTrace_append hprefix tailTrace_1673611
  have hstable : (prefixWord ++ tailWord_1673611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673611).length < 2 ^ (prefixWord ++ tailWord_1673611).sum := by decide
  have hdescent : baseEnd_1673611 < baseStart_1673611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673631 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 4]
def baseStart_1673631 : Nat := 118140960795 + 1673631 * 2 ^ 59
def prefixEnd_1673631 : Nat := 4983230072969 + 3 ^ 40 * 1673631 * 2
def baseEnd_1673631 : Nat := 859377141265046644715617

theorem tailTrace_1673631 : CollatzResearch.WordTrace tailWord_1673631 prefixEnd_1673631 859377141265046644715617 := by
  unfold tailWord_1673631
  simp only [CollatzResearch.WordTrace]
  refine ⟨61042337399728195263548747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40694891599818796842365831 61042337399728195263548747)
  ·
    refine ⟨91563506099592292895323121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61042337399728195263548747 91563506099592292895323121)
    ·
      refine ⟨68672629574694219671492341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91563506099592292895323121 68672629574694219671492341)
      ·
        refine ⟨6438059022627583094202407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68672629574694219671492341 6438059022627583094202407)
        ·
          refine ⟨9657088533941374641303611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6438059022627583094202407 9657088533941374641303611)
          ·
            refine ⟨14485632800912061961955417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9657088533941374641303611 14485632800912061961955417)
            ·
              refine ⟨10864224600684046471466563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14485632800912061961955417 10864224600684046471466563)
              ·
                refine ⟨16296336901026069707199845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10864224600684046471466563 16296336901026069707199845)
                ·
                  refine ⟨3055563168942388070099971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16296336901026069707199845 3055563168942388070099971)
                  ·
                    refine ⟨4583344753413582105149957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3055563168942388070099971 4583344753413582105149957)
                    ·
                      refine ⟨859377141265046644715617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4583344753413582105149957 859377141265046644715617)
                      ·
                        rfl

theorem cell23_1673631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_1673631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673631 prefixEnd_1673631 := by exact prefixLift 1673631
  have htrace : WordTrace (prefixWord ++ tailWord_1673631) baseStart_1673631 baseEnd_1673631 := by
    simpa [prefixWord, tailWord_1673631, baseEnd_1673631] using wordTrace_append hprefix tailTrace_1673631
  have hstable : (prefixWord ++ tailWord_1673631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673631).length < 2 ^ (prefixWord ++ tailWord_1673631).sum := by decide
  have hdescent : baseEnd_1673631 < baseStart_1673631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673644 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 6]
def baseStart_1673644 : Nat := 118140960795 + 1673644 * 2 ^ 59
def prefixEnd_1673644 : Nat := 4983230072969 + 3 ^ 40 * 1673644 * 2
def baseEnd_1673644 : Nat := 859383816513555093853057

theorem tailTrace_1673644 : CollatzResearch.WordTrace tailWord_1673644 prefixEnd_1673644 859383816513555093853057 := by
  unfold tailWord_1673644
  simp only [CollatzResearch.WordTrace]
  refine ⟨30521405774340549241885993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40695207699120732322514657 30521405774340549241885993)
  ·
    refine ⟨22891054330755411931414495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30521405774340549241885993 22891054330755411931414495)
    ·
      refine ⟨34336581496133117897121743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22891054330755411931414495 34336581496133117897121743)
      ·
        refine ⟨51504872244199676845682615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34336581496133117897121743 51504872244199676845682615)
        ·
          refine ⟨77257308366299515268523923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51504872244199676845682615 77257308366299515268523923)
          ·
            refine ⟨115885962549449272902785885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77257308366299515268523923 115885962549449272902785885)
            ·
              refine ⟨43457235956043477338544707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115885962549449272902785885 43457235956043477338544707)
              ·
                refine ⟨65185853934065216007817061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43457235956043477338544707 65185853934065216007817061)
                ·
                  refine ⟨12222347612637228001465699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65185853934065216007817061 12222347612637228001465699)
                  ·
                    refine ⟨18333521418955842002198549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12222347612637228001465699 18333521418955842002198549)
                    ·
                      refine ⟨859383816513555093853057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18333521418955842002198549 859383816513555093853057)
                      ·
                        rfl

theorem cell23_1673644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_1673644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673644 prefixEnd_1673644 := by exact prefixLift 1673644
  have htrace : WordTrace (prefixWord ++ tailWord_1673644) baseStart_1673644 baseEnd_1673644 := by
    simpa [prefixWord, tailWord_1673644, baseEnd_1673644] using wordTrace_append hprefix tailTrace_1673644
  have hstable : (prefixWord ++ tailWord_1673644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673644).length < 2 ^ (prefixWord ++ tailWord_1673644).sum := by decide
  have hdescent : baseEnd_1673644 < baseStart_1673644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673708 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 4, 3, 2]
def baseStart_1673708 : Nat := 118140960795 + 1673708 * 2 ^ 59
def prefixEnd_1673708 : Nat := 4983230072969 + 3 ^ 40 * 1673708 * 2
def baseEnd_1673708 : Nat := 859416679275442843452763

theorem tailTrace_1673708 : CollatzResearch.WordTrace tailWord_1673708 prefixEnd_1673708 859416679275442843452763 := by
  unfold tailWord_1673708
  simp only [CollatzResearch.WordTrace]
  refine ⟨30522572910224618707050889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40696763880299491609401185 30522572910224618707050889)
  ·
    refine ⟨22891929682668464030288167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30522572910224618707050889 22891929682668464030288167)
    ·
      refine ⟨34337894524002696045432251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22891929682668464030288167 34337894524002696045432251)
      ·
        refine ⟨51506841786004044068148377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34337894524002696045432251 51506841786004044068148377)
        ·
          refine ⟨38630131339503033051111283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51506841786004044068148377 38630131339503033051111283)
          ·
            refine ⟨57945197009254549576666925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38630131339503033051111283 57945197009254549576666925)
            ·
              refine ⟨21729448878470456091250097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57945197009254549576666925 21729448878470456091250097)
              ·
                refine ⟨16297086658852842068437573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21729448878470456091250097 16297086658852842068437573)
                ·
                  refine ⟨3055703748534907887832045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16297086658852842068437573 3055703748534907887832045)
                  ·
                    refine ⟨1145888905700590457937017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3055703748534907887832045 1145888905700590457937017)
                    ·
                      refine ⟨859416679275442843452763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1145888905700590457937017 859416679275442843452763)
                      ·
                        rfl

theorem cell23_1673708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 3, 2].length) (baseStart_1673708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673708 prefixEnd_1673708 := by exact prefixLift 1673708
  have htrace : WordTrace (prefixWord ++ tailWord_1673708) baseStart_1673708 baseEnd_1673708 := by
    simpa [prefixWord, tailWord_1673708, baseEnd_1673708] using wordTrace_append hprefix tailTrace_1673708
  have hstable : (prefixWord ++ tailWord_1673708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673708).length < 2 ^ (prefixWord ++ tailWord_1673708).sum := by decide
  have hdescent : baseEnd_1673708 < baseStart_1673708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673718 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_1673718 : Nat := 118140960795 + 1673718 * 2 ^ 59
def prefixEnd_1673718 : Nat := 4983230072969 + 3 ^ 40 * 1673718 * 2
def baseEnd_1673718 : Nat := 286473938027329268109239

theorem tailTrace_1673718 : CollatzResearch.WordTrace tailWord_1673718 prefixEnd_1673718 286473938027329268109239 := by
  unfold tailWord_1673718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3815344409400813070122863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40697007033608672747977205 3815344409400813070122863)
  ·
    refine ⟨5723016614101219605184295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3815344409400813070122863 5723016614101219605184295)
    ·
      refine ⟨8584524921151829407776443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5723016614101219605184295 8584524921151829407776443)
      ·
        refine ⟨12876787381727744111664665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8584524921151829407776443 12876787381727744111664665)
        ·
          refine ⟨9657590536295808083748499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12876787381727744111664665 9657590536295808083748499)
          ·
            refine ⟨14486385804443712125622749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9657590536295808083748499 14486385804443712125622749)
            ·
              refine ⟨5432394676666392047108531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14486385804443712125622749 5432394676666392047108531)
              ·
                refine ⟨8148592014999588070662797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5432394676666392047108531 8148592014999588070662797)
                ·
                  refine ⟨3055722005624845526498549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8148592014999588070662797 3055722005624845526498549)
                  ·
                    refine ⟨286473938027329268109239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3055722005624845526498549 286473938027329268109239)
                    ·
                      rfl

theorem cell23_1673718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_1673718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673718 prefixEnd_1673718 := by exact prefixLift 1673718
  have htrace : WordTrace (prefixWord ++ tailWord_1673718) baseStart_1673718 baseEnd_1673718 := by
    simpa [prefixWord, tailWord_1673718, baseEnd_1673718] using wordTrace_append hprefix tailTrace_1673718
  have hstable : (prefixWord ++ tailWord_1673718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673718).length < 2 ^ (prefixWord ++ tailWord_1673718).sum := by decide
  have hdescent : baseEnd_1673718 < baseStart_1673718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673725 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 2, 3, 2]
def baseStart_1673725 : Nat := 118140960795 + 1673725 * 2 ^ 59
def prefixEnd_1673725 : Nat := 4983230072969 + 3 ^ 40 * 1673725 * 2
def baseEnd_1673725 : Nat := 859425408446569276940185

theorem tailTrace_1673725 : CollatzResearch.WordTrace tailWord_1673725 prefixEnd_1673725 859425408446569276940185 := by
  unfold tailWord_1673725
  simp only [CollatzResearch.WordTrace]
  refine ⟨61045765861387649317470629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40697177240925099544980419 61045765861387649317470629)
  ·
    refine ⟨11446081099010184247025743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61045765861387649317470629 11446081099010184247025743)
    ·
      refine ⟨17169121648515276370538615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11446081099010184247025743 17169121648515276370538615)
      ·
        refine ⟨25753682472772914555807923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17169121648515276370538615 25753682472772914555807923)
        ·
          refine ⟨38630523709159371833711885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25753682472772914555807923 38630523709159371833711885)
          ·
            refine ⟨14486446390934764437641957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38630523709159371833711885 14486446390934764437641957)
            ·
              refine ⟨2716208698300268332057867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14486446390934764437641957 2716208698300268332057867)
              ·
                refine ⟨4074313047450402498086801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2716208698300268332057867 4074313047450402498086801)
                ·
                  refine ⟨3055734785587801873565101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4074313047450402498086801 3055734785587801873565101)
                  ·
                    refine ⟨1145900544595425702586913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3055734785587801873565101 1145900544595425702586913)
                    ·
                      refine ⟨859425408446569276940185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1145900544595425702586913 859425408446569276940185)
                      ·
                        rfl

theorem cell23_1673725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_1673725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673725 prefixEnd_1673725 := by exact prefixLift 1673725
  have htrace : WordTrace (prefixWord ++ tailWord_1673725) baseStart_1673725 baseEnd_1673725 := by
    simpa [prefixWord, tailWord_1673725, baseEnd_1673725] using wordTrace_append hprefix tailTrace_1673725
  have hstable : (prefixWord ++ tailWord_1673725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673725).length < 2 ^ (prefixWord ++ tailWord_1673725).sum := by decide
  have hdescent : baseEnd_1673725 < baseStart_1673725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673731 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 1, 6]
def baseStart_1673731 : Nat := 118140960795 + 1673731 * 2 ^ 59
def prefixEnd_1673731 : Nat := 4983230072969 + 3 ^ 40 * 1673731 * 2
def baseEnd_1673731 : Nat := 286476163110165417821719

theorem tailTrace_1673731 : CollatzResearch.WordTrace tailWord_1673731 prefixEnd_1673731 286476163110165417821719 := by
  unfold tailWord_1673731
  simp only [CollatzResearch.WordTrace]
  refine ⟨61045984699365912342189047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40697323132910608228126031 61045984699365912342189047)
  ·
    refine ⟨91568977049048868513283571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61045984699365912342189047 91568977049048868513283571)
    ·
      refine ⟨137353465573573302769925357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91568977049048868513283571 137353465573573302769925357)
      ·
        refine ⟨51507549590089988538722009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137353465573573302769925357 51507549590089988538722009)
        ·
          refine ⟨38630662192567491404041507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51507549590089988538722009 38630662192567491404041507)
          ·
            refine ⟨57945993288851237106062261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38630662192567491404041507 57945993288851237106062261)
            ·
              refine ⟨5432436870829803478693337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57945993288851237106062261 5432436870829803478693337)
              ·
                refine ⟨4074327653122352609020003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5432436870829803478693337 4074327653122352609020003)
                ·
                  refine ⟨6111491479683528913530005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4074327653122352609020003 6111491479683528913530005)
                  ·
                    refine ⟨286476163110165417821719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6111491479683528913530005 286476163110165417821719)
                    ·
                      rfl

theorem cell23_1673731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 6].length) (baseStart_1673731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673731 prefixEnd_1673731 := by exact prefixLift 1673731
  have htrace : WordTrace (prefixWord ++ tailWord_1673731) baseStart_1673731 baseEnd_1673731 := by
    simpa [prefixWord, tailWord_1673731, baseEnd_1673731] using wordTrace_append hprefix tailTrace_1673731
  have hstable : (prefixWord ++ tailWord_1673731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673731).length < 2 ^ (prefixWord ++ tailWord_1673731).sum := by decide
  have hdescent : baseEnd_1673731 < baseStart_1673731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673789 : List Nat := [1, 4, 1, 3, 2, 1, 1, 5, 1, 2, 2]
def baseStart_1673789 : Nat := 118140960795 + 1673789 * 2 ^ 59
def prefixEnd_1673789 : Nat := 4983230072969 + 3 ^ 40 * 1673789 * 2
def baseEnd_1673789 : Nat := 859458271208457026539891

theorem tailTrace_1673789 : CollatzResearch.WordTrace tailWord_1673789 prefixEnd_1673789 859458271208457026539891 := by
  unfold tailWord_1673789
  simp only [CollatzResearch.WordTrace]
  refine ⟨61048100133155788247800421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40698733422103858831866947 61048100133155788247800421)
  ·
    refine ⟨11446518774966710296462579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61048100133155788247800421 11446518774966710296462579)
    ·
      refine ⟨17169778162450065444693869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11446518774966710296462579 17169778162450065444693869)
      ·
        refine ⟨6438666810918774541760201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17169778162450065444693869 6438666810918774541760201)
        ·
          refine ⟨4829000108189080906320151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6438666810918774541760201 4829000108189080906320151)
          ·
            refine ⟨7243500162283621359480227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4829000108189080906320151 7243500162283621359480227)
            ·
              refine ⟨10865250243425432039220341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7243500162283621359480227 10865250243425432039220341)
              ·
                refine ⟨1018617210321134253676907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10865250243425432039220341 1018617210321134253676907)
                ·
                  refine ⟨1527925815481701380515361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1018617210321134253676907 1527925815481701380515361)
                  ·
                    refine ⟨1145944361611276035386521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1527925815481701380515361 1145944361611276035386521)
                    ·
                      refine ⟨859458271208457026539891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1145944361611276035386521 859458271208457026539891)
                      ·
                        rfl

theorem cell23_1673789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_1673789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673789 prefixEnd_1673789 := by exact prefixLift 1673789
  have htrace : WordTrace (prefixWord ++ tailWord_1673789) baseStart_1673789 baseEnd_1673789 := by
    simpa [prefixWord, tailWord_1673789, baseEnd_1673789] using wordTrace_append hprefix tailTrace_1673789
  have hstable : (prefixWord ++ tailWord_1673789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673789).length < 2 ^ (prefixWord ++ tailWord_1673789).sum := by decide
  have hdescent : baseEnd_1673789 < baseStart_1673789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673945 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 3, 4]
def baseStart_1673945 : Nat := 118140960795 + 1673945 * 2 ^ 59
def prefixEnd_1673945 : Nat := 4983230072969 + 3 ^ 40 * 1673945 * 2
def baseEnd_1673945 : Nat := 286512791396852805396391

theorem tailTrace_1673945 : CollatzResearch.WordTrace tailWord_1673945 prefixEnd_1673945 286512791396852805396391 := by
  unfold tailWord_1673945
  simp only [CollatzResearch.WordTrace]
  refine ⟨61053789920590626890479289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40702526613727084593652859 61053789920590626890479289)
  ·
    refine ⟨45790342440442970167859467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61053789920590626890479289 45790342440442970167859467)
    ·
      refine ⟨68685513660664455251789201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45790342440442970167859467 68685513660664455251789201)
      ·
        refine ⟨51514135245498341438841901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68685513660664455251789201 51514135245498341438841901)
        ·
          refine ⟨19317800717061878039565713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51514135245498341438841901 19317800717061878039565713)
          ·
            refine ⟨14488350537796408529674285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19317800717061878039565713 14488350537796408529674285)
            ·
              refine ⟨5433131451673653198627857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14488350537796408529674285 5433131451673653198627857)
              ·
                refine ⟨4074848588755239898970893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5433131451673653198627857 4074848588755239898970893)
                ·
                  refine ⟨1528068220783214962114085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4074848588755239898970893 1528068220783214962114085)
                  ·
                    refine ⟨286512791396852805396391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1528068220783214962114085 286512791396852805396391)
                    ·
                      rfl

theorem cell23_1673945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 4].length) (baseStart_1673945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673945 prefixEnd_1673945 := by exact prefixLift 1673945
  have htrace : WordTrace (prefixWord ++ tailWord_1673945) baseStart_1673945 baseEnd_1673945 := by
    simpa [prefixWord, tailWord_1673945, baseEnd_1673945] using wordTrace_append hprefix tailTrace_1673945
  have hstable : (prefixWord ++ tailWord_1673945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673945).length < 2 ^ (prefixWord ++ tailWord_1673945).sum := by decide
  have hdescent : baseEnd_1673945 < baseStart_1673945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673978 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6]
def baseStart_1673978 : Nat := 118140960795 + 1673978 * 2 ^ 59
def prefixEnd_1673978 : Nat := 4983230072969 + 3 ^ 40 * 1673978 * 2
def baseEnd_1673978 : Nat := 859555319052156787076521

theorem tailTrace_1673978 : CollatzResearch.WordTrace tailWord_1673978 prefixEnd_1673978 859555319052156787076521 := by
  unfold tailWord_1673978
  simp only [CollatzResearch.WordTrace]
  refine ⟨15263748382367768381607647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40703329019647382350953725 15263748382367768381607647)
  ·
    refine ⟨22895622573551652572411471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15263748382367768381607647 22895622573551652572411471)
    ·
      refine ⟨34343433860327478858617207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22895622573551652572411471 34343433860327478858617207)
      ·
        refine ⟨51515150790491218287925811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34343433860327478858617207 51515150790491218287925811)
        ·
          refine ⟨77272726185736827431888717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51515150790491218287925811 77272726185736827431888717)
          ·
            refine ⟨28977272319651310286958269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77272726185736827431888717 28977272319651310286958269)
            ·
              refine ⟨10866477119869241357609351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28977272319651310286958269 10866477119869241357609351)
              ·
                refine ⟨16299715679803862036414027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10866477119869241357609351 16299715679803862036414027)
                ·
                  refine ⟨24449573519705793054621041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16299715679803862036414027 24449573519705793054621041)
                  ·
                    refine ⟨18337180139779344790965781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24449573519705793054621041 18337180139779344790965781)
                    ·
                      refine ⟨859555319052156787076521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18337180139779344790965781 859555319052156787076521)
                      ·
                        rfl

theorem cell23_1673978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_1673978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673978 prefixEnd_1673978 := by exact prefixLift 1673978
  have htrace : WordTrace (prefixWord ++ tailWord_1673978) baseStart_1673978 baseEnd_1673978 := by
    simpa [prefixWord, tailWord_1673978, baseEnd_1673978] using wordTrace_append hprefix tailTrace_1673978
  have hstable : (prefixWord ++ tailWord_1673978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673978).length < 2 ^ (prefixWord ++ tailWord_1673978).sum := by decide
  have hdescent : baseEnd_1673978 < baseStart_1673978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673992 : List Nat := [2, 1, 3, 2, 2, 3, 3, 1, 6]
def baseStart_1673992 : Nat := 118140960795 + 1673992 * 2 ^ 59
def prefixEnd_1673992 : Nat := 4983230072969 + 3 ^ 40 * 1673992 * 2
def baseEnd_1673992 : Nat := 95506945309035525811273

theorem tailTrace_1673992 : CollatzResearch.WordTrace tailWord_1673992 prefixEnd_1673992 95506945309035525811273 := by
  unfold tailWord_1673992
  simp only [CollatzResearch.WordTrace]
  refine ⟨30527752075710176958720115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40703669434280235944960153 30527752075710176958720115)
  ·
    refine ⟨45791628113565265438080173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30527752075710176958720115 45791628113565265438080173)
    ·
      refine ⟨17171860542586974539280065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45791628113565265438080173 17171860542586974539280065)
      ·
        refine ⟨12878895406940230904460049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17171860542586974539280065 12878895406940230904460049)
        ·
          refine ⟨9659171555205173178345037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12878895406940230904460049 9659171555205173178345037)
          ·
            refine ⟨3622189333201939941879389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9659171555205173178345037 3622189333201939941879389)
            ·
              refine ⟨1358320999950727478204771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3622189333201939941879389 1358320999950727478204771)
              ·
                refine ⟨2037481499926091217307157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358320999950727478204771 2037481499926091217307157)
                ·
                  refine ⟨95506945309035525811273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2037481499926091217307157 95506945309035525811273)
                  ·
                    rfl

theorem cell23_1673992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 6].length) (baseStart_1673992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1673992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1673992 prefixEnd_1673992 := by exact prefixLift 1673992
  have htrace : WordTrace (prefixWord ++ tailWord_1673992) baseStart_1673992 baseEnd_1673992 := by
    simpa [prefixWord, tailWord_1673992, baseEnd_1673992] using wordTrace_append hprefix tailTrace_1673992
  have hstable : (prefixWord ++ tailWord_1673992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673992).length < 2 ^ (prefixWord ++ tailWord_1673992).sum := by decide
  have hdescent : baseEnd_1673992 < baseStart_1673992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674012 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 1, 5, 2]
def baseStart_1674012 : Nat := 118140960795 + 1674012 * 2 ^ 59
def prefixEnd_1674012 : Nat := 4983230072969 + 3 ^ 40 * 1674012 * 2
def baseEnd_1674012 : Nat := 859572777394409654051365

theorem tailTrace_1674012 : CollatzResearch.WordTrace tailWord_1674012 prefixEnd_1674012 859572777394409654051365 := by
  unfold tailWord_1674012
  simp only [CollatzResearch.WordTrace]
  refine ⟨30528116805673948666584145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40704155740898598222112193 30528116805673948666584145)
  ·
    refine ⟨22896087604255461499938109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30528116805673948666584145 22896087604255461499938109)
    ·
      refine ⟨8586032851595798062476791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22896087604255461499938109 8586032851595798062476791)
      ·
        refine ⟨12879049277393697093715187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8586032851595798062476791 12879049277393697093715187)
        ·
          refine ⟨19318573916090545640572781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12879049277393697093715187 19318573916090545640572781)
          ·
            refine ⟨7244465218533954615214793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19318573916090545640572781 7244465218533954615214793)
            ·
              refine ⟨5433348913900465961411095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7244465218533954615214793 5433348913900465961411095)
              ·
                refine ⟨8150023370850698942116643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5433348913900465961411095 8150023370850698942116643)
                ·
                  refine ⟨12225035056276048413174965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8150023370850698942116643 12225035056276048413174965)
                  ·
                    refine ⟨1146097036525879538735153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12225035056276048413174965 1146097036525879538735153)
                    ·
                      refine ⟨859572777394409654051365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1146097036525879538735153 859572777394409654051365)
                      ·
                        rfl

theorem cell23_1674012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_1674012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674012 prefixEnd_1674012 := by exact prefixLift 1674012
  have htrace : WordTrace (prefixWord ++ tailWord_1674012) baseStart_1674012 baseEnd_1674012 := by
    simpa [prefixWord, tailWord_1674012, baseEnd_1674012] using wordTrace_append hprefix tailTrace_1674012
  have hstable : (prefixWord ++ tailWord_1674012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674012).length < 2 ^ (prefixWord ++ tailWord_1674012).sum := by decide
  have hdescent : baseEnd_1674012 < baseStart_1674012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674013 : List Nat := [1, 4, 2, 4, 1, 2, 1, 3, 1, 4]
def baseStart_1674013 : Nat := 118140960795 + 1674013 * 2 ^ 59
def prefixEnd_1674013 : Nat := 4983230072969 + 3 ^ 40 * 1674013 * 2
def baseEnd_1674013 : Nat := 286524430291688050046287

theorem tailTrace_1674013 : CollatzResearch.WordTrace tailWord_1674013 prefixEnd_1674013 286524430291688050046287 := by
  unfold tailWord_1674013
  simp only [CollatzResearch.WordTrace]
  refine ⟨61056270084344274503954693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40704180056229516335969795 61056270084344274503954693)
  ·
    refine ⟨11448050640814551469491505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61056270084344274503954693 11448050640814551469491505)
    ·
      refine ⟨8586037980610913602118629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11448050640814551469491505 8586037980610913602118629)
      ·
        refine ⟨1609882121364546300397243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8586037980610913602118629 1609882121364546300397243)
        ·
          refine ⟨2414823182046819450595865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1609882121364546300397243 2414823182046819450595865)
          ·
            refine ⟨1811117386535114587946899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2414823182046819450595865 1811117386535114587946899)
            ·
              refine ⟨2716676079802671881920349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811117386535114587946899 2716676079802671881920349)
              ·
                refine ⟨1018753529926001955720131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2716676079802671881920349 1018753529926001955720131)
                ·
                  refine ⟨1528130294889002933580197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1018753529926001955720131 1528130294889002933580197)
                  ·
                    refine ⟨286524430291688050046287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1528130294889002933580197 286524430291688050046287)
                    ·
                      rfl

theorem cell23_1674013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_1674013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674013 prefixEnd_1674013 := by exact prefixLift 1674013
  have htrace : WordTrace (prefixWord ++ tailWord_1674013) baseStart_1674013 baseEnd_1674013 := by
    simpa [prefixWord, tailWord_1674013, baseEnd_1674013] using wordTrace_append hprefix tailTrace_1674013
  have hstable : (prefixWord ++ tailWord_1674013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674013).length < 2 ^ (prefixWord ++ tailWord_1674013).sum := by decide
  have hdescent : baseEnd_1674013 < baseStart_1674013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674025 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 1, 8, 2]
def baseStart_1674025 : Nat := 118140960795 + 1674025 * 2 ^ 59
def prefixEnd_1674025 : Nat := 4983230072969 + 3 ^ 40 * 1674025 * 2
def baseEnd_1674025 : Nat := 859579452642918103188805

theorem tailTrace_1674025 : CollatzResearch.WordTrace tailWord_1674025 prefixEnd_1674025 859579452642918103188805 := by
  unfold tailWord_1674025
  simp only [CollatzResearch.WordTrace]
  refine ⟨61056707760300800553391529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40704471840200533702261019 61056707760300800553391529)
  ·
    refine ⟨45792530820225600415043647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61056707760300800553391529 45792530820225600415043647)
    ·
      refine ⟨68688796230338400622565471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45792530820225600415043647 68688796230338400622565471)
      ·
        refine ⟨103033194345507600933848207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68688796230338400622565471 103033194345507600933848207)
        ·
          refine ⟨154549791518261401400772311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103033194345507600933848207 154549791518261401400772311)
          ·
            refine ⟨231824687277392102101158467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154549791518261401400772311 231824687277392102101158467)
            ·
              refine ⟨347737030916088153151737701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231824687277392102101158467 347737030916088153151737701)
              ·
                refine ⟨65200693296766528715950819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347737030916088153151737701 65200693296766528715950819)
                ·
                  refine ⟨97801039945149793073926229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65200693296766528715950819 97801039945149793073926229)
                  ·
                    refine ⟨1146105936857224137585073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97801039945149793073926229 1146105936857224137585073)
                    ·
                      refine ⟨859579452642918103188805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1146105936857224137585073 859579452642918103188805)
                      ·
                        rfl

theorem cell23_1674025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 8, 2].length) (baseStart_1674025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674025 prefixEnd_1674025 := by exact prefixLift 1674025
  have htrace : WordTrace (prefixWord ++ tailWord_1674025) baseStart_1674025 baseEnd_1674025 := by
    simpa [prefixWord, tailWord_1674025, baseEnd_1674025] using wordTrace_append hprefix tailTrace_1674025
  have hstable : (prefixWord ++ tailWord_1674025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674025).length < 2 ^ (prefixWord ++ tailWord_1674025).sum := by decide
  have hdescent : baseEnd_1674025 < baseStart_1674025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674055 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_1674055 : Nat := 118140960795 + 1674055 * 2 ^ 59
def prefixEnd_1674055 : Nat := 4983230072969 + 3 ^ 40 * 1674055 * 2
def baseEnd_1674055 : Nat := 859594857062552985813667

theorem tailTrace_1674055 : CollatzResearch.WordTrace tailWord_1674055 prefixEnd_1674055 859594857062552985813667 := by
  unfold tailWord_1674055
  simp only [CollatzResearch.WordTrace]
  refine ⟨61057801950192115676983619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40705201300128077117989079 61057801950192115676983619)
  ·
    refine ⟨91586702925288173515475429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61057801950192115676983619 91586702925288173515475429)
    ·
      refine ⟨17172506798491532534151643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91586702925288173515475429 17172506798491532534151643)
      ·
        refine ⟨25758760197737298801227465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17172506798491532534151643 25758760197737298801227465)
        ·
          refine ⟨19319070148302974100920599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25758760197737298801227465 19319070148302974100920599)
          ·
            refine ⟨28978605222454461151380899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19319070148302974100920599 28978605222454461151380899)
            ·
              refine ⟨43467907833681691727071349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28978605222454461151380899 43467907833681691727071349)
              ·
                refine ⟨4075116359407658599412939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43467907833681691727071349 4075116359407658599412939)
                ·
                  refine ⟨6112674539111487899119409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4075116359407658599412939 6112674539111487899119409)
                  ·
                    refine ⟨4584505904333615924339557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6112674539111487899119409 4584505904333615924339557)
                    ·
                      refine ⟨859594857062552985813667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4584505904333615924339557 859594857062552985813667)
                      ·
                        rfl

theorem cell23_1674055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_1674055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674055 prefixEnd_1674055 := by exact prefixLift 1674055
  have htrace : WordTrace (prefixWord ++ tailWord_1674055) baseStart_1674055 baseEnd_1674055 := by
    simpa [prefixWord, tailWord_1674055, baseEnd_1674055] using wordTrace_append hprefix tailTrace_1674055
  have hstable : (prefixWord ++ tailWord_1674055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674055).length < 2 ^ (prefixWord ++ tailWord_1674055).sum := by decide
  have hdescent : baseEnd_1674055 < baseStart_1674055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674076 : List Nat := [2, 2, 4, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_1674076 : Nat := 118140960795 + 1674076 * 2 ^ 59
def prefixEnd_1674076 : Nat := 4983230072969 + 3 ^ 40 * 1674076 * 2
def baseEnd_1674076 : Nat := 859605640156297403651071

theorem tailTrace_1674076 : CollatzResearch.WordTrace tailWord_1674076 prefixEnd_1674076 859605640156297403651071 := by
  unfold tailWord_1674076
  simp only [CollatzResearch.WordTrace]
  refine ⟨30529283941558018131749041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40705711922077357508998721 30529283941558018131749041)
  ·
    refine ⟨22896962956168513598811781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30529283941558018131749041 22896962956168513598811781)
    ·
      refine ⟨4293180554281596299777209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22896962956168513598811781 4293180554281596299777209)
      ·
        refine ⟨3219885415711197224832907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4293180554281596299777209 3219885415711197224832907)
        ·
          refine ⟨4829828123566795837249361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3219885415711197224832907 4829828123566795837249361)
          ·
            refine ⟨3622371092675096877937021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4829828123566795837249361 3622371092675096877937021)
            ·
              refine ⟨1358389159753161329226383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3622371092675096877937021 1358389159753161329226383)
              ·
                refine ⟨2037583739629741993839575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358389159753161329226383 2037583739629741993839575)
                ·
                  refine ⟨3056375609444612990759363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2037583739629741993839575 3056375609444612990759363)
                  ·
                    refine ⟨4584563414166919486139045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3056375609444612990759363 4584563414166919486139045)
                    ·
                      refine ⟨859605640156297403651071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4584563414166919486139045 859605640156297403651071)
                      ·
                        rfl

theorem cell23_1674076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_1674076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674076 prefixEnd_1674076 := by exact prefixLift 1674076
  have htrace : WordTrace (prefixWord ++ tailWord_1674076) baseStart_1674076 baseEnd_1674076 := by
    simpa [prefixWord, tailWord_1674076, baseEnd_1674076] using wordTrace_append hprefix tailTrace_1674076
  have hstable : (prefixWord ++ tailWord_1674076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674076).length < 2 ^ (prefixWord ++ tailWord_1674076).sum := by decide
  have hdescent : baseEnd_1674076 < baseStart_1674076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674079 : List Nat := [1, 1, 2, 3, 1, 3, 5, 1, 1, 2, 3]
def baseStart_1674079 : Nat := 118140960795 + 1674079 * 2 ^ 59
def prefixEnd_1674079 : Nat := 4983230072969 + 3 ^ 40 * 1674079 * 2
def baseEnd_1674079 : Nat := 859607180598260891913557

theorem tailTrace_1674079 : CollatzResearch.WordTrace tailWord_1674079 prefixEnd_1674079 859607180598260891913557 := by
  unfold tailWord_1674079
  simp only [CollatzResearch.WordTrace]
  refine ⟨61058677302105167775857291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40705784868070111850571527 61058677302105167775857291)
  ·
    refine ⟨91588015953157751663785937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61058677302105167775857291 91588015953157751663785937)
    ·
      refine ⟨68691011964868313747839453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91588015953157751663785937 68691011964868313747839453)
      ·
        refine ⟨25759129486825617655439795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68691011964868313747839453 25759129486825617655439795)
        ·
          refine ⟨38638694230238426483159693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25759129486825617655439795 38638694230238426483159693)
          ·
            refine ⟨14489510336339409931184885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38638694230238426483159693 14489510336339409931184885)
            ·
              refine ⟨1358391594031819681048583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14489510336339409931184885 1358391594031819681048583)
              ·
                refine ⟨2037587391047729521572875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358391594031819681048583 2037587391047729521572875)
                ·
                  refine ⟨3056381086571594282359313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2037587391047729521572875 3056381086571594282359313)
                  ·
                    refine ⟨2292285814928695711769485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3056381086571594282359313 2292285814928695711769485)
                    ·
                      refine ⟨859607180598260891913557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2292285814928695711769485 859607180598260891913557)
                      ·
                        rfl

theorem cell23_1674079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_1674079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674079 prefixEnd_1674079 := by exact prefixLift 1674079
  have htrace : WordTrace (prefixWord ++ tailWord_1674079) baseStart_1674079 baseEnd_1674079 := by
    simpa [prefixWord, tailWord_1674079, baseEnd_1674079] using wordTrace_append hprefix tailTrace_1674079
  have hstable : (prefixWord ++ tailWord_1674079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674079).length < 2 ^ (prefixWord ++ tailWord_1674079).sum := by decide
  have hdescent : baseEnd_1674079 < baseStart_1674079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674082 : List Nat := [3, 3, 2, 1, 4, 10]
def baseStart_1674082 : Nat := 118140960795 + 1674082 * 2 ^ 59
def prefixEnd_1674082 : Nat := 4983230072969 + 3 ^ 40 * 1674082 * 2
def baseEnd_1674082 : Nat := 3537484448725203210601

theorem tailTrace_1674082 : CollatzResearch.WordTrace tailWord_1674082 prefixEnd_1674082 3537484448725203210601 := by
  unfold tailWord_1674082
  simp only [CollatzResearch.WordTrace]
  refine ⟨15264696680273574822054125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40705857814062866192144333 15264696680273574822054125)
  ·
    refine ⟨5724261255102590558270297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15264696680273574822054125 5724261255102590558270297)
    ·
      refine ⟨4293195941326942918702723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5724261255102590558270297 4293195941326942918702723)
      ·
        refine ⟨6439793911990414378054085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4293195941326942918702723 6439793911990414378054085)
        ·
          refine ⟨1207461358498202695885141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6439793911990414378054085 1207461358498202695885141)
          ·
            refine ⟨3537484448725203210601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1207461358498202695885141 3537484448725203210601)
            ·
              rfl

theorem cell23_1674082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 10].length) (baseStart_1674082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674082 prefixEnd_1674082 := by exact prefixLift 1674082
  have htrace : WordTrace (prefixWord ++ tailWord_1674082) baseStart_1674082 baseEnd_1674082 := by
    simpa [prefixWord, tailWord_1674082, baseEnd_1674082] using wordTrace_append hprefix tailTrace_1674082
  have hstable : (prefixWord ++ tailWord_1674082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674082).length < 2 ^ (prefixWord ++ tailWord_1674082).sum := by decide
  have hdescent : baseEnd_1674082 < baseStart_1674082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674109 : List Nat := [1, 4, 1, 1, 2, 1, 4, 3, 2, 1, 3]
def baseStart_1674109 : Nat := 118140960795 + 1674109 * 2 ^ 59
def prefixEnd_1674109 : Nat := 4983230072969 + 3 ^ 40 * 1674109 * 2
def baseEnd_1674109 : Nat := 859622585017895774538419

theorem tailTrace_1674109 : CollatzResearch.WordTrace tailWord_1674109 prefixEnd_1674109 859622585017895774538419 := by
  unfold tailWord_1674109
  simp only [CollatzResearch.WordTrace]
  refine ⟨61059771491996482899449381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40706514327997655266299587 61059771491996482899449381)
  ·
    refine ⟨11448707154749340543646759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61059771491996482899449381 11448707154749340543646759)
    ·
      refine ⟨17173060732124010815470139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11448707154749340543646759 17173060732124010815470139)
      ·
        refine ⟨25759591098186016223205209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17173060732124010815470139 25759591098186016223205209)
        ·
          refine ⟨19319693323639512167403907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25759591098186016223205209 19319693323639512167403907)
          ·
            refine ⟨28979539985459268251105861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19319693323639512167403907 28979539985459268251105861)
            ·
              refine ⟨5433663747273612797082349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28979539985459268251105861 5433663747273612797082349)
              ·
                refine ⟨2037623905227604798905881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5433663747273612797082349 2037623905227604798905881)
                ·
                  refine ⟨1528217928920703599179411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2037623905227604798905881 1528217928920703599179411)
                  ·
                    refine ⟨2292326893381055398769117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1528217928920703599179411 2292326893381055398769117)
                    ·
                      refine ⟨859622585017895774538419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2292326893381055398769117 859622585017895774538419)
                      ·
                        rfl

theorem cell23_1674109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_1674109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674109 prefixEnd_1674109 := by exact prefixLift 1674109
  have htrace : WordTrace (prefixWord ++ tailWord_1674109) baseStart_1674109 baseEnd_1674109 := by
    simpa [prefixWord, tailWord_1674109, baseEnd_1674109] using wordTrace_append hprefix tailTrace_1674109
  have hstable : (prefixWord ++ tailWord_1674109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674109).length < 2 ^ (prefixWord ++ tailWord_1674109).sum := by decide
  have hdescent : baseEnd_1674109 < baseStart_1674109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674115 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 4]
def baseStart_1674115 : Nat := 118140960795 + 1674115 * 2 ^ 59
def prefixEnd_1674115 : Nat := 4983230072969 + 3 ^ 40 * 1674115 * 2
def baseEnd_1674115 : Nat := 859625665901822751063391

theorem tailTrace_1674115 : CollatzResearch.WordTrace tailWord_1674115 prefixEnd_1674115 859625665901822751063391 := by
  unfold tailWord_1674115
  simp only [CollatzResearch.WordTrace]
  refine ⟨61059990329974745924167799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40706660219983163949445199 61059990329974745924167799)
  ·
    refine ⟨91589985494962118886251699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61059990329974745924167799 91589985494962118886251699)
    ·
      refine ⟨137384978242443178329377549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91589985494962118886251699 137384978242443178329377549)
      ·
        refine ⟨51519366840916191873516581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137384978242443178329377549 51519366840916191873516581)
        ·
          refine ⟨9659881282671785976284359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51519366840916191873516581 9659881282671785976284359)
          ·
            refine ⟨14489821924007678964426539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9659881282671785976284359 14489821924007678964426539)
            ·
              refine ⟨21734732886011518446639809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14489821924007678964426539 21734732886011518446639809)
              ·
                refine ⟨16301049664508638834979857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21734732886011518446639809 16301049664508638834979857)
                ·
                  refine ⟨12225787248381479126234893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16301049664508638834979857 12225787248381479126234893)
                  ·
                    refine ⟨4584670218143054672338085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12225787248381479126234893 4584670218143054672338085)
                    ·
                      refine ⟨859625665901822751063391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4584670218143054672338085 859625665901822751063391)
                      ·
                        rfl

theorem cell23_1674115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_1674115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674115 prefixEnd_1674115 := by exact prefixLift 1674115
  have htrace : WordTrace (prefixWord ++ tailWord_1674115) baseStart_1674115 baseEnd_1674115 := by
    simpa [prefixWord, tailWord_1674115, baseEnd_1674115] using wordTrace_append hprefix tailTrace_1674115
  have hstable : (prefixWord ++ tailWord_1674115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674115).length < 2 ^ (prefixWord ++ tailWord_1674115).sum := by decide
  have hdescent : baseEnd_1674115 < baseStart_1674115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674119 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 3, 3, 2]
def baseStart_1674119 : Nat := 118140960795 + 1674119 * 2 ^ 59
def prefixEnd_1674119 : Nat := 4983230072969 + 3 ^ 40 * 1674119 * 2
def baseEnd_1674119 : Nat := 859627719824440735413373

theorem tailTrace_1674119 : CollatzResearch.WordTrace tailWord_1674119 prefixEnd_1674119 859627719824440735413373 := by
  unfold tailWord_1674119
  simp only [CollatzResearch.WordTrace]
  refine ⟨61060136221960254607313411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40706757481306836404875607 61060136221960254607313411)
  ·
    refine ⟨91590204332940381910970117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61060136221960254607313411 91590204332940381910970117)
    ·
      refine ⟨17173163312426321608306897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91590204332940381910970117 17173163312426321608306897)
      ·
        refine ⟨12879872484319741206230173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17173163312426321608306897 12879872484319741206230173)
        ·
          refine ⟨4829952181619902952336315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12879872484319741206230173 4829952181619902952336315)
          ·
            refine ⟨7244928272429854428504473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4829952181619902952336315 7244928272429854428504473)
            ·
              refine ⟨5433696204322390821378355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7244928272429854428504473 5433696204322390821378355)
              ·
                refine ⟨8150544306483586232067533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5433696204322390821378355 8150544306483586232067533)
                ·
                  refine ⟨3056454114931344837025325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8150544306483586232067533 3056454114931344837025325)
                  ·
                    refine ⟨1146170293099254313884497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3056454114931344837025325 1146170293099254313884497)
                    ·
                      refine ⟨859627719824440735413373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1146170293099254313884497 859627719824440735413373)
                      ·
                        rfl

theorem cell23_1674119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_1674119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674119 prefixEnd_1674119 := by exact prefixLift 1674119
  have htrace : WordTrace (prefixWord ++ tailWord_1674119) baseStart_1674119 baseEnd_1674119 := by
    simpa [prefixWord, tailWord_1674119, baseEnd_1674119] using wordTrace_append hprefix tailTrace_1674119
  have hstable : (prefixWord ++ tailWord_1674119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674119).length < 2 ^ (prefixWord ++ tailWord_1674119).sum := by decide
  have hdescent : baseEnd_1674119 < baseStart_1674119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674130 : List Nat := [3, 2, 3, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_1674130 : Nat := 118140960795 + 1674130 * 2 ^ 59
def prefixEnd_1674130 : Nat := 4983230072969 + 3 ^ 40 * 1674130 * 2
def baseEnd_1674130 : Nat := 859633368111640192375823

theorem tailTrace_1674130 : CollatzResearch.WordTrace tailWord_1674130 prefixEnd_1674130 859633368111640192375823 := by
  unfold tailWord_1674130
  simp only [CollatzResearch.WordTrace]
  refine ⟨15265134356230100871490961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40707024949946935657309229 15265134356230100871490961)
  ·
    refine ⟨11448850767172575653618221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15265134356230100871490961 11448850767172575653618221)
    ·
      refine ⟨4293319037689715870106833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11448850767172575653618221 4293319037689715870106833)
      ·
        refine ⟨3219989278267286902580125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4293319037689715870106833 3219989278267286902580125)
        ·
          refine ⟨1207495979350232588467547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3219989278267286902580125 1207495979350232588467547)
          ·
            refine ⟨1811243969025348882701321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207495979350232588467547 1811243969025348882701321)
            ·
              refine ⟨1358432976769011662025991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1811243969025348882701321 1358432976769011662025991)
              ·
                refine ⟨2037649465153517493038987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358432976769011662025991 2037649465153517493038987)
                ·
                  refine ⟨3056474197730276239558481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2037649465153517493038987 3056474197730276239558481)
                  ·
                    refine ⟨2292355648297707179668861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3056474197730276239558481 2292355648297707179668861)
                    ·
                      refine ⟨859633368111640192375823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2292355648297707179668861 859633368111640192375823)
                      ·
                        rfl

theorem cell23_1674130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_1674130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674130 prefixEnd_1674130 := by exact prefixLift 1674130
  have htrace : WordTrace (prefixWord ++ tailWord_1674130) baseStart_1674130 baseEnd_1674130 := by
    simpa [prefixWord, tailWord_1674130, baseEnd_1674130] using wordTrace_append hprefix tailTrace_1674130
  have hstable : (prefixWord ++ tailWord_1674130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674130).length < 2 ^ (prefixWord ++ tailWord_1674130).sum := by decide
  have hdescent : baseEnd_1674130 < baseStart_1674130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674135 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 5]
def baseStart_1674135 : Nat := 118140960795 + 1674135 * 2 ^ 59
def prefixEnd_1674135 : Nat := 4983230072969 + 3 ^ 40 * 1674135 * 2
def baseEnd_1674135 : Nat := 859635935514912672813299

theorem tailTrace_1674135 : CollatzResearch.WordTrace tailWord_1674135 prefixEnd_1674135 859635935514912672813299 := by
  unfold tailWord_1674135
  simp only [CollatzResearch.WordTrace]
  refine ⟨61060719789902289339895859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40707146526601526226597239 61060719789902289339895859)
  ·
    refine ⟨91591079684853434009843789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61060719789902289339895859 91591079684853434009843789)
    ·
      refine ⟨34346654881820037753691421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91591079684853434009843789 34346654881820037753691421)
      ·
        refine ⟨12879995580682514157634283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34346654881820037753691421 12879995580682514157634283)
        ·
          refine ⟨19319993371023771236451425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12879995580682514157634283 19319993371023771236451425)
          ·
            refine ⟨14489995028267828427338569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19319993371023771236451425 14489995028267828427338569)
            ·
              refine ⟨10867496271200871320503927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14489995028267828427338569 10867496271200871320503927)
              ·
                refine ⟨16301244406801306980755891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10867496271200871320503927 16301244406801306980755891)
                ·
                  refine ⟨24451866610201960471133837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16301244406801306980755891 24451866610201960471133837)
                  ·
                    refine ⟨9169449978825735176675189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24451866610201960471133837 9169449978825735176675189)
                    ·
                      refine ⟨859635935514912672813299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9169449978825735176675189 859635935514912672813299)
                      ·
                        rfl

theorem cell23_1674135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_1674135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674135 prefixEnd_1674135 := by exact prefixLift 1674135
  have htrace : WordTrace (prefixWord ++ tailWord_1674135) baseStart_1674135 baseEnd_1674135 := by
    simpa [prefixWord, tailWord_1674135, baseEnd_1674135] using wordTrace_append hprefix tailTrace_1674135
  have hstable : (prefixWord ++ tailWord_1674135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674135).length < 2 ^ (prefixWord ++ tailWord_1674135).sum := by decide
  have hdescent : baseEnd_1674135 < baseStart_1674135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674192 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 1, 7, 2]
def baseStart_1674192 : Nat := 118140960795 + 1674192 * 2 ^ 59
def prefixEnd_1674192 : Nat := 4983230072969 + 3 ^ 40 * 1674192 * 2
def baseEnd_1674192 : Nat := 859665203912218949800537

theorem tailTrace_1674192 : CollatzResearch.WordTrace tailWord_1674192 prefixEnd_1674192 859665203912218949800537 := by
  unfold tailWord_1674192
  simp only [CollatzResearch.WordTrace]
  refine ⟨30531399375347894037360415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40708532500463858716480553 30531399375347894037360415)
  ·
    refine ⟨45797099063021841056040623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30531399375347894037360415 45797099063021841056040623)
    ·
      refine ⟨68695648594532761584060935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45797099063021841056040623 68695648594532761584060935)
      ·
        refine ⟨103043472891799142376091403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68695648594532761584060935 103043472891799142376091403)
        ·
          refine ⟨154565209337698713564137105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103043472891799142376091403 154565209337698713564137105)
          ·
            refine ⟨115923907003274035173102829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154565209337698713564137105 115923907003274035173102829)
            ·
              refine ⟨43471465126227763189913561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115923907003274035173102829 43471465126227763189913561)
              ·
                refine ⟨32603598844670822392435171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43471465126227763189913561 32603598844670822392435171)
                ·
                  refine ⟨48905398267006233588652757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32603598844670822392435171 48905398267006233588652757)
                  ·
                    refine ⟨1146220271882958599734049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48905398267006233588652757 1146220271882958599734049)
                    ·
                      refine ⟨859665203912218949800537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1146220271882958599734049 859665203912218949800537)
                      ·
                        rfl

theorem cell23_1674192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 7, 2].length) (baseStart_1674192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674192 prefixEnd_1674192 := by exact prefixLift 1674192
  have htrace : WordTrace (prefixWord ++ tailWord_1674192) baseStart_1674192 baseEnd_1674192 := by
    simpa [prefixWord, tailWord_1674192, baseEnd_1674192] using wordTrace_append hprefix tailTrace_1674192
  have hstable : (prefixWord ++ tailWord_1674192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674192).length < 2 ^ (prefixWord ++ tailWord_1674192).sum := by decide
  have hdescent : baseEnd_1674192 < baseStart_1674192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674202 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 4, 5]
def baseStart_1674202 : Nat := 118140960795 + 1674202 * 2 ^ 59
def prefixEnd_1674202 : Nat := 4983230072969 + 3 ^ 40 * 1674202 * 2
def baseEnd_1674202 : Nat := 286556779572921303558497

theorem tailTrace_1674202 : CollatzResearch.WordTrace tailWord_1674202 prefixEnd_1674202 286556779572921303558497 := by
  unfold tailWord_1674202
  simp only [CollatzResearch.WordTrace]
  refine ⟨15265790870164889945646215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40708775653773039855056573 15265790870164889945646215)
  ·
    refine ⟨22898686305247334918469323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15265790870164889945646215 22898686305247334918469323)
    ·
      refine ⟨34348029457871002377703985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22898686305247334918469323 34348029457871002377703985)
      ·
        refine ⟨25761022093403251783277989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34348029457871002377703985 25761022093403251783277989)
        ·
          refine ⟨4830191642513109709364623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25761022093403251783277989 4830191642513109709364623)
          ·
            refine ⟨7245287463769664564046935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4830191642513109709364623 7245287463769664564046935)
            ·
              refine ⟨10867931195654496846070403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7245287463769664564046935 10867931195654496846070403)
              ·
                refine ⟨16301896793481745269105605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10867931195654496846070403 16301896793481745269105605)
                ·
                  refine ⟨3056605648777827237957301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16301896793481745269105605 3056605648777827237957301)
                  ·
                    refine ⟨286556779572921303558497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3056605648777827237957301 286556779572921303558497)
                    ·
                      rfl

theorem cell23_1674202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_1674202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674202 prefixEnd_1674202 := by exact prefixLift 1674202
  have htrace : WordTrace (prefixWord ++ tailWord_1674202) baseStart_1674202 baseEnd_1674202 := by
    simpa [prefixWord, tailWord_1674202, baseEnd_1674202] using wordTrace_append hprefix tailTrace_1674202
  have hstable : (prefixWord ++ tailWord_1674202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674202).length < 2 ^ (prefixWord ++ tailWord_1674202).sum := by decide
  have hdescent : baseEnd_1674202 < baseStart_1674202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674232 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 5, 4]
def baseStart_1674232 : Nat := 118140960795 + 1674232 * 2 ^ 59
def prefixEnd_1674232 : Nat := 4983230072969 + 3 ^ 40 * 1674232 * 2
def baseEnd_1674232 : Nat := 286561914379466264433451

theorem tailTrace_1674232 : CollatzResearch.WordTrace tailWord_1674232 prefixEnd_1674232 286561914379466264433451 := by
  unfold tailWord_1674232
  simp only [CollatzResearch.WordTrace]
  refine ⟨30532128835275437453088475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40709505113700583270784633 30532128835275437453088475)
  ·
    refine ⟨45798193252913156179632713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30532128835275437453088475 45798193252913156179632713)
    ·
      refine ⟨34348644939684867134724535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45798193252913156179632713 34348644939684867134724535)
      ·
        refine ⟨51522967409527300702086803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34348644939684867134724535 51522967409527300702086803)
        ·
          refine ⟨77284451114290951053130205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51522967409527300702086803 77284451114290951053130205)
          ·
            refine ⟨28981669167859106644923827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77284451114290951053130205 28981669167859106644923827)
            ·
              refine ⟨43472503751788659967385741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28981669167859106644923827 43472503751788659967385741)
              ·
                refine ⟨16302188906920747487769653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43472503751788659967385741 16302188906920747487769653)
                ·
                  refine ⟨1528330210023820076978405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16302188906920747487769653 1528330210023820076978405)
                  ·
                    refine ⟨286561914379466264433451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1528330210023820076978405 286561914379466264433451)
                    ·
                      rfl

theorem cell23_1674232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_1674232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674232 prefixEnd_1674232 := by exact prefixLift 1674232
  have htrace : WordTrace (prefixWord ++ tailWord_1674232) baseStart_1674232 baseEnd_1674232 := by
    simpa [prefixWord, tailWord_1674232, baseEnd_1674232] using wordTrace_append hprefix tailTrace_1674232
  have hstable : (prefixWord ++ tailWord_1674232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674232).length < 2 ^ (prefixWord ++ tailWord_1674232).sum := by decide
  have hdescent : baseEnd_1674232 < baseStart_1674232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674235 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 6]
def baseStart_1674235 : Nat := 118140960795 + 1674235 * 2 ^ 59
def prefixEnd_1674235 : Nat := 4983230072969 + 3 ^ 40 * 1674235 * 2
def baseEnd_1674235 : Nat := 859687283580362281562839

theorem tailTrace_1674235 : CollatzResearch.WordTrace tailWord_1674235 prefixEnd_1674235 859687283580362281562839 := by
  unfold tailWord_1674235
  simp only [CollatzResearch.WordTrace]
  refine ⟨61064367089540006418536159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40709578059693337612357439 61064367089540006418536159)
  ·
    refine ⟨91596550634310009627804239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61064367089540006418536159 91596550634310009627804239)
    ·
      refine ⟨137394825951465014441706359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91596550634310009627804239 137394825951465014441706359)
      ·
        refine ⟨206092238927197521662559539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137394825951465014441706359 206092238927197521662559539)
        ·
          refine ⟨309138358390796282493839309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206092238927197521662559539 309138358390796282493839309)
          ·
            refine ⟨115926884396548605935189741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309138358390796282493839309 115926884396548605935189741)
            ·
              refine ⟨43472581648705727225696153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115926884396548605935189741 43472581648705727225696153)
              ·
                refine ⟨32604436236529295419272115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43472581648705727225696153 32604436236529295419272115)
                ·
                  refine ⟨48906654354793943128908173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32604436236529295419272115 48906654354793943128908173)
                  ·
                    refine ⟨18339995383047728673340565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48906654354793943128908173 18339995383047728673340565)
                    ·
                      refine ⟨859687283580362281562839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18339995383047728673340565 859687283580362281562839)
                      ·
                        rfl

theorem cell23_1674235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 6].length) (baseStart_1674235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674235 prefixEnd_1674235 := by exact prefixLift 1674235
  have htrace : WordTrace (prefixWord ++ tailWord_1674235) baseStart_1674235 baseEnd_1674235 := by
    simpa [prefixWord, tailWord_1674235, baseEnd_1674235] using wordTrace_append hprefix tailTrace_1674235
  have hstable : (prefixWord ++ tailWord_1674235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674235).length < 2 ^ (prefixWord ++ tailWord_1674235).sum := by decide
  have hdescent : baseEnd_1674235 < baseStart_1674235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674255 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 7]
def baseStart_1674255 : Nat := 118140960795 + 1674255 * 2 ^ 59
def prefixEnd_1674255 : Nat := 4983230072969 + 3 ^ 40 * 1674255 * 2
def baseEnd_1674255 : Nat := 859697553193452203312747

theorem tailTrace_1674255 : CollatzResearch.WordTrace tailWord_1674255 prefixEnd_1674255 859697553193452203312747 := by
  unfold tailWord_1674255
  simp only [CollatzResearch.WordTrace]
  refine ⟨61065096549467549834264219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40710064366311699889509479 61065096549467549834264219)
  ·
    refine ⟨91597644824201324751396329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61065096549467549834264219 91597644824201324751396329)
    ·
      refine ⟨68698233618150993563547247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91597644824201324751396329 68698233618150993563547247)
      ·
        refine ⟨103047350427226490345320871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68698233618150993563547247 103047350427226490345320871)
        ·
          refine ⟨154571025640839735517981307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103047350427226490345320871 154571025640839735517981307)
          ·
            refine ⟨231856538461259603276971961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154571025640839735517981307 231856538461259603276971961)
            ·
              refine ⟨173892403845944702457728971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231856538461259603276971961 173892403845944702457728971)
              ·
                refine ⟨260838605768917053686593457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173892403845944702457728971 260838605768917053686593457)
                ·
                  refine ⟨195628954326687790264945093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260838605768917053686593457 195628954326687790264945093)
                  ·
                    refine ⟨36680428936253960674677205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 195628954326687790264945093 36680428936253960674677205)
                    ·
                      refine ⟨859697553193452203312747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36680428936253960674677205 859697553193452203312747)
                      ·
                        rfl

theorem cell23_1674255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_1674255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674255 prefixEnd_1674255 := by exact prefixLift 1674255
  have htrace : WordTrace (prefixWord ++ tailWord_1674255) baseStart_1674255 baseEnd_1674255 := by
    simpa [prefixWord, tailWord_1674255, baseEnd_1674255] using wordTrace_append hprefix tailTrace_1674255
  have hstable : (prefixWord ++ tailWord_1674255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674255).length < 2 ^ (prefixWord ++ tailWord_1674255).sum := by decide
  have hdescent : baseEnd_1674255 < baseStart_1674255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674266 : List Nat := [3, 1, 1, 3, 1, 2, 3, 4, 1, 4]
def baseStart_1674266 : Nat := 118140960795 + 1674266 * 2 ^ 59
def prefixEnd_1674266 : Nat := 4983230072969 + 3 ^ 40 * 1674266 * 2
def baseEnd_1674266 : Nat := 286567733826883886758399

theorem tailTrace_1674266 : CollatzResearch.WordTrace tailWord_1674266 prefixEnd_1674266 286567733826883886758399 := by
  unfold tailWord_1674266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15266374438106924678228663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40710331834951799141943101 15266374438106924678228663)
  ·
    refine ⟨22899561657160387017342995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15266374438106924678228663 22899561657160387017342995)
    ·
      refine ⟨34349342485740580526014493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22899561657160387017342995 34349342485740580526014493)
      ·
        refine ⟨12881003432152717697255435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34349342485740580526014493 12881003432152717697255435)
        ·
          refine ⟨19321505148229076545883153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12881003432152717697255435 19321505148229076545883153)
          ·
            refine ⟨14491128861171807409412365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19321505148229076545883153 14491128861171807409412365)
            ·
              refine ⟨5434173322939427778529637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14491128861171807409412365 5434173322939427778529637)
              ·
                refine ⟨1018907498051142708474307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5434173322939427778529637 1018907498051142708474307)
                ·
                  refine ⟨1528361247076714062711461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1018907498051142708474307 1528361247076714062711461)
                  ·
                    refine ⟨286567733826883886758399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1528361247076714062711461 286567733826883886758399)
                    ·
                      rfl

theorem cell23_1674266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 1, 4].length) (baseStart_1674266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674266 prefixEnd_1674266 := by exact prefixLift 1674266
  have htrace : WordTrace (prefixWord ++ tailWord_1674266) baseStart_1674266 baseEnd_1674266 := by
    simpa [prefixWord, tailWord_1674266, baseEnd_1674266] using wordTrace_append hprefix tailTrace_1674266
  have hstable : (prefixWord ++ tailWord_1674266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674266).length < 2 ^ (prefixWord ++ tailWord_1674266).sum := by decide
  have hdescent : baseEnd_1674266 < baseStart_1674266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674346 : List Nat := [3, 1, 3, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_1674346 : Nat := 118140960795 + 1674346 * 2 ^ 59
def prefixEnd_1674346 : Nat := 4983230072969 + 3 ^ 40 * 1674346 * 2
def baseEnd_1674346 : Nat := 859744279933011347274829

theorem tailTrace_1674346 : CollatzResearch.WordTrace tailWord_1674346 prefixEnd_1674346 859744279933011347274829 := by
  unfold tailWord_1674346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15267103898034468093956723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40712277061425248250551261 15267103898034468093956723)
  ·
    refine ⟨22900655847051702140935085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15267103898034468093956723 22900655847051702140935085)
    ·
      refine ⟨8587745942644388302850657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22900655847051702140935085 8587745942644388302850657)
      ·
        refine ⟨6440809456983291227137993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8587745942644388302850657 6440809456983291227137993)
        ·
          refine ⟨4830607092737468420353495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6440809456983291227137993 4830607092737468420353495)
          ·
            refine ⟨7245910639106202630530243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4830607092737468420353495 7245910639106202630530243)
            ·
              refine ⟨10868865958659303945795365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7245910639106202630530243 10868865958659303945795365)
              ·
                refine ⟨2037912367248619489836631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10868865958659303945795365 2037912367248619489836631)
                ·
                  refine ⟨3056868550872929234754947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2037912367248619489836631 3056868550872929234754947)
                  ·
                    refine ⟨4585302826309393852132421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3056868550872929234754947 4585302826309393852132421)
                    ·
                      refine ⟨859744279933011347274829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4585302826309393852132421 859744279933011347274829)
                      ·
                        rfl

theorem cell23_1674346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_1674346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674346 prefixEnd_1674346 := by exact prefixLift 1674346
  have htrace : WordTrace (prefixWord ++ tailWord_1674346) baseStart_1674346 baseEnd_1674346 := by
    simpa [prefixWord, tailWord_1674346, baseEnd_1674346] using wordTrace_append hprefix tailTrace_1674346
  have hstable : (prefixWord ++ tailWord_1674346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674346).length < 2 ^ (prefixWord ++ tailWord_1674346).sum := by decide
  have hdescent : baseEnd_1674346 < baseStart_1674346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674352 : List Nat := [2, 1, 1, 1, 5, 1, 3, 9]
def baseStart_1674352 : Nat := 118140960795 + 1674352 * 2 ^ 59
def prefixEnd_1674352 : Nat := 4983230072969 + 3 ^ 40 * 1674352 * 2
def baseEnd_1674352 : Nat := 31842494845071789770363

theorem tailTrace_1674352 : CollatzResearch.WordTrace tailWord_1674352 prefixEnd_1674352 31842494845071789770363 := by
  unfold tailWord_1674352
  simp only [CollatzResearch.WordTrace]
  refine ⟨30534317215058067700272655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40712422953410756933696873 30534317215058067700272655)
  ·
    refine ⟨45801475822587101550408983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30534317215058067700272655 45801475822587101550408983)
    ·
      refine ⟨68702213733880652325613475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45801475822587101550408983 68702213733880652325613475)
      ·
        refine ⟨103053320600820978488420213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68702213733880652325613475 103053320600820978488420213)
        ·
          refine ⟨9661248806326966733289395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103053320600820978488420213 9661248806326966733289395)
          ·
            refine ⟨14491873209490450099934093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9661248806326966733289395 14491873209490450099934093)
            ·
              refine ⟨5434452453558918787475285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14491873209490450099934093 5434452453558918787475285)
              ·
                refine ⟨31842494845071789770363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5434452453558918787475285 31842494845071789770363)
                ·
                  rfl

theorem cell23_1674352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 9].length) (baseStart_1674352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674352 prefixEnd_1674352 := by exact prefixLift 1674352
  have htrace : WordTrace (prefixWord ++ tailWord_1674352) baseStart_1674352 baseEnd_1674352 := by
    simpa [prefixWord, tailWord_1674352, baseEnd_1674352] using wordTrace_append hprefix tailTrace_1674352
  have hstable : (prefixWord ++ tailWord_1674352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674352).length < 2 ^ (prefixWord ++ tailWord_1674352).sum := by decide
  have hdescent : baseEnd_1674352 < baseStart_1674352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674369 : List Nat := [1, 2, 4, 2, 2, 3, 9]
def baseStart_1674369 : Nat := 118140960795 + 1674369 * 2 ^ 59
def prefixEnd_1674369 : Nat := 4983230072969 + 3 ^ 40 * 1674369 * 2
def baseEnd_1674369 : Nat := 10614272715902034040583

theorem tailTrace_1674369 : CollatzResearch.WordTrace tailWord_1674369 prefixEnd_1674369 10614272715902034040583 := by
  unfold tailWord_1674369
  simp only [CollatzResearch.WordTrace]
  refine ⟨61069254471054547303914161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40712836314036364869276107 61069254471054547303914161)
  ·
    refine ⟨45801940853290910477935621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61069254471054547303914161 45801940853290910477935621)
    ·
      refine ⟨8587863909992045714612929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45801940853290910477935621 8587863909992045714612929)
      ·
        refine ⟨6440897932494034285959697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8587863909992045714612929 6440897932494034285959697)
        ·
          refine ⟨4830673449370525714469773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6440897932494034285959697 4830673449370525714469773)
          ·
            refine ⟨1811502543513947142926165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4830673449370525714469773 1811502543513947142926165)
            ·
              refine ⟨10614272715902034040583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1811502543513947142926165 10614272715902034040583)
              ·
                rfl

theorem cell23_1674369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 9].length) (baseStart_1674369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674369 prefixEnd_1674369 := by exact prefixLift 1674369
  have htrace : WordTrace (prefixWord ++ tailWord_1674369) baseStart_1674369 baseEnd_1674369 := by
    simpa [prefixWord, tailWord_1674369, baseEnd_1674369] using wordTrace_append hprefix tailTrace_1674369
  have hstable : (prefixWord ++ tailWord_1674369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674369).length < 2 ^ (prefixWord ++ tailWord_1674369).sum := by decide
  have hdescent : baseEnd_1674369 < baseStart_1674369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674412 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 3, 8]
def baseStart_1674412 : Nat := 118140960795 + 1674412 * 2 ^ 59
def prefixEnd_1674412 : Nat := 4983230072969 + 3 ^ 40 * 1674412 * 2
def baseEnd_1674412 : Nat := 286592723218736029683175

theorem tailTrace_1674412 : CollatzResearch.WordTrace tailWord_1674412 prefixEnd_1674412 286592723218736029683175 := by
  unfold tailWord_1674412
  simp only [CollatzResearch.WordTrace]
  refine ⟨30535411404949382823864745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40713881873265843765152993 30535411404949382823864745)
  ·
    refine ⟨22901558553712037117898559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30535411404949382823864745 22901558553712037117898559)
    ·
      refine ⟨34352337830568055676847839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22901558553712037117898559 34352337830568055676847839)
      ·
        refine ⟨51528506745852083515271759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34352337830568055676847839 51528506745852083515271759)
        ·
          refine ⟨77292760118778125272907639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51528506745852083515271759 77292760118778125272907639)
          ·
            refine ⟨115939140178167187909361459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77292760118778125272907639 115939140178167187909361459)
            ·
              refine ⟨173908710267250781864042189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115939140178167187909361459 173908710267250781864042189)
              ·
                refine ⟨65215766350219043199015821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173908710267250781864042189 65215766350219043199015821)
                ·
                  refine ⟨24455912381332141199630933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65215766350219043199015821 24455912381332141199630933)
                  ·
                    refine ⟨286592723218736029683175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24455912381332141199630933 286592723218736029683175)
                    ·
                      rfl

theorem cell23_1674412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_1674412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674412 prefixEnd_1674412 := by exact prefixLift 1674412
  have htrace : WordTrace (prefixWord ++ tailWord_1674412) baseStart_1674412 baseEnd_1674412 := by
    simpa [prefixWord, tailWord_1674412, baseEnd_1674412] using wordTrace_append hprefix tailTrace_1674412
  have hstable : (prefixWord ++ tailWord_1674412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674412).length < 2 ^ (prefixWord ++ tailWord_1674412).sum := by decide
  have hdescent : baseEnd_1674412 < baseStart_1674412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674413 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_1674413 : Nat := 118140960795 + 1674413 * 2 ^ 59
def prefixEnd_1674413 : Nat := 4983230072969 + 3 ^ 40 * 1674413 * 2
def baseEnd_1674413 : Nat := 859778683136862585137021

theorem tailTrace_1674413 : CollatzResearch.WordTrace tailWord_1674413 prefixEnd_1674413 859778683136862585137021 := by
  unfold tailWord_1674413
  simp only [CollatzResearch.WordTrace]
  refine ⟨61070859282895142818515893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40713906188596761879010595 61070859282895142818515893)
  ·
    refine ⟨5725393057771419639235865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61070859282895142818515893 5725393057771419639235865)
    ·
      refine ⟨4294044793328564729426899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5725393057771419639235865 4294044793328564729426899)
      ·
        refine ⟨6441067189992847094140349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4294044793328564729426899 6441067189992847094140349)
        ·
          refine ⟨2415400196247317660302631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6441067189992847094140349 2415400196247317660302631)
          ·
            refine ⟨3623100294370976490453947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2415400196247317660302631 3623100294370976490453947)
            ·
              refine ⟨5434650441556464735680921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3623100294370976490453947 5434650441556464735680921)
              ·
                refine ⟨4075987831167348551760691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5434650441556464735680921 4075987831167348551760691)
                ·
                  refine ⟨6113981746751022827641037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4075987831167348551760691 6113981746751022827641037)
                  ·
                    refine ⟨2292743155031633560365389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6113981746751022827641037 2292743155031633560365389)
                    ·
                      refine ⟨859778683136862585137021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2292743155031633560365389 859778683136862585137021)
                      ·
                        rfl

theorem cell23_1674413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_1674413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674413 prefixEnd_1674413 := by exact prefixLift 1674413
  have htrace : WordTrace (prefixWord ++ tailWord_1674413) baseStart_1674413 baseEnd_1674413 := by
    simpa [prefixWord, tailWord_1674413, baseEnd_1674413] using wordTrace_append hprefix tailTrace_1674413
  have hstable : (prefixWord ++ tailWord_1674413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674413).length < 2 ^ (prefixWord ++ tailWord_1674413).sum := by decide
  have hdescent : baseEnd_1674413 < baseStart_1674413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674430 : List Nat := [4, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_1674430 : Nat := 118140960795 + 1674430 * 2 ^ 59
def prefixEnd_1674430 : Nat := 4983230072969 + 3 ^ 40 * 1674430 * 2
def baseEnd_1674430 : Nat := 859787412307989018624443

theorem tailTrace_1674430 : CollatzResearch.WordTrace tailWord_1674430 prefixEnd_1674430 859787412307989018624443 := by
  unfold tailWord_1674430
  simp only [CollatzResearch.WordTrace]
  refine ⟨7633934915479194340235593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40714319549222369814589829 7633934915479194340235593)
  ·
    refine ⟨5725451186609395755176695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7633934915479194340235593 5725451186609395755176695)
    ·
      refine ⟨8588176779914093632765043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5725451186609395755176695 8588176779914093632765043)
      ·
        refine ⟨12882265169871140449147565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8588176779914093632765043 12882265169871140449147565)
        ·
          refine ⟨4830849438701677668430337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12882265169871140449147565 4830849438701677668430337)
          ·
            refine ⟨3623137079026258251322753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4830849438701677668430337 3623137079026258251322753)
            ·
              refine ⟨2717352809269693688492065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3623137079026258251322753 2717352809269693688492065)
              ·
                refine ⟨2038014606952270266369049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2717352809269693688492065 2038014606952270266369049)
                ·
                  refine ⟨1528510955214202699776787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2038014606952270266369049 1528510955214202699776787)
                  ·
                    refine ⟨2292766432821304049665181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1528510955214202699776787 2292766432821304049665181)
                    ·
                      refine ⟨859787412307989018624443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2292766432821304049665181 859787412307989018624443)
                      ·
                        rfl

theorem cell23_1674430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_1674430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674430 prefixEnd_1674430 := by exact prefixLift 1674430
  have htrace : WordTrace (prefixWord ++ tailWord_1674430) baseStart_1674430 baseEnd_1674430 := by
    simpa [prefixWord, tailWord_1674430, baseEnd_1674430] using wordTrace_append hprefix tailTrace_1674430
  have hstable : (prefixWord ++ tailWord_1674430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674430).length < 2 ^ (prefixWord ++ tailWord_1674430).sum := by decide
  have hdescent : baseEnd_1674430 < baseStart_1674430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674446 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 2, 6]
def baseStart_1674446 : Nat := 118140960795 + 1674446 * 2 ^ 59
def prefixEnd_1674446 : Nat := 4983230072969 + 3 ^ 40 * 1674446 * 2
def baseEnd_1674446 : Nat := 286598542666153652008123

theorem tailTrace_1674446 : CollatzResearch.WordTrace tailWord_1674446 prefixEnd_1674446 286598542666153652008123 := by
  unfold tailWord_1674446
  simp only [CollatzResearch.WordTrace]
  refine ⟨7634007861471948681808399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40714708594517059636311461 7634007861471948681808399)
  ·
    refine ⟨11451011792207923022712599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7634007861471948681808399 11451011792207923022712599)
    ·
      refine ⟨17176517688311884534068899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11451011792207923022712599 17176517688311884534068899)
      ·
        refine ⟨25764776532467826801103349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17176517688311884534068899 25764776532467826801103349)
        ·
          refine ⟨2415447799918858762603439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25764776532467826801103349 2415447799918858762603439)
          ·
            refine ⟨3623171699878288143905159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2415447799918858762603439 3623171699878288143905159)
            ·
              refine ⟨5434757549817432215857739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3623171699878288143905159 5434757549817432215857739)
              ·
                refine ⟨8152136324726148323786609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5434757549817432215857739 8152136324726148323786609)
                ·
                  refine ⟨6114102243544611242839957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8152136324726148323786609 6114102243544611242839957)
                  ·
                    refine ⟨286598542666153652008123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6114102243544611242839957 286598542666153652008123)
                    ·
                      rfl

theorem cell23_1674446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_1674446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674446 prefixEnd_1674446 := by exact prefixLift 1674446
  have htrace : WordTrace (prefixWord ++ tailWord_1674446) baseStart_1674446 baseEnd_1674446 := by
    simpa [prefixWord, tailWord_1674446, baseEnd_1674446] using wordTrace_append hprefix tailTrace_1674446
  have hstable : (prefixWord ++ tailWord_1674446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674446).length < 2 ^ (prefixWord ++ tailWord_1674446).sum := by decide
  have hdescent : baseEnd_1674446 < baseStart_1674446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674453 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 1, 4, 2]
def baseStart_1674453 : Nat := 118140960795 + 1674453 * 2 ^ 59
def prefixEnd_1674453 : Nat := 4983230072969 + 3 ^ 40 * 1674453 * 2
def baseEnd_1674453 : Nat := 859799222363042428636837

theorem tailTrace_1674453 : CollatzResearch.WordTrace tailWord_1674453 prefixEnd_1674453 859799222363042428636837 := by
  unfold tailWord_1674453
  simp only [CollatzResearch.WordTrace]
  refine ⟨61072318202750229649972013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40714878801833486433314675 61072318202750229649972013)
  ·
    refine ⟨22902119326031336118739505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61072318202750229649972013 22902119326031336118739505)
    ·
      refine ⟨17176589494523502089054629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22902119326031336118739505 17176589494523502089054629)
      ·
        refine ⟨3220610530223156641697743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17176589494523502089054629 3220610530223156641697743)
        ·
          refine ⟨4830915795334734962546615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3220610530223156641697743 4830915795334734962546615)
          ·
            refine ⟨7246373693002102443819923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4830915795334734962546615 7246373693002102443819923)
            ·
              refine ⟨10869560539503153665729885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7246373693002102443819923 10869560539503153665729885)
              ·
                refine ⟨4076085202313682624648707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10869560539503153665729885 4076085202313682624648707)
                ·
                  refine ⟨6114127803470523936973061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4076085202313682624648707 6114127803470523936973061)
                  ·
                    refine ⟨1146398963150723238182449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6114127803470523936973061 1146398963150723238182449)
                    ·
                      refine ⟨859799222363042428636837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1146398963150723238182449 859799222363042428636837)
                      ·
                        rfl

theorem cell23_1674453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_1674453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674453 prefixEnd_1674453 := by exact prefixLift 1674453
  have htrace : WordTrace (prefixWord ++ tailWord_1674453) baseStart_1674453 baseEnd_1674453 := by
    simpa [prefixWord, tailWord_1674453, baseEnd_1674453] using wordTrace_append hprefix tailTrace_1674453
  have hstable : (prefixWord ++ tailWord_1674453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674453).length < 2 ^ (prefixWord ++ tailWord_1674453).sum := by decide
  have hdescent : baseEnd_1674453 < baseStart_1674453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674476 : List Nat := [2, 2, 1, 1, 2, 4, 1, 5, 5]
def baseStart_1674476 : Nat := 118140960795 + 1674476 * 2 ^ 59
def prefixEnd_1674476 : Nat := 4983230072969 + 3 ^ 40 * 1674476 * 2
def baseEnd_1674476 : Nat := 95534559157566204294359

theorem tailTrace_1674476 : CollatzResearch.WordTrace tailWord_1674476 prefixEnd_1674476 95534559157566204294359 := by
  unfold tailWord_1674476
  simp only [CollatzResearch.WordTrace]
  refine ⟨30536578540833452289029641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40715438054444603052039521 30536578540833452289029641)
  ·
    refine ⟨22902433905625089216772231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30536578540833452289029641 22902433905625089216772231)
    ·
      refine ⟨34353650858437633825158347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22902433905625089216772231 34353650858437633825158347)
      ·
        refine ⟨51530476287656450737737521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34353650858437633825158347 51530476287656450737737521)
        ·
          refine ⟨38647857215742338053303141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51530476287656450737737521 38647857215742338053303141)
          ·
            refine ⟨7246473227951688384994339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38647857215742338053303141 7246473227951688384994339)
            ·
              refine ⟨10869709841927532577491509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7246473227951688384994339 10869709841927532577491509)
              ·
                refine ⟨1019035297680706179139829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10869709841927532577491509 1019035297680706179139829)
                ·
                  refine ⟨95534559157566204294359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1019035297680706179139829 95534559157566204294359)
                  ·
                    rfl

theorem cell23_1674476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 5].length) (baseStart_1674476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674476 prefixEnd_1674476 := by exact prefixLift 1674476
  have htrace : WordTrace (prefixWord ++ tailWord_1674476) baseStart_1674476 baseEnd_1674476 := by
    simpa [prefixWord, tailWord_1674476, baseEnd_1674476] using wordTrace_append hprefix tailTrace_1674476
  have hstable : (prefixWord ++ tailWord_1674476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674476).length < 2 ^ (prefixWord ++ tailWord_1674476).sum := by decide
  have hdescent : baseEnd_1674476 < baseStart_1674476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674489 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 4, 5]
def baseStart_1674489 : Nat := 118140960795 + 1674489 * 2 ^ 59
def prefixEnd_1674489 : Nat := 4983230072969 + 3 ^ 40 * 1674489 * 2
def baseEnd_1674489 : Nat := 286605902555534762595557

theorem tailTrace_1674489 : CollatzResearch.WordTrace tailWord_1674489 prefixEnd_1674489 286605902555534762595557 := by
  unfold tailWord_1674489
  simp only [CollatzResearch.WordTrace]
  refine ⟨61073631230619807798282521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40715754153746538532188347 61073631230619807798282521)
  ·
    refine ⟨45805223422964855848711891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61073631230619807798282521 45805223422964855848711891)
    ·
      refine ⟨68707835134447283773067837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45805223422964855848711891 68707835134447283773067837)
      ·
        refine ⟨25765438175417731414900439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68707835134447283773067837 25765438175417731414900439)
        ·
          refine ⟨38648157263126597122350659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25765438175417731414900439 38648157263126597122350659)
          ·
            refine ⟨57972235894689895683525989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38648157263126597122350659 57972235894689895683525989)
            ·
              refine ⟨10869794230254355440661123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57972235894689895683525989 10869794230254355440661123)
              ·
                refine ⟨16304691345381533160991685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10869794230254355440661123 16304691345381533160991685)
                ·
                  refine ⟨3057129627259037467685941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16304691345381533160991685 3057129627259037467685941)
                  ·
                    refine ⟨286605902555534762595557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3057129627259037467685941 286605902555534762595557)
                    ·
                      rfl

theorem cell23_1674489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 5].length) (baseStart_1674489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674489 prefixEnd_1674489 := by exact prefixLift 1674489
  have htrace : WordTrace (prefixWord ++ tailWord_1674489) baseStart_1674489 baseEnd_1674489 := by
    simpa [prefixWord, tailWord_1674489, baseEnd_1674489] using wordTrace_append hprefix tailTrace_1674489
  have hstable : (prefixWord ++ tailWord_1674489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674489).length < 2 ^ (prefixWord ++ tailWord_1674489).sum := by decide
  have hdescent : baseEnd_1674489 < baseStart_1674489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674519 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 2, 8]
def baseStart_1674519 : Nat := 118140960795 + 1674519 * 2 ^ 59
def prefixEnd_1674519 : Nat := 4983230072969 + 3 ^ 40 * 1674519 * 2
def baseEnd_1674519 : Nat := 286611037362079723470511

theorem tailTrace_1674519 : CollatzResearch.WordTrace tailWord_1674519 prefixEnd_1674519 286611037362079723470511 := by
  unfold tailWord_1674519
  simp only [CollatzResearch.WordTrace]
  refine ⟨61074725420511122921874611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40716483613674081947916407 61074725420511122921874611)
  ·
    refine ⟨91612088130766684382811917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61074725420511122921874611 91612088130766684382811917)
    ·
      refine ⟨34354533049037506643554469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91612088130766684382811917 34354533049037506643554469)
      ·
        refine ⟨6441474946694532495666463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34354533049037506643554469 6441474946694532495666463)
        ·
          refine ⟨9662212420041798743499695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6441474946694532495666463 9662212420041798743499695)
          ·
            refine ⟨14493318630062698115249543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9662212420041798743499695 14493318630062698115249543)
            ·
              refine ⟨21739977945094047172874315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14493318630062698115249543 21739977945094047172874315)
              ·
                refine ⟨32609966917641070759311473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21739977945094047172874315 32609966917641070759311473)
                ·
                  refine ⟨24457475188230803069483605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32609966917641070759311473 24457475188230803069483605)
                  ·
                    refine ⟨286611037362079723470511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24457475188230803069483605 286611037362079723470511)
                    ·
                      rfl

theorem cell23_1674519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_1674519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674519 prefixEnd_1674519 := by exact prefixLift 1674519
  have htrace : WordTrace (prefixWord ++ tailWord_1674519) baseStart_1674519 baseEnd_1674519 := by
    simpa [prefixWord, tailWord_1674519, baseEnd_1674519] using wordTrace_append hprefix tailTrace_1674519
  have hstable : (prefixWord ++ tailWord_1674519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674519).length < 2 ^ (prefixWord ++ tailWord_1674519).sum := by decide
  have hdescent : baseEnd_1674519 < baseStart_1674519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674529 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1674529 : Nat := 118140960795 + 1674529 * 2 ^ 59
def prefixEnd_1674529 : Nat := 4983230072969 + 3 ^ 40 * 1674529 * 2
def baseEnd_1674529 : Nat := 859838246892784131286487

theorem tailTrace_1674529 : CollatzResearch.WordTrace tailWord_1674529 prefixEnd_1674529 859838246892784131286487 := by
  unfold tailWord_1674529
  simp only [CollatzResearch.WordTrace]
  refine ⟨61075090150474894629738641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40716726766983263086492427 61075090150474894629738641)
  ·
    refine ⟨45806317612856170972303981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61075090150474894629738641 45806317612856170972303981)
    ·
      refine ⟨17177369104821064114613993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45806317612856170972303981 17177369104821064114613993)
      ·
        refine ⟨12883026828615798085960495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17177369104821064114613993 12883026828615798085960495)
        ·
          refine ⟨19324540242923697128940743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12883026828615798085960495 19324540242923697128940743)
          ·
            refine ⟨28986810364385545693411115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19324540242923697128940743 28986810364385545693411115)
            ·
              refine ⟨43480215546578318540116673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28986810364385545693411115 43480215546578318540116673)
              ·
                refine ⟨32610161659933738905087505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43480215546578318540116673 32610161659933738905087505)
                ·
                  refine ⟨24457621244950304178815629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32610161659933738905087505 24457621244950304178815629)
                  ·
                    refine ⟨9171607966856364067055861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24457621244950304178815629 9171607966856364067055861)
                    ·
                      refine ⟨859838246892784131286487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9171607966856364067055861 859838246892784131286487)
                      ·
                        rfl

theorem cell23_1674529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1674529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674529 prefixEnd_1674529 := by exact prefixLift 1674529
  have htrace : WordTrace (prefixWord ++ tailWord_1674529) baseStart_1674529 baseEnd_1674529 := by
    simpa [prefixWord, tailWord_1674529, baseEnd_1674529] using wordTrace_append hprefix tailTrace_1674529
  have hstable : (prefixWord ++ tailWord_1674529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674529).length < 2 ^ (prefixWord ++ tailWord_1674529).sum := by decide
  have hdescent : baseEnd_1674529 < baseStart_1674529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674550 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1674550 : Nat := 118140960795 + 1674550 * 2 ^ 59
def prefixEnd_1674550 : Nat := 4983230072969 + 3 ^ 40 * 1674550 * 2
def baseEnd_1674550 : Nat := 859849029986528549123891

theorem tailTrace_1674550 : CollatzResearch.WordTrace tailWord_1674550 prefixEnd_1674550 859849029986528549123891 := by
  unfold tailWord_1674550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3817241005212425951015819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40717237388932543477502069 3817241005212425951015819)
  ·
    refine ⟨5725861507818638926523729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3817241005212425951015819 5725861507818638926523729)
    ·
      refine ⟨4294396130863979194892797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5725861507818638926523729 4294396130863979194892797)
      ·
        refine ⟨1610398549073992198084799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4294396130863979194892797 1610398549073992198084799)
        ·
          refine ⟨2415597823610988297127199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1610398549073992198084799 2415597823610988297127199)
          ·
            refine ⟨3623396735416482445690799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2415597823610988297127199 3623396735416482445690799)
            ·
              refine ⟨5435095103124723668536199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3623396735416482445690799 5435095103124723668536199)
              ·
                refine ⟨8152642654687085502804299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5435095103124723668536199 8152642654687085502804299)
                ·
                  refine ⟨12228963982030628254206449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8152642654687085502804299 12228963982030628254206449)
                  ·
                    refine ⟨9171722986522971190654837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12228963982030628254206449 9171722986522971190654837)
                    ·
                      refine ⟨859849029986528549123891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9171722986522971190654837 859849029986528549123891)
                      ·
                        rfl

theorem cell23_1674550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1674550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674550 prefixEnd_1674550 := by exact prefixLift 1674550
  have htrace : WordTrace (prefixWord ++ tailWord_1674550) baseStart_1674550 baseEnd_1674550 := by
    simpa [prefixWord, tailWord_1674550, baseEnd_1674550] using wordTrace_append hprefix tailTrace_1674550
  have hstable : (prefixWord ++ tailWord_1674550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674550).length < 2 ^ (prefixWord ++ tailWord_1674550).sum := by decide
  have hdescent : baseEnd_1674550 < baseStart_1674550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674569 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 1, 2, 6]
def baseStart_1674569 : Nat := 118140960795 + 1674569 * 2 ^ 59
def prefixEnd_1674569 : Nat := 4983230072969 + 3 ^ 40 * 1674569 * 2
def baseEnd_1674569 : Nat := 859858786118963974786303

theorem tailTrace_1674569 : CollatzResearch.WordTrace tailWord_1674569 prefixEnd_1674569 859858786118963974786303 := by
  unfold tailWord_1674569
  simp only [CollatzResearch.WordTrace]
  refine ⟨61076549070329981461194761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40717699380219987640796507 61076549070329981461194761)
  ·
    refine ⟨45807411802747486095896071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61076549070329981461194761 45807411802747486095896071)
    ·
      refine ⟨68711117704121229143844107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45807411802747486095896071 68711117704121229143844107)
      ·
        refine ⟨103066676556181843715766161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68711117704121229143844107 103066676556181843715766161)
        ·
          refine ⟨77300007417136382786824621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103066676556181843715766161 77300007417136382786824621)
          ·
            refine ⟨28987502781426143545059233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77300007417136382786824621 28987502781426143545059233)
            ·
              refine ⟨21740627086069607658794425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28987502781426143545059233 21740627086069607658794425)
              ·
                refine ⟨16305470314552205744095819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21740627086069607658794425 16305470314552205744095819)
                ·
                  refine ⟨24458205471828308616143729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16305470314552205744095819 24458205471828308616143729)
                  ·
                    refine ⟨18343654103871231462107797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24458205471828308616143729 18343654103871231462107797)
                    ·
                      refine ⟨859858786118963974786303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18343654103871231462107797 859858786118963974786303)
                      ·
                        rfl

theorem cell23_1674569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_1674569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674569 prefixEnd_1674569 := by exact prefixLift 1674569
  have htrace : WordTrace (prefixWord ++ tailWord_1674569) baseStart_1674569 baseEnd_1674569 := by
    simpa [prefixWord, tailWord_1674569, baseEnd_1674569] using wordTrace_append hprefix tailTrace_1674569
  have hstable : (prefixWord ++ tailWord_1674569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674569).length < 2 ^ (prefixWord ++ tailWord_1674569).sum := by decide
  have hdescent : baseEnd_1674569 < baseStart_1674569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674644 : List Nat := [2, 4, 2, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_1674644 : Nat := 118140960795 + 1674644 * 2 ^ 59
def prefixEnd_1674644 : Nat := 4983230072969 + 3 ^ 40 * 1674644 * 2
def baseEnd_1674644 : Nat := 859897297168051181348459

theorem tailTrace_1674644 : CollatzResearch.WordTrace tailWord_1674644 prefixEnd_1674644 859897297168051181348459 := by
  unfold tailWord_1674644
  simp only [CollatzResearch.WordTrace]
  refine ⟨30539642272529134635087493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40719523030038846180116657 30539642272529134635087493)
  ·
    refine ⟨5726182926099212744078905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30539642272529134635087493 5726182926099212744078905)
    ·
      refine ⟨4294637194574409558059179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5726182926099212744078905 4294637194574409558059179)
      ·
        refine ⟨6441955791861614337088769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4294637194574409558059179 6441955791861614337088769)
        ·
          refine ⟨4831466843896210752816577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6441955791861614337088769 4831466843896210752816577)
          ·
            refine ⟨3623600132922158064612433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4831466843896210752816577 3623600132922158064612433)
            ·
              refine ⟨2717700099691618548459325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3623600132922158064612433 2717700099691618548459325)
              ·
                refine ⟨1019137537384356955672247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2717700099691618548459325 1019137537384356955672247)
                ·
                  refine ⟨1528706306076535433508371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019137537384356955672247 1528706306076535433508371)
                  ·
                    refine ⟨2293059459114803150262557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1528706306076535433508371 2293059459114803150262557)
                    ·
                      refine ⟨859897297168051181348459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2293059459114803150262557 859897297168051181348459)
                      ·
                        rfl

theorem cell23_1674644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_1674644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674644 prefixEnd_1674644 := by exact prefixLift 1674644
  have htrace : WordTrace (prefixWord ++ tailWord_1674644) baseStart_1674644 baseEnd_1674644 := by
    simpa [prefixWord, tailWord_1674644, baseEnd_1674644] using wordTrace_append hprefix tailTrace_1674644
  have hstable : (prefixWord ++ tailWord_1674644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674644).length < 2 ^ (prefixWord ++ tailWord_1674644).sum := by decide
  have hdescent : baseEnd_1674644 < baseStart_1674644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674650 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2]
def baseStart_1674650 : Nat := 118140960795 + 1674650 * 2 ^ 59
def prefixEnd_1674650 : Nat := 4983230072969 + 3 ^ 40 * 1674650 * 2
def baseEnd_1674650 : Nat := 859900378051978157873431

theorem tailTrace_1674650 : CollatzResearch.WordTrace tailWord_1674650 prefixEnd_1674650 859900378051978157873431 := by
  unfold tailWord_1674650
  simp only [CollatzResearch.WordTrace]
  refine ⟨15269875845759133073723351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40719668922024354863262269 15269875845759133073723351)
  ·
    refine ⟨22904813768638699610585027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15269875845759133073723351 22904813768638699610585027)
    ·
      refine ⟨34357220652958049415877541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22904813768638699610585027 34357220652958049415877541)
      ·
        refine ⟨6441978872429634265477039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34357220652958049415877541 6441978872429634265477039)
        ·
          refine ⟨9662968308644451398215559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6441978872429634265477039 9662968308644451398215559)
          ·
            refine ⟨14494452462966677097323339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9662968308644451398215559 14494452462966677097323339)
            ·
              refine ⟨21741678694450015645985009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14494452462966677097323339 21741678694450015645985009)
              ·
                refine ⟨16306259020837511734488757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21741678694450015645985009 16306259020837511734488757)
                ·
                  refine ⟨1528711783203516725108321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16306259020837511734488757 1528711783203516725108321)
                  ·
                    refine ⟨1146533837402637543831241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1528711783203516725108321 1146533837402637543831241)
                    ·
                      refine ⟨859900378051978157873431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1146533837402637543831241 859900378051978157873431)
                      ·
                        rfl

theorem cell23_1674650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_1674650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674650 prefixEnd_1674650 := by exact prefixLift 1674650
  have htrace : WordTrace (prefixWord ++ tailWord_1674650) baseStart_1674650 baseEnd_1674650 := by
    simpa [prefixWord, tailWord_1674650, baseEnd_1674650] using wordTrace_append hprefix tailTrace_1674650
  have hstable : (prefixWord ++ tailWord_1674650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674650).length < 2 ^ (prefixWord ++ tailWord_1674650).sum := by decide
  have hdescent : baseEnd_1674650 < baseStart_1674650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674677 : List Nat := [1, 3, 3, 2, 2, 2, 3, 1, 2, 4]
def baseStart_1674677 : Nat := 118140960795 + 1674677 * 2 ^ 59
def prefixEnd_1674677 : Nat := 4983230072969 + 3 ^ 40 * 1674677 * 2
def baseEnd_1674677 : Nat := 286638080676549850745269

theorem tailTrace_1674677 : CollatzResearch.WordTrace tailWord_1674677 prefixEnd_1674677 286638080676549850745269 := by
  unfold tailWord_1674677
  simp only [CollatzResearch.WordTrace]
  refine ⟨61080488153938715906126285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40720325435959143937417523 61080488153938715906126285)
  ·
    refine ⟨22905183057727018464797357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61080488153938715906126285 22905183057727018464797357)
    ·
      refine ⟨8589443646647631924299009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22905183057727018464797357 8589443646647631924299009)
      ·
        refine ⟨6442082734985723943224257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8589443646647631924299009 6442082734985723943224257)
        ·
          refine ⟨4831562051239292957418193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6442082734985723943224257 4831562051239292957418193)
          ·
            refine ⟨3623671538429469718063645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4831562051239292957418193 3623671538429469718063645)
            ·
              refine ⟨1358876826911051144273867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3623671538429469718063645 1358876826911051144273867)
              ·
                refine ⟨2038315240366576716410801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358876826911051144273867 2038315240366576716410801)
                ·
                  refine ⟨1528736430274932537308101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2038315240366576716410801 1528736430274932537308101)
                  ·
                    refine ⟨286638080676549850745269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1528736430274932537308101 286638080676549850745269)
                    ·
                      rfl

theorem cell23_1674677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_1674677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674677 prefixEnd_1674677 := by exact prefixLift 1674677
  have htrace : WordTrace (prefixWord ++ tailWord_1674677) baseStart_1674677 baseEnd_1674677 := by
    simpa [prefixWord, tailWord_1674677, baseEnd_1674677] using wordTrace_append hprefix tailTrace_1674677
  have hstable : (prefixWord ++ tailWord_1674677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674677).length < 2 ^ (prefixWord ++ tailWord_1674677).sum := by decide
  have hdescent : baseEnd_1674677 < baseStart_1674677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674696 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_1674696 : Nat := 118140960795 + 1674696 * 2 ^ 59
def prefixEnd_1674696 : Nat := 4983230072969 + 3 ^ 40 * 1674696 * 2
def baseEnd_1674696 : Nat := 859923998162084977898219

theorem tailTrace_1674696 : CollatzResearch.WordTrace tailWord_1674696 prefixEnd_1674696 859923998162084977898219 := by
  unfold tailWord_1674696
  simp only [CollatzResearch.WordTrace]
  refine ⟨30540590570434941075533971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40720787427246588100711961 30540590570434941075533971)
  ·
    refine ⟨45810885855652411613300957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30540590570434941075533971 45810885855652411613300957)
    ·
      refine ⟨17179082195869654354987859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45810885855652411613300957 17179082195869654354987859)
      ·
        refine ⟨25768623293804481532481789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17179082195869654354987859 25768623293804481532481789)
        ·
          refine ⟨9663233735176680574680671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25768623293804481532481789 9663233735176680574680671)
          ·
            refine ⟨14494850602765020862021007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9663233735176680574680671 14494850602765020862021007)
            ·
              refine ⟨21742275904147531293031511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14494850602765020862021007 21742275904147531293031511)
              ·
                refine ⟨32613413856221296939547267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21742275904147531293031511 32613413856221296939547267)
                ·
                  refine ⟨48920120784331945409320901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32613413856221296939547267 48920120784331945409320901)
                  ·
                    refine ⟨9172522647062239764247669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48920120784331945409320901 9172522647062239764247669)
                    ·
                      refine ⟨859923998162084977898219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9172522647062239764247669 859923998162084977898219)
                      ·
                        rfl

theorem cell23_1674696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_1674696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674696 prefixEnd_1674696 := by exact prefixLift 1674696
  have htrace : WordTrace (prefixWord ++ tailWord_1674696) baseStart_1674696 baseEnd_1674696 := by
    simpa [prefixWord, tailWord_1674696, baseEnd_1674696] using wordTrace_append hprefix tailTrace_1674696
  have hstable : (prefixWord ++ tailWord_1674696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674696).length < 2 ^ (prefixWord ++ tailWord_1674696).sum := by decide
  have hdescent : baseEnd_1674696 < baseStart_1674696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674700 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 4, 1, 3]
def baseStart_1674700 : Nat := 118140960795 + 1674700 * 2 ^ 59
def prefixEnd_1674700 : Nat := 4983230072969 + 3 ^ 40 * 1674700 * 2
def baseEnd_1674700 : Nat := 859926052084702962248201

theorem tailTrace_1674700 : CollatzResearch.WordTrace tailWord_1674700 prefixEnd_1674700 859926052084702962248201 := by
  unfold tailWord_1674700
  simp only [CollatzResearch.WordTrace]
  refine ⟨30540663516427695417106777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40720884688570260556142369 30540663516427695417106777)
  ·
    refine ⟨22905497637320771562830083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30540663516427695417106777 22905497637320771562830083)
    ·
      refine ⟨34358246455981157344245125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22905497637320771562830083 34358246455981157344245125)
      ·
        refine ⟨6442171210496467002045961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34358246455981157344245125 6442171210496467002045961)
        ·
          refine ⟨4831628407872350251534471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6442171210496467002045961 4831628407872350251534471)
          ·
            refine ⟨7247442611808525377301707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4831628407872350251534471 7247442611808525377301707)
            ·
              refine ⟨10871163917712788065952561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7247442611808525377301707 10871163917712788065952561)
              ·
                refine ⟨8153372938284591049464421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10871163917712788065952561 8153372938284591049464421)
                ·
                  refine ⟨1528757425928360821774579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8153372938284591049464421 1528757425928360821774579)
                  ·
                    refine ⟨2293136138892541232661869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1528757425928360821774579 2293136138892541232661869)
                    ·
                      refine ⟨859926052084702962248201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2293136138892541232661869 859926052084702962248201)
                      ·
                        rfl

theorem cell23_1674700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_1674700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674700 prefixEnd_1674700 := by exact prefixLift 1674700
  have htrace : WordTrace (prefixWord ++ tailWord_1674700) baseStart_1674700 baseEnd_1674700 := by
    simpa [prefixWord, tailWord_1674700, baseEnd_1674700] using wordTrace_append hprefix tailTrace_1674700
  have hstable : (prefixWord ++ tailWord_1674700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674700).length < 2 ^ (prefixWord ++ tailWord_1674700).sum := by decide
  have hdescent : baseEnd_1674700 < baseStart_1674700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674746 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 9]
def baseStart_1674746 : Nat := 118140960795 + 1674746 * 2 ^ 59
def prefixEnd_1674746 : Nat := 4983230072969 + 3 ^ 40 * 1674746 * 2
def baseEnd_1674746 : Nat := 95549963577201086919221

theorem tailTrace_1674746 : CollatzResearch.WordTrace tailWord_1674746 prefixEnd_1674746 95549963577201086919221 := by
  unfold tailWord_1674746
  simp only [CollatzResearch.WordTrace]
  refine ⟨15270751197672185172597023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40722003193792493793592061 15270751197672185172597023)
  ·
    refine ⟨22906126796508277758895535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15270751197672185172597023 22906126796508277758895535)
    ·
      refine ⟨34359190194762416638343303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22906126796508277758895535 34359190194762416638343303)
      ·
        refine ⟨51538785292143624957514955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34359190194762416638343303 51538785292143624957514955)
        ·
          refine ⟨77308177938215437436272433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51538785292143624957514955 77308177938215437436272433)
          ·
            refine ⟨57981133453661578077204325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77308177938215437436272433 57981133453661578077204325)
            ·
              refine ⟨10871462522561545889475811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57981133453661578077204325 10871462522561545889475811)
              ·
                refine ⟨16307193783842318834213717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10871462522561545889475811 16307193783842318834213717)
                ·
                  refine ⟨95549963577201086919221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16307193783842318834213717 95549963577201086919221)
                  ·
                    rfl

theorem cell23_1674746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 9].length) (baseStart_1674746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674746 prefixEnd_1674746 := by exact prefixLift 1674746
  have htrace : WordTrace (prefixWord ++ tailWord_1674746) baseStart_1674746 baseEnd_1674746 := by
    simpa [prefixWord, tailWord_1674746, baseEnd_1674746] using wordTrace_append hprefix tailTrace_1674746
  have hstable : (prefixWord ++ tailWord_1674746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674746).length < 2 ^ (prefixWord ++ tailWord_1674746).sum := by decide
  have hdescent : baseEnd_1674746 < baseStart_1674746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674780 : List Nat := [2, 2, 3, 1, 2, 1, 3, 4, 5]
def baseStart_1674780 : Nat := 118140960795 + 1674780 * 2 ^ 59
def prefixEnd_1674780 : Nat := 4983230072969 + 3 ^ 40 * 1674780 * 2
def baseEnd_1674780 : Nat := 95551903393006961027537

theorem tailTrace_1674780 : CollatzResearch.WordTrace tailWord_1674780 prefixEnd_1674780 95551903393006961027537 := by
  unfold tailWord_1674780
  simp only [CollatzResearch.WordTrace]
  refine ⟨30542122436282782248562897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40722829915043709664750529 30542122436282782248562897)
  ·
    refine ⟨22906591827212086686422173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30542122436282782248562897 22906591827212086686422173)
    ·
      refine ⟨8589971935204532507408315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22906591827212086686422173 8589971935204532507408315)
      ·
        refine ⟨12884957902806798761112473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8589971935204532507408315 12884957902806798761112473)
        ·
          refine ⟨9663718427105099070834355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12884957902806798761112473 9663718427105099070834355)
          ·
            refine ⟨14495577640657648606251533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9663718427105099070834355 14495577640657648606251533)
            ·
              refine ⟨5435841615246618227344325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14495577640657648606251533 5435841615246618227344325)
              ·
                refine ⟨1019220302858740917627061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5435841615246618227344325 1019220302858740917627061)
                ·
                  refine ⟨95551903393006961027537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1019220302858740917627061 95551903393006961027537)
                  ·
                    rfl

theorem cell23_1674780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 5].length) (baseStart_1674780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674780 prefixEnd_1674780 := by exact prefixLift 1674780
  have htrace : WordTrace (prefixWord ++ tailWord_1674780) baseStart_1674780 baseEnd_1674780 := by
    simpa [prefixWord, tailWord_1674780, baseEnd_1674780] using wordTrace_append hprefix tailTrace_1674780
  have hstable : (prefixWord ++ tailWord_1674780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674780).length < 2 ^ (prefixWord ++ tailWord_1674780).sum := by decide
  have hdescent : baseEnd_1674780 < baseStart_1674780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674863 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 3]
def baseStart_1674863 : Nat := 118140960795 + 1674863 * 2 ^ 59
def prefixEnd_1674863 : Nat := 4983230072969 + 3 ^ 40 * 1674863 * 2
def baseEnd_1674863 : Nat := 860009749431385824509951

theorem tailTrace_1674863 : CollatzResearch.WordTrace tailWord_1674863 prefixEnd_1674863 860009749431385824509951 := by
  unfold tailWord_1674863
  simp only [CollatzResearch.WordTrace]
  refine ⟨61087272131264869672397243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40724848087509913114931495 61087272131264869672397243)
  ·
    refine ⟨91630908196897304508595865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61087272131264869672397243 91630908196897304508595865)
    ·
      refine ⟨68723181147672978381446899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91630908196897304508595865 68723181147672978381446899)
      ·
        refine ⟨103084771721509467572170349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68723181147672978381446899 103084771721509467572170349)
        ·
          refine ⟨38656789395566050339563881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103084771721509467572170349 38656789395566050339563881)
          ·
            refine ⟨28992592046674537754672911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38656789395566050339563881 28992592046674537754672911)
            ·
              refine ⟨43488888070011806632009367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28992592046674537754672911 43488888070011806632009367)
              ·
                refine ⟨65233332105017709948014051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43488888070011806632009367 65233332105017709948014051)
                ·
                  refine ⟨97849998157526564922021077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65233332105017709948014051 97849998157526564922021077)
                  ·
                    refine ⟨2293359331817028865359869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 97849998157526564922021077 2293359331817028865359869)
                    ·
                      refine ⟨860009749431385824509951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2293359331817028865359869 860009749431385824509951)
                      ·
                        rfl

theorem cell23_1674863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 3].length) (baseStart_1674863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674863 prefixEnd_1674863 := by exact prefixLift 1674863
  have htrace : WordTrace (prefixWord ++ tailWord_1674863) baseStart_1674863 baseEnd_1674863 := by
    simpa [prefixWord, tailWord_1674863, baseEnd_1674863] using wordTrace_append hprefix tailTrace_1674863
  have hstable : (prefixWord ++ tailWord_1674863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674863).length < 2 ^ (prefixWord ++ tailWord_1674863).sum := by decide
  have hdescent : baseEnd_1674863 < baseStart_1674863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674870 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 8]
def baseStart_1674870 : Nat := 118140960795 + 1674870 * 2 ^ 59
def prefixEnd_1674870 : Nat := 4983230072969 + 3 ^ 40 * 1674870 * 2
def baseEnd_1674870 : Nat := 95557038199551921902491

theorem tailTrace_1674870 : CollatzResearch.WordTrace tailWord_1674870 prefixEnd_1674870 95557038199551921902491 := by
  unfold tailWord_1674870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3817970465139969366743879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40725018294826339911934709 3817970465139969366743879)
  ·
    refine ⟨5726955697709954050115819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3817970465139969366743879 5726955697709954050115819)
    ·
      refine ⟨8590433546564931075173729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5726955697709954050115819 8590433546564931075173729)
      ·
        refine ⟨6442825159923698306380297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8590433546564931075173729 6442825159923698306380297)
        ·
          refine ⟨4832118869942773729785223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6442825159923698306380297 4832118869942773729785223)
          ·
            refine ⟨7248178304914160594677835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4832118869942773729785223 7248178304914160594677835)
            ·
              refine ⟨10872267457371240892016753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7248178304914160594677835 10872267457371240892016753)
              ·
                refine ⟨8154200593028430669012565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10872267457371240892016753 8154200593028430669012565)
                ·
                  refine ⟨95557038199551921902491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8154200593028430669012565 95557038199551921902491)
                  ·
                    rfl

theorem cell23_1674870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_1674870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674870 prefixEnd_1674870 := by exact prefixLift 1674870
  have htrace : WordTrace (prefixWord ++ tailWord_1674870) baseStart_1674870 baseEnd_1674870 := by
    simpa [prefixWord, tailWord_1674870, baseEnd_1674870] using wordTrace_append hprefix tailTrace_1674870
  have hstable : (prefixWord ++ tailWord_1674870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674870).length < 2 ^ (prefixWord ++ tailWord_1674870).sum := by decide
  have hdescent : baseEnd_1674870 < baseStart_1674870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674883 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 5, 5]
def baseStart_1674883 : Nat := 118140960795 + 1674883 * 2 ^ 59
def prefixEnd_1674883 : Nat := 4983230072969 + 3 ^ 40 * 1674883 * 2
def baseEnd_1674883 : Nat := 286673339681491915419953

theorem tailTrace_1674883 : CollatzResearch.WordTrace tailWord_1674883 prefixEnd_1674883 286673339681491915419953 := by
  unfold tailWord_1674883
  simp only [CollatzResearch.WordTrace]
  refine ⟨61088001591192413088125303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40725334394128275392083535 61088001591192413088125303)
  ·
    refine ⟨91632002386788619632187955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61088001591192413088125303 91632002386788619632187955)
    ·
      refine ⟨137448003580182929448281933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91632002386788619632187955 137448003580182929448281933)
      ·
        refine ⟨51543001342568598543105725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137448003580182929448281933 51543001342568598543105725)
        ·
          refine ⟨19328625503463224453664647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51543001342568598543105725 19328625503463224453664647)
          ·
            refine ⟨28992938255194836680496971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19328625503463224453664647 28992938255194836680496971)
            ·
              refine ⟨43489407382792255020745457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28992938255194836680496971 43489407382792255020745457)
              ·
                refine ⟨32617055537094191265559093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43489407382792255020745457 32617055537094191265559093)
                ·
                  refine ⟨3057848956602580431146165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32617055537094191265559093 3057848956602580431146165)
                  ·
                    refine ⟨286673339681491915419953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3057848956602580431146165 286673339681491915419953)
                    ·
                      rfl

theorem cell23_1674883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 5].length) (baseStart_1674883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674883 prefixEnd_1674883 := by exact prefixLift 1674883
  have htrace : WordTrace (prefixWord ++ tailWord_1674883) baseStart_1674883 baseEnd_1674883 := by
    simpa [prefixWord, tailWord_1674883, baseEnd_1674883] using wordTrace_append hprefix tailTrace_1674883
  have hstable : (prefixWord ++ tailWord_1674883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674883).length < 2 ^ (prefixWord ++ tailWord_1674883).sum := by decide
  have hdescent : baseEnd_1674883 < baseStart_1674883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674930 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 6, 4]
def baseStart_1674930 : Nat := 118140960795 + 1674930 * 2 ^ 59
def prefixEnd_1674930 : Nat := 4983230072969 + 3 ^ 40 * 1674930 * 2
def baseEnd_1674930 : Nat := 286681384211745687457381

theorem tailTrace_1674930 : CollatzResearch.WordTrace tailWord_1674930 prefixEnd_1674930 286681384211745687457381 := by
  unfold tailWord_1674930
  simp only [CollatzResearch.WordTrace]
  refine ⟨15272428955505535028771561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40726477214681426743390829 15272428955505535028771561)
  ·
    refine ⟨11454321716629151271578671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15272428955505535028771561 11454321716629151271578671)
    ·
      refine ⟨17181482574943726907368007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11454321716629151271578671 17181482574943726907368007)
      ·
        refine ⟨25772223862415590361052011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17181482574943726907368007 25772223862415590361052011)
        ·
          refine ⟨38658335793623385541578017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25772223862415590361052011 38658335793623385541578017)
          ·
            refine ⟨28993751845217539156183513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38658335793623385541578017 28993751845217539156183513)
            ·
              refine ⟨21745313883913154367137635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28993751845217539156183513 21745313883913154367137635)
              ·
                refine ⟨32617970825869731550706453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21745313883913154367137635 32617970825869731550706453)
                ·
                  refine ⟨1528967382462643666439365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32617970825869731550706453 1528967382462643666439365)
                  ·
                    refine ⟨286681384211745687457381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1528967382462643666439365 286681384211745687457381)
                    ·
                      rfl

theorem cell23_1674930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_1674930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674930 prefixEnd_1674930 := by exact prefixLift 1674930
  have htrace : WordTrace (prefixWord ++ tailWord_1674930) baseStart_1674930 baseEnd_1674930 := by
    simpa [prefixWord, tailWord_1674930, baseEnd_1674930] using wordTrace_append hprefix tailTrace_1674930
  have hstable : (prefixWord ++ tailWord_1674930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674930).length < 2 ^ (prefixWord ++ tailWord_1674930).sum := by decide
  have hdescent : baseEnd_1674930 < baseStart_1674930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674964 : List Nat := [2, 4, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_1674964 : Nat := 118140960795 + 1674964 * 2 ^ 59
def prefixEnd_1674964 : Nat := 4983230072969 + 3 ^ 40 * 1674964 * 2
def baseEnd_1674964 : Nat := 286687203659163309782329

theorem tailTrace_1674964 : CollatzResearch.WordTrace tailWord_1674964 prefixEnd_1674964 286687203659163309782329 := by
  unfold tailWord_1674964
  simp only [CollatzResearch.WordTrace]
  refine ⟨30545477951949481960911973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40727303935932642614549297 30545477951949481960911973)
  ·
    refine ⟨5727277115990527867670995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30545477951949481960911973 5727277115990527867670995)
    ·
      refine ⟨8590915673985791801506493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5727277115990527867670995 8590915673985791801506493)
      ·
        refine ⟨3221593377744671925564935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8590915673985791801506493 3221593377744671925564935)
        ·
          refine ⟨4832390066617007888347403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3221593377744671925564935 4832390066617007888347403)
          ·
            refine ⟨7248585099925511832521105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4832390066617007888347403 7248585099925511832521105)
            ·
              refine ⟨5436438824944133874390829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7248585099925511832521105 5436438824944133874390829)
              ·
                refine ⟨2038664559354050202896561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5436438824944133874390829 2038664559354050202896561)
                ·
                  refine ⟨1528998419515537652172421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2038664559354050202896561 1528998419515537652172421)
                  ·
                    refine ⟨286687203659163309782329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1528998419515537652172421 286687203659163309782329)
                    ·
                      rfl

theorem cell23_1674964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_1674964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674964 prefixEnd_1674964 := by exact prefixLift 1674964
  have htrace : WordTrace (prefixWord ++ tailWord_1674964) baseStart_1674964 baseEnd_1674964 := by
    simpa [prefixWord, tailWord_1674964, baseEnd_1674964] using wordTrace_append hprefix tailTrace_1674964
  have hstable : (prefixWord ++ tailWord_1674964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674964).length < 2 ^ (prefixWord ++ tailWord_1674964).sum := by decide
  have hdescent : baseEnd_1674964 < baseStart_1674964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674977 : List Nat := [1, 2, 3, 1, 5, 1, 3, 7]
def baseStart_1674977 : Nat := 118140960795 + 1674977 * 2 ^ 59
def prefixEnd_1674977 : Nat := 4983230072969 + 3 ^ 40 * 1674977 * 2
def baseEnd_1674977 : Nat := 31854380971333273277201

theorem tailTrace_1674977 : CollatzResearch.WordTrace tailWord_1674977 prefixEnd_1674977 31854380971333273277201 := by
  unfold tailWord_1674977
  simp only [CollatzResearch.WordTrace]
  refine ⟨61091430052851867142047185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40727620035234578094698123 61091430052851867142047185)
  ·
    refine ⟨45818572539638900356535389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61091430052851867142047185 45818572539638900356535389)
    ·
      refine ⟨17181964702364587633700771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45818572539638900356535389 17181964702364587633700771)
      ·
        refine ⟨25772947053546881450551157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17181964702364587633700771 25772947053546881450551157)
        ·
          refine ⟨2416213786270020135989171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25772947053546881450551157 2416213786270020135989171)
          ·
            refine ⟨3624320679405030203983757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416213786270020135989171 3624320679405030203983757)
            ·
              refine ⟨1359120254776886326493909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3624320679405030203983757 1359120254776886326493909)
              ·
                refine ⟨31854380971333273277201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1359120254776886326493909 31854380971333273277201)
                ·
                  rfl

theorem cell23_1674977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 7].length) (baseStart_1674977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1674977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1674977 prefixEnd_1674977 := by exact prefixLift 1674977
  have htrace : WordTrace (prefixWord ++ tailWord_1674977) baseStart_1674977 baseEnd_1674977 := by
    simpa [prefixWord, tailWord_1674977, baseEnd_1674977] using wordTrace_append hprefix tailTrace_1674977
  have hstable : (prefixWord ++ tailWord_1674977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674977).length < 2 ^ (prefixWord ++ tailWord_1674977).sum := by decide
  have hdescent : baseEnd_1674977 < baseStart_1674977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675020 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 2, 6]
def baseStart_1675020 : Nat := 118140960795 + 1675020 * 2 ^ 59
def prefixEnd_1675020 : Nat := 4983230072969 + 3 ^ 40 * 1675020 * 2
def baseEnd_1675020 : Nat := 286696788631380570082243

theorem tailTrace_1675020 : CollatzResearch.WordTrace tailWord_1675020 prefixEnd_1675020 286696788631380570082243 := by
  unfold tailWord_1675020
  simp only [CollatzResearch.WordTrace]
  refine ⟨30546499195848042742931257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40728665594464056990575009 30546499195848042742931257)
  ·
    refine ⟨22909874396886032057198443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30546499195848042742931257 22909874396886032057198443)
    ·
      refine ⟨34364811595329048085797665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22909874396886032057198443 34364811595329048085797665)
      ·
        refine ⟨25773608696496786064348249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34364811595329048085797665 25773608696496786064348249)
        ·
          refine ⟨19330206522372589548261187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25773608696496786064348249 19330206522372589548261187)
          ·
            refine ⟨28995309783558884322391781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19330206522372589548261187 28995309783558884322391781)
            ·
              refine ⟨5436620584417290810448459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28995309783558884322391781 5436620584417290810448459)
              ·
                refine ⟨8154930876625936215672689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5436620584417290810448459 8154930876625936215672689)
                ·
                  refine ⟨6116198157469452161754517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8154930876625936215672689 6116198157469452161754517)
                  ·
                    refine ⟨286696788631380570082243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6116198157469452161754517 286696788631380570082243)
                    ·
                      rfl

theorem cell23_1675020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_1675020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675020 prefixEnd_1675020 := by exact prefixLift 1675020
  have htrace : WordTrace (prefixWord ++ tailWord_1675020) baseStart_1675020 baseEnd_1675020 := by
    simpa [prefixWord, tailWord_1675020, baseEnd_1675020] using wordTrace_append hprefix tailTrace_1675020
  have hstable : (prefixWord ++ tailWord_1675020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675020).length < 2 ^ (prefixWord ++ tailWord_1675020).sum := by decide
  have hdescent : baseEnd_1675020 < baseStart_1675020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675027 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 1, 4, 2]
def baseStart_1675027 : Nat := 118140960795 + 1675027 * 2 ^ 59
def prefixEnd_1675027 : Nat := 4983230072969 + 3 ^ 40 * 1675027 * 2
def baseEnd_1675027 : Nat := 860093960258723182859197

theorem tailTrace_1675027 : CollatzResearch.WordTrace tailWord_1675027 prefixEnd_1675027 860093960258723182859197 := by
  unfold tailWord_1675027
  simp only [CollatzResearch.WordTrace]
  refine ⟨61093253702670725681367335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40728835801780483787578223 61093253702670725681367335)
  ·
    refine ⟨91639880554006088522051003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61093253702670725681367335 91639880554006088522051003)
    ·
      refine ⟨137459820831009132783076505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91639880554006088522051003 137459820831009132783076505)
      ·
        refine ⟨103094865623256849587307379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137459820831009132783076505 103094865623256849587307379)
        ·
          refine ⟨154642298434885274380961069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103094865623256849587307379 154642298434885274380961069)
          ·
            refine ⟨57990861913081977892860401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154642298434885274380961069 57990861913081977892860401)
            ·
              refine ⟨43493146434811483419645301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57990861913081977892860401 43493146434811483419645301)
              ·
                refine ⟨4077482478263576570591747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43493146434811483419645301 4077482478263576570591747)
                ·
                  refine ⟨6116223717395364855887621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4077482478263576570591747 6116223717395364855887621)
                  ·
                    refine ⟨1146791947011630910478929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6116223717395364855887621 1146791947011630910478929)
                    ·
                      refine ⟨860093960258723182859197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1146791947011630910478929 860093960258723182859197)
                      ·
                        rfl

theorem cell23_1675027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 4, 2].length) (baseStart_1675027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675027 prefixEnd_1675027 := by exact prefixLift 1675027
  have htrace : WordTrace (prefixWord ++ tailWord_1675027) baseStart_1675027 baseEnd_1675027 := by
    simpa [prefixWord, tailWord_1675027, baseEnd_1675027] using wordTrace_append hprefix tailTrace_1675027
  have hstable : (prefixWord ++ tailWord_1675027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675027).length < 2 ^ (prefixWord ++ tailWord_1675027).sum := by decide
  have hdescent : baseEnd_1675027 < baseStart_1675027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675028 : List Nat := [2, 4, 4, 1, 1, 2, 2, 7]
def baseStart_1675028 : Nat := 118140960795 + 1675028 * 2 ^ 59
def prefixEnd_1675028 : Nat := 4983230072969 + 3 ^ 40 * 1675028 * 2
def baseEnd_1675028 : Nat := 31855350879236210331359

theorem tailTrace_1675028 : CollatzResearch.WordTrace tailWord_1675028 prefixEnd_1675028 31855350879236210331359 := by
  unfold tailWord_1675028
  simp only [CollatzResearch.WordTrace]
  refine ⟨30546645087833551426076869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40728860117111401901435825 30546645087833551426076869)
  ·
    refine ⟨5727495953968790892389413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30546645087833551426076869 5727495953968790892389413)
    ·
      refine ⟨1073905491369148292323015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5727495953968790892389413 1073905491369148292323015)
      ·
        refine ⟨1610858237053722438484523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1073905491369148292323015 1610858237053722438484523)
        ·
          refine ⟨2416287355580583657726785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1610858237053722438484523 2416287355580583657726785)
          ·
            refine ⟨1812215516685437743295089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2416287355580583657726785 1812215516685437743295089)
            ·
              refine ⟨1359161637514078307471317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1812215516685437743295089 1359161637514078307471317)
              ·
                refine ⟨31855350879236210331359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1359161637514078307471317 31855350879236210331359)
                ·
                  rfl

theorem cell23_1675028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 7].length) (baseStart_1675028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675028 prefixEnd_1675028 := by exact prefixLift 1675028
  have htrace : WordTrace (prefixWord ++ tailWord_1675028) baseStart_1675028 baseEnd_1675028 := by
    simpa [prefixWord, tailWord_1675028, baseEnd_1675028] using wordTrace_append hprefix tailTrace_1675028
  have hstable : (prefixWord ++ tailWord_1675028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675028).length < 2 ^ (prefixWord ++ tailWord_1675028).sum := by decide
  have hdescent : baseEnd_1675028 < baseStart_1675028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675031 : List Nat := [1, 1, 3, 4, 2, 2, 2, 2, 1, 3, 2]
def baseStart_1675031 : Nat := 118140960795 + 1675031 * 2 ^ 59
def prefixEnd_1675031 : Nat := 4983230072969 + 3 ^ 40 * 1675031 * 2
def baseEnd_1675031 : Nat := 860096014181341167209179

theorem tailTrace_1675031 : CollatzResearch.WordTrace tailWord_1675031 prefixEnd_1675031 860096014181341167209179 := by
  unfold tailWord_1675031
  simp only [CollatzResearch.WordTrace]
  refine ⟨61093399594656234364512947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40728933063104156243008631 61093399594656234364512947)
  ·
    refine ⟨91640099391984351546769421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61093399594656234364512947 91640099391984351546769421)
    ·
      refine ⟨34365037271994131830038533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91640099391984351546769421 34365037271994131830038533)
      ·
        refine ⟨6443444488498899718132225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34365037271994131830038533 6443444488498899718132225)
        ·
          refine ⟨4832583366374174788599169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6443444488498899718132225 4832583366374174788599169)
          ·
            refine ⟨3624437524780631091449377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4832583366374174788599169 3624437524780631091449377)
            ·
              refine ⟨2718328143585473318587033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3624437524780631091449377 2718328143585473318587033)
              ·
                refine ⟨2038746107689104988940275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2718328143585473318587033 2038746107689104988940275)
                ·
                  refine ⟨3058119161533657483410413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2038746107689104988940275 3058119161533657483410413)
                  ·
                    refine ⟨1146794685575121556278905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3058119161533657483410413 1146794685575121556278905)
                    ·
                      refine ⟨860096014181341167209179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1146794685575121556278905 860096014181341167209179)
                      ·
                        rfl

theorem cell23_1675031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_1675031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675031 prefixEnd_1675031 := by exact prefixLift 1675031
  have htrace : WordTrace (prefixWord ++ tailWord_1675031) baseStart_1675031 baseEnd_1675031 := by
    simpa [prefixWord, tailWord_1675031, baseEnd_1675031] using wordTrace_append hprefix tailTrace_1675031
  have hstable : (prefixWord ++ tailWord_1675031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675031).length < 2 ^ (prefixWord ++ tailWord_1675031).sum := by decide
  have hdescent : baseEnd_1675031 < baseStart_1675031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675097 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 2, 5]
def baseStart_1675097 : Nat := 118140960795 + 1675097 * 2 ^ 59
def prefixEnd_1675097 : Nat := 4983230072969 + 3 ^ 40 * 1675097 * 2
def baseEnd_1675097 : Nat := 286709967968179302994625

theorem tailTrace_1675097 : CollatzResearch.WordTrace tailWord_1675097 prefixEnd_1675097 286709967968179302994625 := by
  unfold tailWord_1675097
  simp only [CollatzResearch.WordTrace]
  refine ⟨61095806812417127636415545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40730537874944751757610363 61095806812417127636415545)
  ·
    refine ⟨45821855109312845727311659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61095806812417127636415545 45821855109312845727311659)
    ·
      refine ⟨68732782663969268590967489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45821855109312845727311659 68732782663969268590967489)
      ·
        refine ⟨51549586997976951443225617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68732782663969268590967489 51549586997976951443225617)
        ·
          refine ⟨38662190248482713582419213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51549586997976951443225617 38662190248482713582419213)
          ·
            refine ⟨14498321343181017593407205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38662190248482713582419213 14498321343181017593407205)
            ·
              refine ⟨2718435251846440798763851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14498321343181017593407205 2718435251846440798763851)
              ·
                refine ⟨4077652877769661198145777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2718435251846440798763851 4077652877769661198145777)
                ·
                  refine ⟨3058239658327245898609333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4077652877769661198145777 3058239658327245898609333)
                  ·
                    refine ⟨286709967968179302994625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3058239658327245898609333 286709967968179302994625)
                    ·
                      rfl

theorem cell23_1675097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 5].length) (baseStart_1675097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675097 prefixEnd_1675097 := by exact prefixLift 1675097
  have htrace : WordTrace (prefixWord ++ tailWord_1675097) baseStart_1675097 baseEnd_1675097 := by
    simpa [prefixWord, tailWord_1675097, baseEnd_1675097] using wordTrace_append hprefix tailTrace_1675097
  have hstable : (prefixWord ++ tailWord_1675097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675097).length < 2 ^ (prefixWord ++ tailWord_1675097).sum := by decide
  have hdescent : baseEnd_1675097 < baseStart_1675097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675118 : List Nat := [4, 1, 2, 3, 1, 3, 2, 2, 5]
def baseStart_1675118 : Nat := 118140960795 + 1675118 * 2 ^ 59
def prefixEnd_1675118 : Nat := 4983230072969 + 3 ^ 40 * 1675118 * 2
def baseEnd_1675118 : Nat := 95571187444253591869031

theorem tailTrace_1675118 : CollatzResearch.WordTrace tailWord_1675118 prefixEnd_1675118 95571187444253591869031 := by
  unfold tailWord_1675118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7637071593167631027866251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40731048496894032148620005 7637071593167631027866251)
  ·
    refine ⟨11455607389751446541799377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7637071593167631027866251 11455607389751446541799377)
    ·
      refine ⟨8591705542313584906349533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11455607389751446541799377 8591705542313584906349533)
      ·
        refine ⟨3221889578367594339881075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8591705542313584906349533 3221889578367594339881075)
        ·
          refine ⟨4832834367551391509821613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3221889578367594339881075 4832834367551391509821613)
          ·
            refine ⟨1812312887831771816183105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4832834367551391509821613 1812312887831771816183105)
            ·
              refine ⟨1359234665873828862137329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1812312887831771816183105 1359234665873828862137329)
              ·
                refine ⟨1019425999405371646602997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1359234665873828862137329 1019425999405371646602997)
                ·
                  refine ⟨95571187444253591869031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1019425999405371646602997 95571187444253591869031)
                  ·
                    rfl

theorem cell23_1675118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_1675118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675118 prefixEnd_1675118 := by exact prefixLift 1675118
  have htrace : WordTrace (prefixWord ++ tailWord_1675118) baseStart_1675118 baseEnd_1675118 := by
    simpa [prefixWord, tailWord_1675118, baseEnd_1675118] using wordTrace_append hprefix tailTrace_1675118
  have hstable : (prefixWord ++ tailWord_1675118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675118).length < 2 ^ (prefixWord ++ tailWord_1675118).sum := by decide
  have hdescent : baseEnd_1675118 < baseStart_1675118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675120 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 5]
def baseStart_1675120 : Nat := 118140960795 + 1675120 * 2 ^ 59
def prefixEnd_1675120 : Nat := 4983230072969 + 3 ^ 40 * 1675120 * 2
def baseEnd_1675120 : Nat := 860141713959591318996269

theorem tailTrace_1675120 : CollatzResearch.WordTrace tailWord_1675120 prefixEnd_1675120 860141713959591318996269 := by
  unfold tailWord_1675120
  simp only [CollatzResearch.WordTrace]
  refine ⟨30548322845666901282251407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40731097127555868376335209 30548322845666901282251407)
  ·
    refine ⟨45822484268500351923377111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30548322845666901282251407 45822484268500351923377111)
    ·
      refine ⟨68733726402750527885065667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45822484268500351923377111 68733726402750527885065667)
      ·
        refine ⟨103100589604125791827598501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68733726402750527885065667 103100589604125791827598501)
        ·
          refine ⟨19331360550773585967674719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103100589604125791827598501 19331360550773585967674719)
          ·
            refine ⟨28997040826160378951512079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19331360550773585967674719 28997040826160378951512079)
            ·
              refine ⟨43495561239240568427268119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28997040826160378951512079 43495561239240568427268119)
              ·
                refine ⟨65243341858860852640902179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43495561239240568427268119 65243341858860852640902179)
                ·
                  refine ⟨97865012788291278961353269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65243341858860852640902179 97865012788291278961353269)
                  ·
                    refine ⟨9174844948902307402626869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97865012788291278961353269 9174844948902307402626869)
                    ·
                      refine ⟨860141713959591318996269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9174844948902307402626869 860141713959591318996269)
                      ·
                        rfl

theorem cell23_1675120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_1675120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675120 prefixEnd_1675120 := by exact prefixLift 1675120
  have htrace : WordTrace (prefixWord ++ tailWord_1675120) baseStart_1675120 baseEnd_1675120 := by
    simpa [prefixWord, tailWord_1675120, baseEnd_1675120] using wordTrace_append hprefix tailTrace_1675120
  have hstable : (prefixWord ++ tailWord_1675120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675120).length < 2 ^ (prefixWord ++ tailWord_1675120).sum := by decide
  have hdescent : baseEnd_1675120 < baseStart_1675120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675194 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2]
def baseStart_1675194 : Nat := 118140960795 + 1675194 * 2 ^ 59
def prefixEnd_1675194 : Nat := 4983230072969 + 3 ^ 40 * 1675194 * 2
def baseEnd_1675194 : Nat := 860179711528024029470929

theorem tailTrace_1675194 : CollatzResearch.WordTrace tailWord_1675194 prefixEnd_1675194 860179711528024029470929 := by
  unfold tailWord_1675194
  simp only [CollatzResearch.WordTrace]
  refine ⟨15274836173266428300674159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40732896462043808801797757 15274836173266428300674159)
  ·
    refine ⟨22912254259899642451011239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15274836173266428300674159 22912254259899642451011239)
    ·
      refine ⟨34368381389849463676516859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22912254259899642451011239 34368381389849463676516859)
      ·
        refine ⟨51552572084774195514775289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34368381389849463676516859 51552572084774195514775289)
        ·
          refine ⟨38664429063580646636081467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51552572084774195514775289 38664429063580646636081467)
          ·
            refine ⟨57996643595370969954122201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38664429063580646636081467 57996643595370969954122201)
            ·
              refine ⟨43497482696528227465591651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57996643595370969954122201 43497482696528227465591651)
              ·
                refine ⟨65246224044792341198387477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43497482696528227465591651 65246224044792341198387477)
                ·
                  refine ⟨3058416752099640993674413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65246224044792341198387477 3058416752099640993674413)
                  ·
                    refine ⟨1146906282037365372627905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3058416752099640993674413 1146906282037365372627905)
                    ·
                      refine ⟨860179711528024029470929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1146906282037365372627905 860179711528024029470929)
                      ·
                        rfl

theorem cell23_1675194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2].length) (baseStart_1675194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675194 prefixEnd_1675194 := by exact prefixLift 1675194
  have htrace : WordTrace (prefixWord ++ tailWord_1675194) baseStart_1675194 baseEnd_1675194 := by
    simpa [prefixWord, tailWord_1675194, baseEnd_1675194] using wordTrace_append hprefix tailTrace_1675194
  have hstable : (prefixWord ++ tailWord_1675194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675194).length < 2 ^ (prefixWord ++ tailWord_1675194).sum := by decide
  have hdescent : baseEnd_1675194 < baseStart_1675194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675224 : List Nat := [2, 1, 2, 2, 2, 2, 1, 5, 1, 1, 4]
def baseStart_1675224 : Nat := 118140960795 + 1675224 * 2 ^ 59
def prefixEnd_1675224 : Nat := 4983230072969 + 3 ^ 40 * 1675224 * 2
def baseEnd_1675224 : Nat := 860195115947658912095791

theorem tailTrace_1675224 : CollatzResearch.WordTrace tailWord_1675224 prefixEnd_1675224 860195115947658912095791 := by
  unfold tailWord_1675224
  simp only [CollatzResearch.WordTrace]
  refine ⟨30550219441478514163144363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40733625921971352217525817 30550219441478514163144363)
  ·
    refine ⟨45825329162217771244716545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30550219441478514163144363 45825329162217771244716545)
    ·
      refine ⟨34368996871663328433537409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45825329162217771244716545 34368996871663328433537409)
      ·
        refine ⟨25776747653747496325153057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34368996871663328433537409 25776747653747496325153057)
        ·
          refine ⟨19332560740310622243864793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25776747653747496325153057 19332560740310622243864793)
          ·
            refine ⟨14499420555232966682898595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19332560740310622243864793 14499420555232966682898595)
            ·
              refine ⟨21749130832849450024347893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14499420555232966682898595 21749130832849450024347893)
              ·
                refine ⟨2038981015579635939782615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21749130832849450024347893 2038981015579635939782615)
                ·
                  refine ⟨3058471523369453909673923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2038981015579635939782615 3058471523369453909673923)
                  ·
                    refine ⟨4587707285054180864510885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3058471523369453909673923 4587707285054180864510885)
                    ·
                      refine ⟨860195115947658912095791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4587707285054180864510885 860195115947658912095791)
                      ·
                        rfl

theorem cell23_1675224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_1675224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675224 prefixEnd_1675224 := by exact prefixLift 1675224
  have htrace : WordTrace (prefixWord ++ tailWord_1675224) baseStart_1675224 baseEnd_1675224 := by
    simpa [prefixWord, tailWord_1675224, baseEnd_1675224] using wordTrace_append hprefix tailTrace_1675224
  have hstable : (prefixWord ++ tailWord_1675224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675224).length < 2 ^ (prefixWord ++ tailWord_1675224).sum := by decide
  have hdescent : baseEnd_1675224 < baseStart_1675224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675235 : List Nat := [1, 1, 1, 6, 1, 3, 3, 2, 1, 1, 3]
def baseStart_1675235 : Nat := 118140960795 + 1675235 * 2 ^ 59
def prefixEnd_1675235 : Nat := 4983230072969 + 3 ^ 40 * 1675235 * 2
def baseEnd_1675235 : Nat := 860200764234858369058241

theorem tailTrace_1675235 : CollatzResearch.WordTrace tailWord_1675235 prefixEnd_1675235 860200764234858369058241 := by
  unfold tailWord_1675235
  simp only [CollatzResearch.WordTrace]
  refine ⟨61100840085917177204939159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40733893390611451469959439 61100840085917177204939159)
  ·
    refine ⟨91651260128875765807408739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61100840085917177204939159 91651260128875765807408739)
    ·
      refine ⟨137476890193313648711113109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91651260128875765807408739 137476890193313648711113109)
      ·
        refine ⟨6444229227811577283333427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 137476890193313648711113109 6444229227811577283333427)
        ·
          refine ⟨9666343841717365925000141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6444229227811577283333427 9666343841717365925000141)
          ·
            refine ⟨3624878940644012221875053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9666343841717365925000141 3624878940644012221875053)
            ·
              refine ⟨1359329602741504583203145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3624878940644012221875053 1359329602741504583203145)
              ·
                refine ⟨1019497202056128437402359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1359329602741504583203145 1019497202056128437402359)
                ·
                  refine ⟨1529245803084192656103539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019497202056128437402359 1529245803084192656103539)
                  ·
                    refine ⟨2293868704626288984155309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1529245803084192656103539 2293868704626288984155309)
                    ·
                      refine ⟨860200764234858369058241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2293868704626288984155309 860200764234858369058241)
                      ·
                        rfl

theorem cell23_1675235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_1675235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675235 prefixEnd_1675235 := by exact prefixLift 1675235
  have htrace : WordTrace (prefixWord ++ tailWord_1675235) baseStart_1675235 baseEnd_1675235 := by
    simpa [prefixWord, tailWord_1675235, baseEnd_1675235] using wordTrace_append hprefix tailTrace_1675235
  have hstable : (prefixWord ++ tailWord_1675235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675235).length < 2 ^ (prefixWord ++ tailWord_1675235).sum := by decide
  have hdescent : baseEnd_1675235 < baseStart_1675235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675247 : List Nat := [1, 1, 2, 1, 4, 2, 4, 8]
def baseStart_1675247 : Nat := 118140960795 + 1675247 * 2 ^ 59
def prefixEnd_1675247 : Nat := 4983230072969 + 3 ^ 40 * 1675247 * 2
def baseEnd_1675247 : Nat := 31859515777878234152155

theorem tailTrace_1675247 : CollatzResearch.WordTrace tailWord_1675247 prefixEnd_1675247 31859515777878234152155 := by
  unfold tailWord_1675247
  simp only [CollatzResearch.WordTrace]
  refine ⟨61101277761873703254375995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40734185174582468836250663 61101277761873703254375995)
  ·
    refine ⟨91651916642810554881563993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61101277761873703254375995 91651916642810554881563993)
    ·
      refine ⟨68738937482107916161172995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91651916642810554881563993 68738937482107916161172995)
      ·
        refine ⟨103108406223161874241759493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68738937482107916161172995 103108406223161874241759493)
        ·
          refine ⟨19332826166842851420329905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103108406223161874241759493 19332826166842851420329905)
          ·
            refine ⟨14499619625132138565247429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19332826166842851420329905 14499619625132138565247429)
            ·
              refine ⟨2718678679712275980983893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14499619625132138565247429 2718678679712275980983893)
              ·
                refine ⟨31859515777878234152155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2718678679712275980983893 31859515777878234152155)
                ·
                  rfl

theorem cell23_1675247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 8].length) (baseStart_1675247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675247 prefixEnd_1675247 := by exact prefixLift 1675247
  have htrace : WordTrace (prefixWord ++ tailWord_1675247) baseStart_1675247 baseEnd_1675247 := by
    simpa [prefixWord, tailWord_1675247, baseEnd_1675247] using wordTrace_append hprefix tailTrace_1675247
  have hstable : (prefixWord ++ tailWord_1675247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675247).length < 2 ^ (prefixWord ++ tailWord_1675247).sum := by decide
  have hdescent : baseEnd_1675247 < baseStart_1675247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675261 : List Nat := [1, 4, 1, 1, 1, 2, 5, 2, 1, 2, 3]
def baseStart_1675261 : Nat := 118140960795 + 1675261 * 2 ^ 59
def prefixEnd_1675261 : Nat := 4983230072969 + 3 ^ 40 * 1675261 * 2
def baseEnd_1675261 : Nat := 860214114731875267333121

theorem tailTrace_1675261 : CollatzResearch.WordTrace tailWord_1675261 prefixEnd_1675261 860214114731875267333121 := by
  unfold tailWord_1675261
  simp only [CollatzResearch.WordTrace]
  refine ⟨61101788383822983645385637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40734525589215322430257091 61101788383822983645385637)
  ·
    refine ⟨11456585321966809433509807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61101788383822983645385637 11456585321966809433509807)
    ·
      refine ⟨17184877982950214150264711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11456585321966809433509807 17184877982950214150264711)
      ·
        refine ⟨25777316974425321225397067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17184877982950214150264711 25777316974425321225397067)
        ·
          refine ⟨38665975461637981838095601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25777316974425321225397067 38665975461637981838095601)
          ·
            refine ⟨28999481596228486378571701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38665975461637981838095601 28999481596228486378571701)
            ·
              refine ⟨2718701399646420597991097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28999481596228486378571701 2718701399646420597991097)
              ·
                refine ⟨2039026049734815448493323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2718701399646420597991097 2039026049734815448493323)
                ·
                  refine ⟨3058539074602223172739985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039026049734815448493323 3058539074602223172739985)
                  ·
                    refine ⟨2293904305951667379554989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3058539074602223172739985 2293904305951667379554989)
                    ·
                      refine ⟨860214114731875267333121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2293904305951667379554989 860214114731875267333121)
                      ·
                        rfl

theorem cell23_1675261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_1675261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675261 prefixEnd_1675261 := by exact prefixLift 1675261
  have htrace : WordTrace (prefixWord ++ tailWord_1675261) baseStart_1675261 baseEnd_1675261 := by
    simpa [prefixWord, tailWord_1675261, baseEnd_1675261] using wordTrace_append hprefix tailTrace_1675261
  have hstable : (prefixWord ++ tailWord_1675261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675261).length < 2 ^ (prefixWord ++ tailWord_1675261).sum := by decide
  have hdescent : baseEnd_1675261 < baseStart_1675261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675278 : List Nat := [4, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3]
def baseStart_1675278 : Nat := 118140960795 + 1675278 * 2 ^ 59
def prefixEnd_1675278 : Nat := 4983230072969 + 3 ^ 40 * 1675278 * 2
def baseEnd_1675278 : Nat := 860222843903001700820543

theorem tailTrace_1675278 : CollatzResearch.WordTrace tailWord_1675278 prefixEnd_1675278 860222843903001700820543 := by
  unfold tailWord_1675278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7637801053095174443594311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40734938949840930365836325 7637801053095174443594311)
  ·
    refine ⟨11456701579642761665391467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7637801053095174443594311 11456701579642761665391467)
    ·
      refine ⟨17185052369464142498087201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11456701579642761665391467 17185052369464142498087201)
      ·
        refine ⟨12888789277098106873565401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17185052369464142498087201 12888789277098106873565401)
        ·
          refine ⟨9666591957823580155174051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12888789277098106873565401 9666591957823580155174051)
          ·
            refine ⟨14499887936735370232761077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9666591957823580155174051 14499887936735370232761077)
            ·
              refine ⟨1359364494068940959321351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14499887936735370232761077 1359364494068940959321351)
              ·
                refine ⟨2039046741103411438982027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359364494068940959321351 2039046741103411438982027)
                ·
                  refine ⟨3058570111655117158473041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039046741103411438982027 3058570111655117158473041)
                  ·
                    refine ⟨2293927583741337868854781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3058570111655117158473041 2293927583741337868854781)
                    ·
                      refine ⟨860222843903001700820543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2293927583741337868854781 860222843903001700820543)
                      ·
                        rfl

theorem cell23_1675278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_1675278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675278 prefixEnd_1675278 := by exact prefixLift 1675278
  have htrace : WordTrace (prefixWord ++ tailWord_1675278) baseStart_1675278 baseEnd_1675278 := by
    simpa [prefixWord, tailWord_1675278, baseEnd_1675278] using wordTrace_append hprefix tailTrace_1675278
  have hstable : (prefixWord ++ tailWord_1675278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675278).length < 2 ^ (prefixWord ++ tailWord_1675278).sum := by decide
  have hdescent : baseEnd_1675278 < baseStart_1675278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675292 : List Nat := [2, 2, 3, 1, 3, 1, 4, 2, 1, 2, 2]
def baseStart_1675292 : Nat := 118140960795 + 1675292 * 2 ^ 59
def prefixEnd_1675292 : Nat := 4983230072969 + 3 ^ 40 * 1675292 * 2
def baseEnd_1675292 : Nat := 860230032632164646045479

theorem tailTrace_1675292 : CollatzResearch.WordTrace tailWord_1675292 prefixEnd_1675292 860230032632164646045479 := by
  unfold tailWord_1675292
  simp only [CollatzResearch.WordTrace]
  refine ⟨30551459523355337969882065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40735279364473783959842753 30551459523355337969882065)
  ·
    refine ⟨22913594642516503477411549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30551459523355337969882065 22913594642516503477411549)
    ·
      refine ⟨8592597990943688804029331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22913594642516503477411549 8592597990943688804029331)
      ·
        refine ⟨12888896986415533206043997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8592597990943688804029331 12888896986415533206043997)
        ·
          refine ⟨4833336369905824952266499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12888896986415533206043997 4833336369905824952266499)
          ·
            refine ⟨7250004554858737428399749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4833336369905824952266499 7250004554858737428399749)
            ·
              refine ⟨1359375854036013267824953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7250004554858737428399749 1359375854036013267824953)
              ·
                refine ⟨1019531890527009950868715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1359375854036013267824953 1019531890527009950868715)
                ·
                  refine ⟨1529297835790514926303073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019531890527009950868715 1529297835790514926303073)
                  ·
                    refine ⟨1146973376842886194727305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1529297835790514926303073 1146973376842886194727305)
                    ·
                      refine ⟨860230032632164646045479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1146973376842886194727305 860230032632164646045479)
                      ·
                        rfl

theorem cell23_1675292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_1675292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675292 prefixEnd_1675292 := by exact prefixLift 1675292
  have htrace : WordTrace (prefixWord ++ tailWord_1675292) baseStart_1675292 baseEnd_1675292 := by
    simpa [prefixWord, tailWord_1675292, baseEnd_1675292] using wordTrace_append hprefix tailTrace_1675292
  have hstable : (prefixWord ++ tailWord_1675292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675292).length < 2 ^ (prefixWord ++ tailWord_1675292).sum := by decide
  have hdescent : baseEnd_1675292 < baseStart_1675292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675301 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 3, 3, 2]
def baseStart_1675301 : Nat := 118140960795 + 1675301 * 2 ^ 59
def prefixEnd_1675301 : Nat := 4983230072969 + 3 ^ 40 * 1675301 * 2
def baseEnd_1675301 : Nat := 860234653958055110832937

theorem tailTrace_1675301 : CollatzResearch.WordTrace tailWord_1675301 prefixEnd_1675301 860234653958055110832937 := by
  unfold tailWord_1675301
  simp only [CollatzResearch.WordTrace]
  refine ⟨61103247303678070476841757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40735498202452046984561171 61103247303678070476841757)
  ·
    refine ⟨22913717738879276428815659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61103247303678070476841757 22913717738879276428815659)
    ·
      refine ⟨34370576608318914643223489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22913717738879276428815659 34370576608318914643223489)
      ·
        refine ⟨25777932456239185982417617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34370576608318914643223489 25777932456239185982417617)
        ·
          refine ⟨19333449342179389486813213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25777932456239185982417617 19333449342179389486813213)
          ·
            refine ⟨7250043503317271057554955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19333449342179389486813213 7250043503317271057554955)
            ·
              refine ⟨10875065254975906586332433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7250043503317271057554955 10875065254975906586332433)
              ·
                refine ⟨8156298941231929939749325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10875065254975906586332433 8156298941231929939749325)
                ·
                  refine ⟨3058612102961973727405997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8156298941231929939749325 3058612102961973727405997)
                  ·
                    refine ⟨1146979538610740147777249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3058612102961973727405997 1146979538610740147777249)
                    ·
                      refine ⟨860234653958055110832937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1146979538610740147777249 860234653958055110832937)
                      ·
                        rfl

theorem cell23_1675301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_1675301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675301 prefixEnd_1675301 := by exact prefixLift 1675301
  have htrace : WordTrace (prefixWord ++ tailWord_1675301) baseStart_1675301 baseEnd_1675301 := by
    simpa [prefixWord, tailWord_1675301, baseEnd_1675301] using wordTrace_append hprefix tailTrace_1675301
  have hstable : (prefixWord ++ tailWord_1675301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675301).length < 2 ^ (prefixWord ++ tailWord_1675301).sum := by decide
  have hdescent : baseEnd_1675301 < baseStart_1675301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675318 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_1675318 : Nat := 118140960795 + 1675318 * 2 ^ 59
def prefixEnd_1675318 : Nat := 4983230072969 + 3 ^ 40 * 1675318 * 2
def baseEnd_1675318 : Nat := 860243383129181544320359

theorem tailTrace_1675318 : CollatzResearch.WordTrace tailWord_1675318 prefixEnd_1675318 860243383129181544320359 := by
  unfold tailWord_1675318
  simp only [CollatzResearch.WordTrace]
  refine ⟨3818991709038530148763163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40735911563077654920140405 3818991709038530148763163)
  ·
    refine ⟨5728487563557795223144745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3818991709038530148763163 5728487563557795223144745)
    ·
      refine ⟨4296365672668346417358559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5728487563557795223144745 4296365672668346417358559)
      ·
        refine ⟨6444548509002519626037839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4296365672668346417358559 6444548509002519626037839)
        ·
          refine ⟨9666822763503779439056759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6444548509002519626037839 9666822763503779439056759)
          ·
            refine ⟨14500234145255669158585139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9666822763503779439056759 14500234145255669158585139)
            ·
              refine ⟨21750351217883503737877709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14500234145255669158585139 21750351217883503737877709)
              ·
                refine ⟨8156381706706313901704141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21750351217883503737877709 8156381706706313901704141)
                ·
                  refine ⟨3058643140014867713139053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8156381706706313901704141 3058643140014867713139053)
                  ·
                    refine ⟨1146991177505575392427145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3058643140014867713139053 1146991177505575392427145)
                    ·
                      refine ⟨860243383129181544320359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1146991177505575392427145 860243383129181544320359)
                      ·
                        rfl

theorem cell23_1675318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_1675318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675318 prefixEnd_1675318 := by exact prefixLift 1675318
  have htrace : WordTrace (prefixWord ++ tailWord_1675318) baseStart_1675318 baseEnd_1675318 := by
    simpa [prefixWord, tailWord_1675318, baseEnd_1675318] using wordTrace_append hprefix tailTrace_1675318
  have hstable : (prefixWord ++ tailWord_1675318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675318).length < 2 ^ (prefixWord ++ tailWord_1675318).sum := by decide
  have hdescent : baseEnd_1675318 < baseStart_1675318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675337 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 9]
def baseStart_1675337 : Nat := 118140960795 + 1675337 * 2 ^ 59
def prefixEnd_1675337 : Nat := 4983230072969 + 3 ^ 40 * 1675337 * 2
def baseEnd_1675337 : Nat := 95583682140179663331419

theorem tailTrace_1675337 : CollatzResearch.WordTrace tailWord_1675337 prefixEnd_1675337 95583682140179663331419 := by
  unfold tailWord_1675337
  simp only [CollatzResearch.WordTrace]
  refine ⟨61104560331547648625152265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40736373554365099083434843 61104560331547648625152265)
  ·
    refine ⟨45828420248660736468864199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61104560331547648625152265 45828420248660736468864199)
    ·
      refine ⟨68742630372991104703296299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45828420248660736468864199 68742630372991104703296299)
      ·
        refine ⟨103113945559486657054944449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68742630372991104703296299 103113945559486657054944449)
        ·
          refine ⟨77335459169614992791208337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103113945559486657054944449 77335459169614992791208337)
          ·
            refine ⟨58001594377211244593406253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77335459169614992791208337 58001594377211244593406253)
            ·
              refine ⟨21750597891454216722527345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58001594377211244593406253 21750597891454216722527345)
              ·
                refine ⟨16312948418590662541895509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21750597891454216722527345 16312948418590662541895509)
                ·
                  refine ⟨95583682140179663331419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16312948418590662541895509 95583682140179663331419)
                  ·
                    rfl

theorem cell23_1675337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 9].length) (baseStart_1675337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675337 prefixEnd_1675337 := by exact prefixLift 1675337
  have htrace : WordTrace (prefixWord ++ tailWord_1675337) baseStart_1675337 baseEnd_1675337 := by
    simpa [prefixWord, tailWord_1675337, baseEnd_1675337] using wordTrace_append hprefix tailTrace_1675337
  have hstable : (prefixWord ++ tailWord_1675337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675337).length < 2 ^ (prefixWord ++ tailWord_1675337).sum := by decide
  have hdescent : baseEnd_1675337 < baseStart_1675337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675354 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 7]
def baseStart_1675354 : Nat := 118140960795 + 1675354 * 2 ^ 59
def prefixEnd_1675354 : Nat := 4983230072969 + 3 ^ 40 * 1675354 * 2
def baseEnd_1675354 : Nat := 95584652048082600385577

theorem tailTrace_1675354 : CollatzResearch.WordTrace tailWord_1675354 prefixEnd_1675354 95584652048082600385577 := by
  unfold tailWord_1675354
  simp only [CollatzResearch.WordTrace]
  refine ⟨15276295093121515132130279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40736786914990707019014077 15276295093121515132130279)
  ·
    refine ⟨22914442639682272698195419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15276295093121515132130279 22914442639682272698195419)
    ·
      refine ⟨34371663959523409047293129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22914442639682272698195419 34371663959523409047293129)
      ·
        refine ⟨25778747969642556785469847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34371663959523409047293129 25778747969642556785469847)
        ·
          refine ⟨38668121954463835178204771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25778747969642556785469847 38668121954463835178204771)
          ·
            refine ⟨58002182931695752767307157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38668121954463835178204771 58002182931695752767307157)
            ·
              refine ⟨2718852324923238410967523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58002182931695752767307157 2718852324923238410967523)
              ·
                refine ⟨4078278487384857616451285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2718852324923238410967523 4078278487384857616451285)
                ·
                  refine ⟨95584652048082600385577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4078278487384857616451285 95584652048082600385577)
                  ·
                    rfl

theorem cell23_1675354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 7].length) (baseStart_1675354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675354 prefixEnd_1675354 := by exact prefixLift 1675354
  have htrace : WordTrace (prefixWord ++ tailWord_1675354) baseStart_1675354 baseEnd_1675354 := by
    simpa [prefixWord, tailWord_1675354, baseEnd_1675354] using wordTrace_append hprefix tailTrace_1675354
  have hstable : (prefixWord ++ tailWord_1675354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675354).length < 2 ^ (prefixWord ++ tailWord_1675354).sum := by decide
  have hdescent : baseEnd_1675354 < baseStart_1675354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675384 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 2, 5]
def baseStart_1675384 : Nat := 118140960795 + 1675384 * 2 ^ 59
def prefixEnd_1675384 : Nat := 4983230072969 + 3 ^ 40 * 1675384 * 2
def baseEnd_1675384 : Nat := 286759090950792762031685

theorem tailTrace_1675384 : CollatzResearch.WordTrace tailWord_1675384 prefixEnd_1675384 286759090950792762031685 := by
  unfold tailWord_1675384
  simp only [CollatzResearch.WordTrace]
  refine ⟨30553137281188687826056603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40737516374918250434742137 30553137281188687826056603)
  ·
    refine ⟨45829705921783031739084905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30553137281188687826056603 45829705921783031739084905)
    ·
      refine ⟨34372279441337273804313679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45829705921783031739084905 34372279441337273804313679)
      ·
        refine ⟨51558419162005910706470519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34372279441337273804313679 51558419162005910706470519)
        ·
          refine ⟨77337628743008866059705779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51558419162005910706470519 77337628743008866059705779)
          ·
            refine ⟨116006443114513299089558669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77337628743008866059705779 116006443114513299089558669)
            ·
              refine ⟨43502416167942487158584501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116006443114513299089558669 43502416167942487158584501)
              ·
                refine ⟨4078351515744608171117297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43502416167942487158584501 4078351515744608171117297)
                ·
                  refine ⟨3058763636808456128337973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4078351515744608171117297 3058763636808456128337973)
                  ·
                    refine ⟨286759090950792762031685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3058763636808456128337973 286759090950792762031685)
                    ·
                      rfl

theorem cell23_1675384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_1675384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675384 prefixEnd_1675384 := by exact prefixLift 1675384
  have htrace : WordTrace (prefixWord ++ tailWord_1675384) baseStart_1675384 baseEnd_1675384 := by
    simpa [prefixWord, tailWord_1675384, baseEnd_1675384] using wordTrace_append hprefix tailTrace_1675384
  have hstable : (prefixWord ++ tailWord_1675384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675384).length < 2 ^ (prefixWord ++ tailWord_1675384).sum := by decide
  have hdescent : baseEnd_1675384 < baseStart_1675384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675388 : List Nat := [2, 2, 2, 1, 1, 6, 1, 3, 5]
def baseStart_1675388 : Nat := 118140960795 + 1675388 * 2 ^ 59
def prefixEnd_1675388 : Nat := 4983230072969 + 3 ^ 40 * 1675388 * 2
def baseEnd_1675388 : Nat := 95586591863888474493893

theorem tailTrace_1675388 : CollatzResearch.WordTrace tailWord_1675388 prefixEnd_1675388 95586591863888474493893 := by
  unfold tailWord_1675388
  simp only [CollatzResearch.WordTrace]
  refine ⟨30553210227181442167629409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40737613636241922890172545 30553210227181442167629409)
  ·
    refine ⟨22914907670386081625722057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30553210227181442167629409 22914907670386081625722057)
    ·
      refine ⟨17186180752789561219291543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22914907670386081625722057 17186180752789561219291543)
      ·
        refine ⟨25779271129184341828937315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17186180752789561219291543 25779271129184341828937315)
        ·
          refine ⟨38668906693776512743405973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25779271129184341828937315 38668906693776512743405973)
          ·
            refine ⟨1812605001270774034847155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38668906693776512743405973 1812605001270774034847155)
            ·
              refine ⟨2718907501906161052270733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812605001270774034847155 2718907501906161052270733)
              ·
                refine ⟨1019590313214810394601525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2718907501906161052270733 1019590313214810394601525)
                ·
                  refine ⟨95586591863888474493893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1019590313214810394601525 95586591863888474493893)
                  ·
                    rfl

theorem cell23_1675388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 5].length) (baseStart_1675388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675388 prefixEnd_1675388 := by exact prefixLift 1675388
  have htrace : WordTrace (prefixWord ++ tailWord_1675388) baseStart_1675388 baseEnd_1675388 := by
    simpa [prefixWord, tailWord_1675388, baseEnd_1675388] using wordTrace_append hprefix tailTrace_1675388
  have hstable : (prefixWord ++ tailWord_1675388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675388).length < 2 ^ (prefixWord ++ tailWord_1675388).sum := by decide
  have hdescent : baseEnd_1675388 < baseStart_1675388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675448 : List Nat := [2, 1, 2, 1, 2, 1, 4, 5, 1, 4]
def baseStart_1675448 : Nat := 118140960795 + 1675448 * 2 ^ 59
def prefixEnd_1675448 : Nat := 4983230072969 + 3 ^ 40 * 1675448 * 2
def baseEnd_1675448 : Nat := 286770045204755345231587

theorem tailTrace_1675448 : CollatzResearch.WordTrace tailWord_1675448 prefixEnd_1675448 286770045204755345231587 := by
  unfold tailWord_1675448
  simp only [CollatzResearch.WordTrace]
  refine ⟨30554304417072757291221499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40739072556097009721628665 30554304417072757291221499)
  ·
    refine ⟨45831456625609135936832249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30554304417072757291221499 45831456625609135936832249)
    ·
      refine ⟨34373592469206851952624187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45831456625609135936832249 34373592469206851952624187)
      ·
        refine ⟨51560388703810277928936281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34373592469206851952624187 51560388703810277928936281)
        ·
          refine ⟨38670291527857708446702211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51560388703810277928936281 38670291527857708446702211)
          ·
            refine ⟨58005437291786562670053317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38670291527857708446702211 58005437291786562670053317)
            ·
              refine ⟨10876019492209980500634997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58005437291786562670053317 10876019492209980500634997)
              ·
                refine ⟨1019626827394685671934531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10876019492209980500634997 1019626827394685671934531)
                ·
                  refine ⟨1529440241092028507901797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019626827394685671934531 1529440241092028507901797)
                  ·
                    refine ⟨286770045204755345231587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1529440241092028507901797 286770045204755345231587)
                    ·
                      rfl

theorem cell23_1675448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 1, 4].length) (baseStart_1675448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675448 prefixEnd_1675448 := by exact prefixLift 1675448
  have htrace : WordTrace (prefixWord ++ tailWord_1675448) baseStart_1675448 baseEnd_1675448 := by
    simpa [prefixWord, tailWord_1675448, baseEnd_1675448] using wordTrace_append hprefix tailTrace_1675448
  have hstable : (prefixWord ++ tailWord_1675448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675448).length < 2 ^ (prefixWord ++ tailWord_1675448).sum := by decide
  have hdescent : baseEnd_1675448 < baseStart_1675448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675464 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_1675464 : Nat := 118140960795 + 1675464 * 2 ^ 59
def prefixEnd_1675464 : Nat := 4983230072969 + 3 ^ 40 * 1675464 * 2
def baseEnd_1675464 : Nat := 860318351304737973094687

theorem tailTrace_1675464 : CollatzResearch.WordTrace tailWord_1675464 prefixEnd_1675464 860318351304737973094687 := by
  unfold tailWord_1675464
  simp only [CollatzResearch.WordTrace]
  refine ⟨30554596201043774657512723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40739461601391699543350297 30554596201043774657512723)
  ·
    refine ⟨45831894301565661986269085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30554596201043774657512723 45831894301565661986269085)
    ·
      refine ⟨17186960363087123244850907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45831894301565661986269085 17186960363087123244850907)
      ·
        refine ⟨25780440544630684867276361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17186960363087123244850907 25780440544630684867276361)
        ·
          refine ⟨19335330408473013650457271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25780440544630684867276361 19335330408473013650457271)
          ·
            refine ⟨29002995612709520475685907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19335330408473013650457271 29002995612709520475685907)
            ·
              refine ⟨43504493419064280713528861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29002995612709520475685907 43504493419064280713528861)
              ·
                refine ⟨16314185032149105267573323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43504493419064280713528861 16314185032149105267573323)
                ·
                  refine ⟨24471277548223657901359985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16314185032149105267573323 24471277548223657901359985)
                  ·
                    refine ⟨18353458161167743426019989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24471277548223657901359985 18353458161167743426019989)
                    ·
                      refine ⟨860318351304737973094687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18353458161167743426019989 860318351304737973094687)
                      ·
                        rfl

theorem cell23_1675464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_1675464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675464 prefixEnd_1675464 := by exact prefixLift 1675464
  have htrace : WordTrace (prefixWord ++ tailWord_1675464) baseStart_1675464 baseEnd_1675464 := by
    simpa [prefixWord, tailWord_1675464, baseEnd_1675464] using wordTrace_append hprefix tailTrace_1675464
  have hstable : (prefixWord ++ tailWord_1675464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675464).length < 2 ^ (prefixWord ++ tailWord_1675464).sum := by decide
  have hdescent : baseEnd_1675464 < baseStart_1675464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675488 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 3, 1, 3]
def baseStart_1675488 : Nat := 118140960795 + 1675488 * 2 ^ 59
def prefixEnd_1675488 : Nat := 4983230072969 + 3 ^ 40 * 1675488 * 2
def baseEnd_1675488 : Nat := 860330674840445879194577

theorem tailTrace_1675488 : CollatzResearch.WordTrace tailWord_1675488 prefixEnd_1675488 860330674840445879194577 := by
  unfold tailWord_1675488
  simp only [CollatzResearch.WordTrace]
  refine ⟨30555033877000300706949559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40740045169333734275932745 30555033877000300706949559)
  ·
    refine ⟨45832550815500451060424339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30555033877000300706949559 45832550815500451060424339)
    ·
      refine ⟨68748826223250676590636509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45832550815500451060424339 68748826223250676590636509)
      ·
        refine ⟨25780809833719003721488691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68748826223250676590636509 25780809833719003721488691)
        ·
          refine ⟨38671214750578505582233037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25780809833719003721488691 38671214750578505582233037)
          ·
            refine ⟨14501705531466939593337389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38671214750578505582233037 14501705531466939593337389)
            ·
              refine ⟨5438139574300102347501521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14501705531466939593337389 5438139574300102347501521)
              ·
                refine ⟨4078604680725076760626141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5438139574300102347501521 4078604680725076760626141)
                ·
                  refine ⟨1529476755271903785234803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4078604680725076760626141 1529476755271903785234803)
                  ·
                    refine ⟨2294215132907855677852205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1529476755271903785234803 2294215132907855677852205)
                    ·
                      refine ⟨860330674840445879194577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2294215132907855677852205 860330674840445879194577)
                      ·
                        rfl

theorem cell23_1675488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_1675488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675488 prefixEnd_1675488 := by exact prefixLift 1675488
  have htrace : WordTrace (prefixWord ++ tailWord_1675488) baseStart_1675488 baseEnd_1675488 := by
    simpa [prefixWord, tailWord_1675488, baseEnd_1675488] using wordTrace_append hprefix tailTrace_1675488
  have hstable : (prefixWord ++ tailWord_1675488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675488).length < 2 ^ (prefixWord ++ tailWord_1675488).sum := by decide
  have hdescent : baseEnd_1675488 < baseStart_1675488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675498 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 1, 5, 2]
def baseStart_1675498 : Nat := 118140960795 + 1675498 * 2 ^ 59
def prefixEnd_1675498 : Nat := 4983230072969 + 3 ^ 40 * 1675498 * 2
def baseEnd_1675498 : Nat := 860335809646990840069531

theorem tailTrace_1675498 : CollatzResearch.WordTrace tailWord_1675498 prefixEnd_1675498 860335809646990840069531 := by
  unfold tailWord_1675498
  simp only [CollatzResearch.WordTrace]
  refine ⟨15277608120991093280440787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40740288322642915414508765 15277608120991093280440787)
  ·
    refine ⟨22916412181486639920661181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15277608120991093280440787 22916412181486639920661181)
    ·
      refine ⟨8593654568057489970247943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22916412181486639920661181 8593654568057489970247943)
      ·
        refine ⟨12890481852086234955371915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8593654568057489970247943 12890481852086234955371915)
        ·
          refine ⟨19335722778129352433057873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12890481852086234955371915 19335722778129352433057873)
          ·
            refine ⟨14501792083597014324793405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19335722778129352433057873 14501792083597014324793405)
            ·
              refine ⟨5438172031348880371797527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14501792083597014324793405 5438172031348880371797527)
              ·
                refine ⟨8157258047023320557696291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5438172031348880371797527 8157258047023320557696291)
                ·
                  refine ⟨12235887070534980836544437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8157258047023320557696291 12235887070534980836544437)
                  ·
                    refine ⟨1147114412862654453426041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12235887070534980836544437 1147114412862654453426041)
                    ·
                      refine ⟨860335809646990840069531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1147114412862654453426041 860335809646990840069531)
                      ·
                        rfl

theorem cell23_1675498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_1675498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675498 prefixEnd_1675498 := by exact prefixLift 1675498
  have htrace : WordTrace (prefixWord ++ tailWord_1675498) baseStart_1675498 baseEnd_1675498 := by
    simpa [prefixWord, tailWord_1675498, baseEnd_1675498] using wordTrace_append hprefix tailTrace_1675498
  have hstable : (prefixWord ++ tailWord_1675498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675498).length < 2 ^ (prefixWord ++ tailWord_1675498).sum := by decide
  have hdescent : baseEnd_1675498 < baseStart_1675498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675505 : List Nat := [1, 2, 2, 2, 2, 1, 3, 5, 1, 1, 3]
def baseStart_1675505 : Nat := 118140960795 + 1675505 * 2 ^ 59
def prefixEnd_1675505 : Nat := 4983230072969 + 3 ^ 40 * 1675505 * 2
def baseEnd_1675505 : Nat := 860339404011572312681999

theorem tailTrace_1675505 : CollatzResearch.WordTrace tailWord_1675505 prefixEnd_1675505 860339404011572312681999 := by
  unfold tailWord_1675505
  simp only [CollatzResearch.WordTrace]
  refine ⟨61110687794939013317267969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40740458529959342211511979 61110687794939013317267969)
  ·
    refine ⟨45833015846204259987950977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61110687794939013317267969 45833015846204259987950977)
    ·
      refine ⟨34374761884653194990963233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45833015846204259987950977 34374761884653194990963233)
      ·
        refine ⟨25781071413489896243222425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34374761884653194990963233 25781071413489896243222425)
        ·
          refine ⟨19335803560117422182416819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25781071413489896243222425 19335803560117422182416819)
          ·
            refine ⟨29003705340176133273625229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19335803560117422182416819 29003705340176133273625229)
            ·
              refine ⟨10876389502566049977609461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29003705340176133273625229 10876389502566049977609461)
              ·
                refine ⟨1019661515865567185400887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10876389502566049977609461 1019661515865567185400887)
                ·
                  refine ⟨1529492273798350778101331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019661515865567185400887 1529492273798350778101331)
                  ·
                    refine ⟨2294238410697526167151997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1529492273798350778101331 2294238410697526167151997)
                    ·
                      refine ⟨860339404011572312681999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2294238410697526167151997 860339404011572312681999)
                      ·
                        rfl

theorem cell23_1675505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_1675505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675505 prefixEnd_1675505 := by exact prefixLift 1675505
  have htrace : WordTrace (prefixWord ++ tailWord_1675505) baseStart_1675505 baseEnd_1675505 := by
    simpa [prefixWord, tailWord_1675505, baseEnd_1675505] using wordTrace_append hprefix tailTrace_1675505
  have hstable : (prefixWord ++ tailWord_1675505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675505).length < 2 ^ (prefixWord ++ tailWord_1675505).sum := by decide
  have hdescent : baseEnd_1675505 < baseStart_1675505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675522 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_1675522 : Nat := 118140960795 + 1675522 * 2 ^ 59
def prefixEnd_1675522 : Nat := 4983230072969 + 3 ^ 40 * 1675522 * 2
def baseEnd_1675522 : Nat := 860348133182698746169421

theorem tailTrace_1675522 : CollatzResearch.WordTrace tailWord_1675522 prefixEnd_1675522 860348133182698746169421 := by
  unfold tailWord_1675522
  simp only [CollatzResearch.WordTrace]
  refine ⟨15277826958969356305159205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40740871890584950147091213 15277826958969356305159205)
  ·
    refine ⟨2864592554806754307217351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15277826958969356305159205 2864592554806754307217351)
    ·
      refine ⟨4296888832210131460826027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2864592554806754307217351 4296888832210131460826027)
      ·
        refine ⟨6445333248315197191239041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4296888832210131460826027 6445333248315197191239041)
        ·
          refine ⟨4833999936236397893429281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6445333248315197191239041 4833999936236397893429281)
          ·
            refine ⟨3625499952177298420071961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4833999936236397893429281 3625499952177298420071961)
            ·
              refine ⟨2719124964132973815053971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3625499952177298420071961 2719124964132973815053971)
              ·
                refine ⟨4078687446199460722580957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719124964132973815053971 4078687446199460722580957)
                ·
                  refine ⟨1529507792324797770967859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4078687446199460722580957 1529507792324797770967859)
                  ·
                    refine ⟨2294261688487196656451789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1529507792324797770967859 2294261688487196656451789)
                    ·
                      refine ⟨860348133182698746169421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2294261688487196656451789 860348133182698746169421)
                      ·
                        rfl

theorem cell23_1675522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_1675522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675522 prefixEnd_1675522 := by exact prefixLift 1675522
  have htrace : WordTrace (prefixWord ++ tailWord_1675522) baseStart_1675522 baseEnd_1675522 := by
    simpa [prefixWord, tailWord_1675522, baseEnd_1675522] using wordTrace_append hprefix tailTrace_1675522
  have hstable : (prefixWord ++ tailWord_1675522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675522).length < 2 ^ (prefixWord ++ tailWord_1675522).sum := by decide
  have hdescent : baseEnd_1675522 < baseStart_1675522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675531 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 5]
def baseStart_1675531 : Nat := 118140960795 + 1675531 * 2 ^ 59
def prefixEnd_1675531 : Nat := 4983230072969 + 3 ^ 40 * 1675531 * 2
def baseEnd_1675531 : Nat := 860352754508589210956879

theorem tailTrace_1675531 : CollatzResearch.WordTrace tailWord_1675531 prefixEnd_1675531 860352754508589210956879 := by
  unfold tailWord_1675531
  simp only [CollatzResearch.WordTrace]
  refine ⟨61111636092844819757714447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40741090728563213171809631 61111636092844819757714447)
  ·
    refine ⟨91667454139267229636571671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61111636092844819757714447 91667454139267229636571671)
    ·
      refine ⟨137501181208900844454857507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91667454139267229636571671 137501181208900844454857507)
      ·
        refine ⟨206251771813351266682286261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137501181208900844454857507 206251771813351266682286261)
        ·
          refine ⟨19336103607501681251464337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206251771813351266682286261 19336103607501681251464337)
          ·
            refine ⟨14502077705626260938598253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19336103607501681251464337 14502077705626260938598253)
            ·
              refine ⟨5438279139609847851974345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14502077705626260938598253 5438279139609847851974345)
              ·
                refine ⟨4078709354707385888980759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5438279139609847851974345 4078709354707385888980759)
                ·
                  refine ⟨6118064032061078833471139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4078709354707385888980759 6118064032061078833471139)
                  ·
                    refine ⟨9177096048091618250206709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6118064032061078833471139 9177096048091618250206709)
                    ·
                      refine ⟨860352754508589210956879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9177096048091618250206709 860352754508589210956879)
                      ·
                        rfl

theorem cell23_1675531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 5].length) (baseStart_1675531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675531 prefixEnd_1675531 := by exact prefixLift 1675531
  have htrace : WordTrace (prefixWord ++ tailWord_1675531) baseStart_1675531 baseEnd_1675531 := by
    simpa [prefixWord, tailWord_1675531, baseEnd_1675531] using wordTrace_append hprefix tailTrace_1675531
  have hstable : (prefixWord ++ tailWord_1675531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675531).length < 2 ^ (prefixWord ++ tailWord_1675531).sum := by decide
  have hdescent : baseEnd_1675531 < baseStart_1675531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675551 : List Nat := [1, 1, 2, 4, 3, 2, 1, 9]
def baseStart_1675551 : Nat := 118140960795 + 1675551 * 2 ^ 59
def prefixEnd_1675551 : Nat := 4983230072969 + 3 ^ 40 * 1675551 * 2
def baseEnd_1675551 : Nat := 31865297189691819729881

theorem tailTrace_1675551 : CollatzResearch.WordTrace tailWord_1675551 prefixEnd_1675551 31865297189691819729881 := by
  unfold tailWord_1675551
  simp only [CollatzResearch.WordTrace]
  refine ⟨61112365552772363173442507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40741577035181575448961671 61112365552772363173442507)
  ·
    refine ⟨91668548329158544760163761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61112365552772363173442507 91668548329158544760163761)
    ·
      refine ⟨68751411246868908570122821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91668548329158544760163761 68751411246868908570122821)
      ·
        refine ⟨12890889608787920356898029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68751411246868908570122821 12890889608787920356898029)
        ·
          refine ⟨4834083603295470133836761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12890889608787920356898029 4834083603295470133836761)
          ·
            refine ⟨3625562702471602600377571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4834083603295470133836761 3625562702471602600377571)
            ·
              refine ⟨5438344053707403900566357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3625562702471602600377571 5438344053707403900566357)
              ·
                refine ⟨31865297189691819729881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5438344053707403900566357 31865297189691819729881)
                ·
                  rfl

theorem cell23_1675551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 9].length) (baseStart_1675551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675551 prefixEnd_1675551 := by exact prefixLift 1675551
  have htrace : WordTrace (prefixWord ++ tailWord_1675551) baseStart_1675551 baseEnd_1675551 := by
    simpa [prefixWord, tailWord_1675551, baseEnd_1675551] using wordTrace_append hprefix tailTrace_1675551
  have hstable : (prefixWord ++ tailWord_1675551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675551).length < 2 ^ (prefixWord ++ tailWord_1675551).sum := by decide
  have hdescent : baseEnd_1675551 < baseStart_1675551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675612 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1675612 : Nat := 118140960795 + 1675612 * 2 ^ 59
def prefixEnd_1675612 : Nat := 4983230072969 + 3 ^ 40 * 1675612 * 2
def baseEnd_1675612 : Nat := 860394346441603394044007

theorem tailTrace_1675612 : CollatzResearch.WordTrace tailWord_1675612 prefixEnd_1675612 860394346441603394044007 := by
  unfold tailWord_1675612
  simp only [CollatzResearch.WordTrace]
  refine ⟨30557295202775685295706545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40743060270367580394275393 30557295202775685295706545)
  ·
    refine ⟨22917971402081763971779909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30557295202775685295706545 22917971402081763971779909)
    ·
      refine ⟨4297119637890330744708733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22917971402081763971779909 4297119637890330744708733)
      ·
        refine ⟨1611419864208874029265775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4297119637890330744708733 1611419864208874029265775)
        ·
          refine ⟨2417129796313311043898663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611419864208874029265775 2417129796313311043898663)
          ·
            refine ⟨3625694694469966565847995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2417129796313311043898663 3625694694469966565847995)
            ·
              refine ⟨5438542041704949848771993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3625694694469966565847995 5438542041704949848771993)
              ·
                refine ⟨4078906531278712386578995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5438542041704949848771993 4078906531278712386578995)
                ·
                  refine ⟨6118359796918068579868493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4078906531278712386578995 6118359796918068579868493)
                  ·
                    refine ⟨2294384923844275717450685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6118359796918068579868493 2294384923844275717450685)
                    ·
                      refine ⟨860394346441603394044007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2294384923844275717450685 860394346441603394044007)
                      ·
                        rfl

theorem cell23_1675612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1675612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675612 prefixEnd_1675612 := by exact prefixLift 1675612
  have htrace : WordTrace (prefixWord ++ tailWord_1675612) baseStart_1675612 baseEnd_1675612 := by
    simpa [prefixWord, tailWord_1675612, baseEnd_1675612] using wordTrace_append hprefix tailTrace_1675612
  have hstable : (prefixWord ++ tailWord_1675612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675612).length < 2 ^ (prefixWord ++ tailWord_1675612).sum := by decide
  have hdescent : baseEnd_1675612 < baseStart_1675612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675641 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 7]
def baseStart_1675641 : Nat := 118140960795 + 1675641 * 2 ^ 59
def prefixEnd_1675641 : Nat := 4983230072969 + 3 ^ 40 * 1675641 * 2
def baseEnd_1675641 : Nat := 95601026375620420064597

theorem tailTrace_1675641 : CollatzResearch.WordTrace tailWord_1675641 prefixEnd_1675641 95601026375620420064597 := by
  unfold tailWord_1675641
  simp only [CollatzResearch.WordTrace]
  refine ⟨61115648122446308544218777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40743765414964205696145851 61115648122446308544218777)
  ·
    refine ⟨45836736091834731408164083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61115648122446308544218777 45836736091834731408164083)
    ·
      refine ⟨68755104137752097112246125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45836736091834731408164083 68755104137752097112246125)
      ·
        refine ⟨25783164051657036417092297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68755104137752097112246125 25783164051657036417092297)
        ·
          refine ⟨19337373038742777312819223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25783164051657036417092297 19337373038742777312819223)
          ·
            refine ⟨29006059558114165969228835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19337373038742777312819223 29006059558114165969228835)
            ·
              refine ⟨43509089337171248953843253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29006059558114165969228835 43509089337171248953843253)
              ·
                refine ⟨4078977125359804589422805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43509089337171248953843253 4078977125359804589422805)
                ·
                  refine ⟨95601026375620420064597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4078977125359804589422805 95601026375620420064597)
                  ·
                    rfl

theorem cell23_1675641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 7].length) (baseStart_1675641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675641 prefixEnd_1675641 := by exact prefixLift 1675641
  have htrace : WordTrace (prefixWord ++ tailWord_1675641) baseStart_1675641 baseEnd_1675641 := by
    simpa [prefixWord, tailWord_1675641, baseEnd_1675641] using wordTrace_append hprefix tailTrace_1675641
  have hstable : (prefixWord ++ tailWord_1675641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675641).length < 2 ^ (prefixWord ++ tailWord_1675641).sum := by decide
  have hdescent : baseEnd_1675641 < baseStart_1675641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675652 : List Nat := [2, 3, 2, 1, 1, 2, 1, 5, 2, 2, 2]
def baseStart_1675652 : Nat := 118140960795 + 1675652 * 2 ^ 59
def prefixEnd_1675652 : Nat := 4983230072969 + 3 ^ 40 * 1675652 * 2
def baseEnd_1675652 : Nat := 860414885667783237543823

theorem tailTrace_1675652 : CollatzResearch.WordTrace tailWord_1675652 prefixEnd_1675652 860414885667783237543823 := by
  unfold tailWord_1675652
  simp only [CollatzResearch.WordTrace]
  refine ⟨30558024662703228711434605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40744032883604304948579473 30558024662703228711434605)
  ·
    refine ⟨11459259248513710766787977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30558024662703228711434605 11459259248513710766787977)
    ·
      refine ⟨8594444436385283075090983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11459259248513710766787977 8594444436385283075090983)
      ·
        refine ⟨12891666654577924612636475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8594444436385283075090983 12891666654577924612636475)
        ·
          refine ⟨19337499981866886918954713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12891666654577924612636475 19337499981866886918954713)
          ·
            refine ⟨14503124986400165189216035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19337499981866886918954713 14503124986400165189216035)
            ·
              refine ⟨21754687479600247783824053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14503124986400165189216035 21754687479600247783824053)
              ·
                refine ⟨2039501951212523229733505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21754687479600247783824053 2039501951212523229733505)
                ·
                  refine ⟨1529626463409392422300129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2039501951212523229733505 1529626463409392422300129)
                  ·
                    refine ⟨1147219847557044316725097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1529626463409392422300129 1147219847557044316725097)
                    ·
                      refine ⟨860414885667783237543823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1147219847557044316725097 860414885667783237543823)
                      ·
                        rfl

theorem cell23_1675652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_1675652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675652 prefixEnd_1675652 := by exact prefixLift 1675652
  have htrace : WordTrace (prefixWord ++ tailWord_1675652) baseStart_1675652 baseEnd_1675652 := by
    simpa [prefixWord, tailWord_1675652, baseEnd_1675652] using wordTrace_append hprefix tailTrace_1675652
  have hstable : (prefixWord ++ tailWord_1675652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675652).length < 2 ^ (prefixWord ++ tailWord_1675652).sum := by decide
  have hdescent : baseEnd_1675652 < baseStart_1675652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675745 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 2, 2, 3]
def baseStart_1675745 : Nat := 118140960795 + 1675745 * 2 ^ 59
def prefixEnd_1675745 : Nat := 4983230072969 + 3 ^ 40 * 1675745 * 2
def baseEnd_1675745 : Nat := 860462639368651373680895

theorem tailTrace_1675745 : CollatzResearch.WordTrace tailWord_1675745 prefixEnd_1675745 860462639368651373680895 := by
  unfold tailWord_1675745
  simp only [CollatzResearch.WordTrace]
  refine ⟨61119441314069534306004689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40746294209379689537336459 61119441314069534306004689)
  ·
    refine ⟨45839580985552150729503517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61119441314069534306004689 45839580985552150729503517)
    ·
      refine ⟨17189842869582056523563819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45839580985552150729503517 17189842869582056523563819)
      ·
        refine ⟨25784764304373084785345729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17189842869582056523563819 25784764304373084785345729)
        ·
          refine ⟨19338573228279813589009297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25784764304373084785345729 19338573228279813589009297)
          ·
            refine ⟨14503929921209860191756973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19338573228279813589009297 14503929921209860191756973)
            ·
              refine ⟨5438973720453697571908865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14503929921209860191756973 5438973720453697571908865)
              ·
                refine ⟨4079230290340273178931649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5438973720453697571908865 4079230290340273178931649)
                ·
                  refine ⟨3059422717755204884198737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4079230290340273178931649 3059422717755204884198737)
                  ·
                    refine ⟨2294567038316403663149053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3059422717755204884198737 2294567038316403663149053)
                    ·
                      refine ⟨860462639368651373680895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2294567038316403663149053 860462639368651373680895)
                      ·
                        rfl

theorem cell23_1675745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_1675745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675745 prefixEnd_1675745 := by exact prefixLift 1675745
  have htrace : WordTrace (prefixWord ++ tailWord_1675745) baseStart_1675745 baseEnd_1675745 := by
    simpa [prefixWord, tailWord_1675745, baseEnd_1675745] using wordTrace_append hprefix tailTrace_1675745
  have hstable : (prefixWord ++ tailWord_1675745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675745).length < 2 ^ (prefixWord ++ tailWord_1675745).sum := by decide
  have hdescent : baseEnd_1675745 < baseStart_1675745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675752 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 3, 4]
def baseStart_1675752 : Nat := 118140960795 + 1675752 * 2 ^ 59
def prefixEnd_1675752 : Nat := 4983230072969 + 3 ^ 40 * 1675752 * 2
def baseEnd_1675752 : Nat := 286822077911077615431121

theorem tailTrace_1675752 : CollatzResearch.WordTrace tailWord_1675752 prefixEnd_1675752 286822077911077615431121 := by
  unfold tailWord_1675752
  simp only [CollatzResearch.WordTrace]
  refine ⟨30559848312522087250754755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40746464416696116334339673 30559848312522087250754755)
  ·
    refine ⟨45839772468783130876132133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30559848312522087250754755 45839772468783130876132133)
    ·
      refine ⟨8594957337896837039274775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45839772468783130876132133 8594957337896837039274775)
      ·
        refine ⟨12892436006845255558912163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8594957337896837039274775 12892436006845255558912163)
        ·
          refine ⟨19338654010267883338368245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12892436006845255558912163 19338654010267883338368245)
          ·
            refine ⟨1812998813462614062972023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19338654010267883338368245 1812998813462614062972023)
            ·
              refine ⟨2719498220193921094458035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812998813462614062972023 2719498220193921094458035)
              ·
                refine ⟨4079247330290881641687053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719498220193921094458035 4079247330290881641687053)
                ·
                  refine ⟨1529717748859080615632645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4079247330290881641687053 1529717748859080615632645)
                  ·
                    refine ⟨286822077911077615431121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1529717748859080615632645 286822077911077615431121)
                    ·
                      rfl

theorem cell23_1675752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_1675752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675752 prefixEnd_1675752 := by exact prefixLift 1675752
  have htrace : WordTrace (prefixWord ++ tailWord_1675752) baseStart_1675752 baseEnd_1675752 := by
    simpa [prefixWord, tailWord_1675752, baseEnd_1675752] using wordTrace_append hprefix tailTrace_1675752
  have hstable : (prefixWord ++ tailWord_1675752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675752).length < 2 ^ (prefixWord ++ tailWord_1675752).sum := by decide
  have hdescent : baseEnd_1675752 < baseStart_1675752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675775 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 5, 1, 3]
def baseStart_1675775 : Nat := 118140960795 + 1675775 * 2 ^ 59
def prefixEnd_1675775 : Nat := 4983230072969 + 3 ^ 40 * 1675775 * 2
def baseEnd_1675775 : Nat := 860478043788286256305757

theorem tailTrace_1675775 : CollatzResearch.WordTrace tailWord_1675775 prefixEnd_1675775 860478043788286256305757 := by
  unfold tailWord_1675775
  simp only [CollatzResearch.WordTrace]
  refine ⟨61120535503960849429596779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40747023669307232953064519 61120535503960849429596779)
  ·
    refine ⟨91680803255941274144395169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61120535503960849429596779 91680803255941274144395169)
    ·
      refine ⟨68760602441955955608296377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91680803255941274144395169 68760602441955955608296377)
      ·
        refine ⟨51570451831466966706222283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68760602441955955608296377 51570451831466966706222283)
        ·
          refine ⟨77355677747200450059333425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51570451831466966706222283 77355677747200450059333425)
          ·
            refine ⟨58016758310400337544500069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77355677747200450059333425 58016758310400337544500069)
            ·
              refine ⟨10878142183200063289593763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58016758310400337544500069 10878142183200063289593763)
              ·
                refine ⟨16317213274800094934390645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10878142183200063289593763 16317213274800094934390645)
                ·
                  refine ⟨1529738744512508900099123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16317213274800094934390645 1529738744512508900099123)
                  ·
                    refine ⟨2294608116768763350148685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1529738744512508900099123 2294608116768763350148685)
                    ·
                      refine ⟨860478043788286256305757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2294608116768763350148685 860478043788286256305757)
                      ·
                        rfl

theorem cell23_1675775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_1675775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675775 prefixEnd_1675775 := by exact prefixLift 1675775
  have htrace : WordTrace (prefixWord ++ tailWord_1675775) baseStart_1675775 baseEnd_1675775 := by
    simpa [prefixWord, tailWord_1675775, baseEnd_1675775] using wordTrace_append hprefix tailTrace_1675775
  have hstable : (prefixWord ++ tailWord_1675775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675775).length < 2 ^ (prefixWord ++ tailWord_1675775).sum := by decide
  have hdescent : baseEnd_1675775 < baseStart_1675775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675802 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2]
def baseStart_1675802 : Nat := 118140960795 + 1675802 * 2 ^ 59
def prefixEnd_1675802 : Nat := 4983230072969 + 3 ^ 40 * 1675802 * 2
def baseEnd_1675802 : Nat := 860491907765957650668133

theorem tailTrace_1675802 : CollatzResearch.WordTrace tailWord_1675802 prefixEnd_1675802 860491907765957650668133 := by
  unfold tailWord_1675802
  simp only [CollatzResearch.WordTrace]
  refine ⟨15280380068715758260207415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40747680183242022027219773 15280380068715758260207415)
  ·
    refine ⟨22920570103073637390311123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15280380068715758260207415 22920570103073637390311123)
    ·
      refine ⟨34380855154610456085466685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22920570103073637390311123 34380855154610456085466685)
      ·
        refine ⟨12892820682978921032050007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34380855154610456085466685 12892820682978921032050007)
        ·
          refine ⟨19339231024468381548075011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12892820682978921032050007 19339231024468381548075011)
          ·
            refine ⟨29008846536702572322112517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19339231024468381548075011 29008846536702572322112517)
            ·
              refine ⟨5439158725631732310396097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29008846536702572322112517 5439158725631732310396097)
              ·
                refine ⟨4079369044223799232797073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5439158725631732310396097 4079369044223799232797073)
                ·
                  refine ⟨3059526783167849424597805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4079369044223799232797073 3059526783167849424597805)
                  ·
                    refine ⟨1147322543687943534224177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3059526783167849424597805 1147322543687943534224177)
                    ·
                      refine ⟨860491907765957650668133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1147322543687943534224177 860491907765957650668133)
                      ·
                        rfl

theorem cell23_1675802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_1675802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675802 prefixEnd_1675802 := by exact prefixLift 1675802
  have htrace : WordTrace (prefixWord ++ tailWord_1675802) baseStart_1675802 baseEnd_1675802 := by
    simpa [prefixWord, tailWord_1675802, baseEnd_1675802] using wordTrace_append hprefix tailTrace_1675802
  have hstable : (prefixWord ++ tailWord_1675802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675802).length < 2 ^ (prefixWord ++ tailWord_1675802).sum := by decide
  have hdescent : baseEnd_1675802 < baseStart_1675802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675809 : List Nat := [1, 2, 3, 2, 2, 1, 3, 4, 1, 1, 3]
def baseStart_1675809 : Nat := 118140960795 + 1675809 * 2 ^ 59
def prefixEnd_1675809 : Nat := 4983230072969 + 3 ^ 40 * 1675809 * 2
def baseEnd_1675809 : Nat := 860495502130539123280601

theorem tailTrace_1675809 : CollatzResearch.WordTrace tailWord_1675809 prefixEnd_1675809 860495502130539123280601 := by
  unfold tailWord_1675809
  simp only [CollatzResearch.WordTrace]
  refine ⟨61121775585837673236334481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40747850390558448824222987 61121775585837673236334481)
  ·
    refine ⟨45841331689378254927250861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61121775585837673236334481 45841331689378254927250861)
    ·
      refine ⟨17190499383516845597719073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45841331689378254927250861 17190499383516845597719073)
      ·
        refine ⟨12892874537637634198289305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17190499383516845597719073 12892874537637634198289305)
        ·
          refine ⟨9669655903228225648716979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12892874537637634198289305 9669655903228225648716979)
          ·
            refine ⟨14504483854842338473075469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9669655903228225648716979 14504483854842338473075469)
            ·
              refine ⟨5439181445565876927403301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14504483854842338473075469 5439181445565876927403301)
              ·
                refine ⟨1019846521043601923888119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5439181445565876927403301 1019846521043601923888119)
                ·
                  refine ⟨1529769781565402885832179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019846521043601923888119 1529769781565402885832179)
                  ·
                    refine ⟨2294654672348104328748269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1529769781565402885832179 2294654672348104328748269)
                    ·
                      refine ⟨860495502130539123280601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2294654672348104328748269 860495502130539123280601)
                      ·
                        rfl

theorem cell23_1675809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_1675809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675809 prefixEnd_1675809 := by exact prefixLift 1675809
  have htrace : WordTrace (prefixWord ++ tailWord_1675809) baseStart_1675809 baseEnd_1675809 := by
    simpa [prefixWord, tailWord_1675809, baseEnd_1675809] using wordTrace_append hprefix tailTrace_1675809
  have hstable : (prefixWord ++ tailWord_1675809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675809).length < 2 ^ (prefixWord ++ tailWord_1675809).sum := by decide
  have hdescent : baseEnd_1675809 < baseStart_1675809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675845 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 1, 2, 4]
def baseStart_1675845 : Nat := 118140960795 + 1675845 * 2 ^ 59
def prefixEnd_1675845 : Nat := 4983230072969 + 3 ^ 40 * 1675845 * 2
def baseEnd_1675845 : Nat := 860513987434100982430435

theorem tailTrace_1675845 : CollatzResearch.WordTrace tailWord_1675845 prefixEnd_1675845 860513987434100982430435 := by
  unfold tailWord_1675845
  simp only [CollatzResearch.WordTrace]
  refine ⟨61123088613707251384644989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40748725742471500923096659 61123088613707251384644989)
  ·
    refine ⟨22921158230140219269241871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61123088613707251384644989 22921158230140219269241871)
    ·
      refine ⟨34381737345210328903862807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22921158230140219269241871 34381737345210328903862807)
      ·
        refine ⟨51572606017815493355794211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34381737345210328903862807 51572606017815493355794211)
        ·
          refine ⟨77358909026723240033691317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51572606017815493355794211 77358909026723240033691317)
          ·
            refine ⟨7252397721255303753158561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77358909026723240033691317 7252397721255303753158561)
            ·
              refine ⟨5439298290941477814868921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7252397721255303753158561 5439298290941477814868921)
              ·
                refine ⟨4079473718206108361151691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5439298290941477814868921 4079473718206108361151691)
                ·
                  refine ⟨6119210577309162541727537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4079473718206108361151691 6119210577309162541727537)
                  ·
                    refine ⟨4589407932981871906295653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6119210577309162541727537 4589407932981871906295653)
                    ·
                      refine ⟨860513987434100982430435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4589407932981871906295653 860513987434100982430435)
                      ·
                        rfl

theorem cell23_1675845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_1675845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675845 prefixEnd_1675845 := by exact prefixLift 1675845
  have htrace : WordTrace (prefixWord ++ tailWord_1675845) baseStart_1675845 baseEnd_1675845 := by
    simpa [prefixWord, tailWord_1675845, baseEnd_1675845] using wordTrace_append hprefix tailTrace_1675845
  have hstable : (prefixWord ++ tailWord_1675845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675845).length < 2 ^ (prefixWord ++ tailWord_1675845).sum := by decide
  have hdescent : baseEnd_1675845 < baseStart_1675845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675846 : List Nat := [6, 1, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_1675846 : Nat := 118140960795 + 1675846 * 2 ^ 59
def prefixEnd_1675846 : Nat := 4983230072969 + 3 ^ 40 * 1675846 * 2
def baseEnd_1675846 : Nat := 286838166971585159505977

theorem tailTrace_1675846 : CollatzResearch.WordTrace tailWord_1675846 prefixEnd_1675846 286838166971585159505977 := by
  unfold tailWord_1675846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1910097658959488392357231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40748750057802419036954261 1910097658959488392357231)
  ·
    refine ⟨2865146488439232588535847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1910097658959488392357231 2865146488439232588535847)
    ·
      refine ⟨4297719732658848882803771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2865146488439232588535847 4297719732658848882803771)
      ·
        refine ⟨6446579598988273324205657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4297719732658848882803771 6446579598988273324205657)
        ·
          refine ⟨4834934699241204993154243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6446579598988273324205657 4834934699241204993154243)
          ·
            refine ⟨7252402048861807489731365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4834934699241204993154243 7252402048861807489731365)
            ·
              refine ⟨1359825384161588904324631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7252402048861807489731365 1359825384161588904324631)
              ·
                refine ⟨2039738076242383356486947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359825384161588904324631 2039738076242383356486947)
                ·
                  refine ⟨3059607114363575034730421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039738076242383356486947 3059607114363575034730421)
                  ·
                    refine ⟨286838166971585159505977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3059607114363575034730421 286838166971585159505977)
                    ·
                      rfl

theorem cell23_1675846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_1675846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675846 prefixEnd_1675846 := by exact prefixLift 1675846
  have htrace : WordTrace (prefixWord ++ tailWord_1675846) baseStart_1675846 baseEnd_1675846 := by
    simpa [prefixWord, tailWord_1675846, baseEnd_1675846] using wordTrace_append hprefix tailTrace_1675846
  have hstable : (prefixWord ++ tailWord_1675846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675846).length < 2 ^ (prefixWord ++ tailWord_1675846).sum := by decide
  have hdescent : baseEnd_1675846 < baseStart_1675846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675852 : List Nat := [2, 2, 1, 3, 1, 2, 3, 3, 1, 2, 3]
def baseStart_1675852 : Nat := 118140960795 + 1675852 * 2 ^ 59
def prefixEnd_1675852 : Nat := 4983230072969 + 3 ^ 40 * 1675852 * 2
def baseEnd_1675852 : Nat := 860517581798682455042903

theorem tailTrace_1675852 : CollatzResearch.WordTrace tailWord_1675852 prefixEnd_1675852 860517581798682455042903 := by
  unfold tailWord_1675852
  simp only [CollatzResearch.WordTrace]
  refine ⟨30561671962340945790074905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40748895949787927720099873 30561671962340945790074905)
  ·
    refine ⟨22921253971755709342556179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30561671962340945790074905 22921253971755709342556179)
    ·
      refine ⟨34381880957633564013834269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22921253971755709342556179 34381880957633564013834269)
      ·
        refine ⟨12893205359112586505187851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34381880957633564013834269 12893205359112586505187851)
        ·
          refine ⟨19339808038668879757781777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12893205359112586505187851 19339808038668879757781777)
          ·
            refine ⟨14504856029001659818336333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19339808038668879757781777 14504856029001659818336333)
            ·
              refine ⟨5439321010875622431876125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14504856029001659818336333 5439321010875622431876125)
              ·
                refine ⟨2039745379078358411953547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5439321010875622431876125 2039745379078358411953547)
                ·
                  refine ⟨3059618068617537617930321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039745379078358411953547 3059618068617537617930321)
                  ·
                    refine ⟨2294713551463153213447741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3059618068617537617930321 2294713551463153213447741)
                    ·
                      refine ⟨860517581798682455042903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2294713551463153213447741 860517581798682455042903)
                      ·
                        rfl

theorem cell23_1675852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_1675852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675852 prefixEnd_1675852 := by exact prefixLift 1675852
  have htrace : WordTrace (prefixWord ++ tailWord_1675852) baseStart_1675852 baseEnd_1675852 := by
    simpa [prefixWord, tailWord_1675852, baseEnd_1675852] using wordTrace_append hprefix tailTrace_1675852
  have hstable : (prefixWord ++ tailWord_1675852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675852).length < 2 ^ (prefixWord ++ tailWord_1675852).sum := by decide
  have hdescent : baseEnd_1675852 < baseStart_1675852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675906 : List Nat := [3, 4, 3, 1, 1, 2, 9]
def baseStart_1675906 : Nat := 118140960795 + 1675906 * 2 ^ 59
def prefixEnd_1675906 : Nat := 4983230072969 + 3 ^ 40 * 1675906 * 2
def baseEnd_1675906 : Nat := 10624016169802780787255

theorem tailTrace_1675906 : CollatzResearch.WordTrace tailWord_1675906 prefixEnd_1675906 10624016169802780787255 := by
  unfold tailWord_1675906
  simp only [CollatzResearch.WordTrace]
  refine ⟨15281328366621564700653893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40750208977657505868410381 15281328366621564700653893)
  ·
    refine ⟨2865249068741543381372605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15281328366621564700653893 2865249068741543381372605)
    ·
      refine ⟨1074468400778078768014727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2865249068741543381372605 1074468400778078768014727)
      ·
        refine ⟨1611702601167118152022091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074468400778078768014727 1611702601167118152022091)
        ·
          refine ⟨2417553901750677228033137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611702601167118152022091 2417553901750677228033137)
          ·
            refine ⟨1813165426313007921024853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2417553901750677228033137 1813165426313007921024853)
            ·
              refine ⟨10624016169802780787255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1813165426313007921024853 10624016169802780787255)
              ·
                rfl

theorem cell23_1675906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 9].length) (baseStart_1675906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675906 prefixEnd_1675906 := by exact prefixLift 1675906
  have htrace : WordTrace (prefixWord ++ tailWord_1675906) baseStart_1675906 baseEnd_1675906 := by
    simpa [prefixWord, tailWord_1675906, baseEnd_1675906] using wordTrace_append hprefix tailTrace_1675906
  have hstable : (prefixWord ++ tailWord_1675906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675906).length < 2 ^ (prefixWord ++ tailWord_1675906).sum := by decide
  have hdescent : baseEnd_1675906 < baseStart_1675906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675909 : List Nat := [1, 3, 1, 1, 4, 2, 2, 3, 1, 3, 2]
def baseStart_1675909 : Nat := 118140960795 + 1675909 * 2 ^ 59
def prefixEnd_1675909 : Nat := 4983230072969 + 3 ^ 40 * 1675909 * 2
def baseEnd_1675909 : Nat := 860546850195988732030141

theorem tailTrace_1675909 : CollatzResearch.WordTrace tailWord_1675909 prefixEnd_1675909 860546850195988732030141 := by
  unfold tailWord_1675909
  simp only [CollatzResearch.WordTrace]
  refine ⟨61125422885475390314974781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40750281923650260209983187 61125422885475390314974781)
  ·
    refine ⟨22922033582053271368115543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61125422885475390314974781 22922033582053271368115543)
    ·
      refine ⟨34383050373079907052173315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22922033582053271368115543 34383050373079907052173315)
      ·
        refine ⟨51574575559619860578259973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34383050373079907052173315 51574575559619860578259973)
        ·
          refine ⟨9670232917428723858423745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51574575559619860578259973 9670232917428723858423745)
          ·
            refine ⟨7252674688071542893817809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9670232917428723858423745 7252674688071542893817809)
            ·
              refine ⟨5439506016053657170363357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7252674688071542893817809 5439506016053657170363357)
              ·
                refine ⟨2039814756020121438886259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5439506016053657170363357 2039814756020121438886259)
                ·
                  refine ⟨3059722134030182158329389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039814756020121438886259 3059722134030182158329389)
                  ·
                    refine ⟨1147395800261318309373521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3059722134030182158329389 1147395800261318309373521)
                    ·
                      refine ⟨860546850195988732030141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1147395800261318309373521 860546850195988732030141)
                      ·
                        rfl

theorem cell23_1675909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 3, 2].length) (baseStart_1675909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675909 prefixEnd_1675909 := by exact prefixLift 1675909
  have htrace : WordTrace (prefixWord ++ tailWord_1675909) baseStart_1675909 baseEnd_1675909 := by
    simpa [prefixWord, tailWord_1675909, baseEnd_1675909] using wordTrace_append hprefix tailTrace_1675909
  have hstable : (prefixWord ++ tailWord_1675909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675909).length < 2 ^ (prefixWord ++ tailWord_1675909).sum := by decide
  have hdescent : baseEnd_1675909 < baseStart_1675909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675962 : List Nat := [3, 1, 1, 1, 2, 3, 2, 5, 5]
def baseStart_1675962 : Nat := 118140960795 + 1675962 * 2 ^ 59
def prefixEnd_1675962 : Nat := 4983230072969 + 3 ^ 40 * 1675962 * 2
def baseEnd_1675962 : Nat := 95619340518964113851933

theorem tailTrace_1675962 : CollatzResearch.WordTrace tailWord_1675962 prefixEnd_1675962 95619340518964113851933 := by
  unfold tailWord_1675962
  simp only [CollatzResearch.WordTrace]
  refine ⟨15281838988570845091663535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40751570636188920244436093 15281838988570845091663535)
  ·
    refine ⟨22922758482856267637495303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15281838988570845091663535 22922758482856267637495303)
    ·
      refine ⟨34384137724284401456242955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22922758482856267637495303 34384137724284401456242955)
      ·
        refine ⟨51576206586426602184364433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34384137724284401456242955 51576206586426602184364433)
        ·
          refine ⟨38682154939819951638273325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51576206586426602184364433 38682154939819951638273325)
          ·
            refine ⟨14505808102432481864352497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38682154939819951638273325 14505808102432481864352497)
            ·
              refine ⟨10879356076824361398264373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14505808102432481864352497 10879356076824361398264373)
              ·
                refine ⟨1019939632202283881087285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10879356076824361398264373 1019939632202283881087285)
                ·
                  refine ⟨95619340518964113851933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1019939632202283881087285 95619340518964113851933)
                  ·
                    rfl

theorem cell23_1675962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 5].length) (baseStart_1675962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675962 prefixEnd_1675962 := by exact prefixLift 1675962
  have htrace : WordTrace (prefixWord ++ tailWord_1675962) baseStart_1675962 baseEnd_1675962 := by
    simpa [prefixWord, tailWord_1675962, baseEnd_1675962] using wordTrace_append hprefix tailTrace_1675962
  have hstable : (prefixWord ++ tailWord_1675962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675962).length < 2 ^ (prefixWord ++ tailWord_1675962).sum := by decide
  have hdescent : baseEnd_1675962 < baseStart_1675962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675975 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 4, 5]
def baseStart_1675975 : Nat := 118140960795 + 1675975 * 2 ^ 59
def prefixEnd_1675975 : Nat := 4983230072969 + 3 ^ 40 * 1675975 * 2
def baseEnd_1675975 : Nat := 286860246639728491268279

theorem tailTrace_1675975 : CollatzResearch.WordTrace tailWord_1675975 prefixEnd_1675975 286860246639728491268279 := by
  unfold tailWord_1675975
  simp only [CollatzResearch.WordTrace]
  refine ⟨61127830103236283586877379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40751886735490855724584919 61127830103236283586877379)
  ·
    refine ⟨91691745154854425380316069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61127830103236283586877379 91691745154854425380316069)
    ·
      refine ⟨17192202216535204758809263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91691745154854425380316069 17192202216535204758809263)
      ·
        refine ⟨25788303324802807138213895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17192202216535204758809263 25788303324802807138213895)
        ·
          refine ⟨38682454987204210707320843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25788303324802807138213895 38682454987204210707320843)
          ·
            refine ⟨58023682480806316060981265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38682454987204210707320843 58023682480806316060981265)
            ·
              refine ⟨43517761860604737045735949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58023682480806316060981265 43517761860604737045735949)
              ·
                refine ⟨16319160697726776392150981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43517761860604737045735949 16319160697726776392150981)
                ·
                  refine ⟨3059842630823770573528309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16319160697726776392150981 3059842630823770573528309)
                  ·
                    refine ⟨286860246639728491268279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3059842630823770573528309 286860246639728491268279)
                    ·
                      rfl

theorem cell23_1675975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_1675975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675975 prefixEnd_1675975 := by exact prefixLift 1675975
  have htrace : WordTrace (prefixWord ++ tailWord_1675975) baseStart_1675975 baseEnd_1675975 := by
    simpa [prefixWord, tailWord_1675975, baseEnd_1675975] using wordTrace_append hprefix tailTrace_1675975
  have hstable : (prefixWord ++ tailWord_1675975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675975).length < 2 ^ (prefixWord ++ tailWord_1675975).sum := by decide
  have hdescent : baseEnd_1675975 < baseStart_1675975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675985 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 1, 2, 5]
def baseStart_1675985 : Nat := 118140960795 + 1675985 * 2 ^ 59
def prefixEnd_1675985 : Nat := 4983230072969 + 3 ^ 40 * 1675985 * 2
def baseEnd_1675985 : Nat := 860585874725730434679791

theorem tailTrace_1675985 : CollatzResearch.WordTrace tailWord_1675985 prefixEnd_1675985 860585874725730434679791 := by
  unfold tailWord_1675985
  simp only [CollatzResearch.WordTrace]
  refine ⟨61128194833200055294741409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40752129888800036863160939 61128194833200055294741409)
  ·
    refine ⟨45846146124900041471056057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61128194833200055294741409 45846146124900041471056057)
    ·
      refine ⟨34384609593675031103292043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45846146124900041471056057 34384609593675031103292043)
      ·
        refine ⟨51576914390512546654938065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34384609593675031103292043 51576914390512546654938065)
        ·
          refine ⟨38682685792884409991203549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51576914390512546654938065 38682685792884409991203549)
          ·
            refine ⟨14506007172331653746701331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38682685792884409991203549 14506007172331653746701331)
            ·
              refine ⟨21759010758497480620051997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14506007172331653746701331 21759010758497480620051997)
              ·
                refine ⟨8159629034436555232519499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21759010758497480620051997 8159629034436555232519499)
                ·
                  refine ⟨12239443551654832848779249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8159629034436555232519499 12239443551654832848779249)
                  ·
                    refine ⟨9179582663741124636584437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12239443551654832848779249 9179582663741124636584437)
                    ·
                      refine ⟨860585874725730434679791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9179582663741124636584437 860585874725730434679791)
                      ·
                        rfl

theorem cell23_1675985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_1675985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1675985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1675985 prefixEnd_1675985 := by exact prefixLift 1675985
  have htrace : WordTrace (prefixWord ++ tailWord_1675985) baseStart_1675985 baseEnd_1675985 := by
    simpa [prefixWord, tailWord_1675985, baseEnd_1675985] using wordTrace_append hprefix tailTrace_1675985
  have hstable : (prefixWord ++ tailWord_1675985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675985).length < 2 ^ (prefixWord ++ tailWord_1675985).sum := by decide
  have hdescent : baseEnd_1675985 < baseStart_1675985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676012 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 3, 6, 2]
def baseStart_1676012 : Nat := 118140960795 + 1676012 * 2 ^ 59
def prefixEnd_1676012 : Nat := 4983230072969 + 3 ^ 40 * 1676012 * 2
def baseEnd_1676012 : Nat := 860599738703401829042167

theorem tailTrace_1676012 : CollatzResearch.WordTrace tailWord_1676012 prefixEnd_1676012 860599738703401829042167 := by
  unfold tailWord_1676012
  simp only [CollatzResearch.WordTrace]
  refine ⟨30564589802051119452987145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40752786402734825937316193 30564589802051119452987145)
  ·
    refine ⟨22923442351538339589740359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30564589802051119452987145 22923442351538339589740359)
    ·
      refine ⟨34385163527307509384610539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22923442351538339589740359 34385163527307509384610539)
      ·
        refine ⟨51577745290961264076915809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34385163527307509384610539 51577745290961264076915809)
        ·
          refine ⟨38683308968220948057686857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51577745290961264076915809 38683308968220948057686857)
          ·
            refine ⟨29012481726165711043265143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38683308968220948057686857 29012481726165711043265143)
            ·
              refine ⟨43518722589248566564897715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29012481726165711043265143 43518722589248566564897715)
              ·
                refine ⟨65278083883872849847346573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43518722589248566564897715 65278083883872849847346573)
                ·
                  refine ⟨24479281456452318692754965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65278083883872849847346573 24479281456452318692754965)
                  ·
                    refine ⟨1147466318271202438722889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24479281456452318692754965 1147466318271202438722889)
                    ·
                      refine ⟨860599738703401829042167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1147466318271202438722889 860599738703401829042167)
                      ·
                        rfl

theorem cell23_1676012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 6, 2].length) (baseStart_1676012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676012 prefixEnd_1676012 := by exact prefixLift 1676012
  have htrace : WordTrace (prefixWord ++ tailWord_1676012) baseStart_1676012 baseEnd_1676012 := by
    simpa [prefixWord, tailWord_1676012, baseEnd_1676012] using wordTrace_append hprefix tailTrace_1676012
  have hstable : (prefixWord ++ tailWord_1676012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676012).length < 2 ^ (prefixWord ++ tailWord_1676012).sum := by decide
  have hdescent : baseEnd_1676012 < baseStart_1676012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676025 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 1, 6, 4]
def baseStart_1676025 : Nat := 118140960795 + 1676025 * 2 ^ 59
def prefixEnd_1676025 : Nat := 4983230072969 + 3 ^ 40 * 1676025 * 2
def baseEnd_1676025 : Nat := 860606413951910278179607

theorem tailTrace_1676025 : CollatzResearch.WordTrace tailWord_1676025 prefixEnd_1676025 860606413951910278179607 := by
  unfold tailWord_1676025
  simp only [CollatzResearch.WordTrace]
  refine ⟨61129653753055142126197529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40753102502036761417465019 61129653753055142126197529)
  ·
    refine ⟨45847240314791356594648147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61129653753055142126197529 45847240314791356594648147)
    ·
      refine ⟨68770860472187034891972221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45847240314791356594648147 68770860472187034891972221)
      ·
        refine ⟨25789072677070138084489583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68770860472187034891972221 25789072677070138084489583)
        ·
          refine ⟨38683609015605207126734375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25789072677070138084489583 38683609015605207126734375)
          ·
            refine ⟨58025413523407810690101563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38683609015605207126734375 58025413523407810690101563)
            ·
              refine ⟨87038120285111716035152345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58025413523407810690101563 87038120285111716035152345)
              ·
                refine ⟨65278590213833787026364259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87038120285111716035152345 65278590213833787026364259)
                ·
                  refine ⟨97917885320750680539546389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65278590213833787026364259 97917885320750680539546389)
                  ·
                    refine ⟨4589900874410188150291237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97917885320750680539546389 4589900874410188150291237)
                    ·
                      refine ⟨860606413951910278179607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4589900874410188150291237 860606413951910278179607)
                      ·
                        rfl

theorem cell23_1676025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_1676025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676025 prefixEnd_1676025 := by exact prefixLift 1676025
  have htrace : WordTrace (prefixWord ++ tailWord_1676025) baseStart_1676025 baseEnd_1676025 := by
    simpa [prefixWord, tailWord_1676025, baseEnd_1676025] using wordTrace_append hprefix tailTrace_1676025
  have hstable : (prefixWord ++ tailWord_1676025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676025).length < 2 ^ (prefixWord ++ tailWord_1676025).sum := by decide
  have hdescent : baseEnd_1676025 < baseStart_1676025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676039 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 3, 4]
def baseStart_1676039 : Nat := 118140960795 + 1676039 * 2 ^ 59
def prefixEnd_1676039 : Nat := 4983230072969 + 3 ^ 40 * 1676039 * 2
def baseEnd_1676039 : Nat := 286871200893691074468181

theorem tailTrace_1676039 : CollatzResearch.WordTrace tailWord_1676039 prefixEnd_1676039 286871200893691074468181 := by
  unfold tailWord_1676039
  simp only [CollatzResearch.WordTrace]
  refine ⟨61130164375004422517207171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40753442916669615011471447 61130164375004422517207171)
  ·
    refine ⟨91695246562506633775810757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61130164375004422517207171 91695246562506633775810757)
    ·
      refine ⟨17192858730469993832964517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91695246562506633775810757 17192858730469993832964517)
      ·
        refine ⟨3223661011963123843680847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17192858730469993832964517 3223661011963123843680847)
        ·
          refine ⟨4835491517944685765521271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3223661011963123843680847 4835491517944685765521271)
          ·
            refine ⟨7253237276917028648281907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4835491517944685765521271 7253237276917028648281907)
            ·
              refine ⟨10879855915375542972422861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7253237276917028648281907 10879855915375542972422861)
              ·
                refine ⟨4079945968265828614658573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10879855915375542972422861 4079945968265828614658573)
                ·
                  refine ⟨1529979738099685730496965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4079945968265828614658573 1529979738099685730496965)
                  ·
                    refine ⟨286871200893691074468181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1529979738099685730496965 286871200893691074468181)
                    ·
                      rfl

theorem cell23_1676039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_1676039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676039 prefixEnd_1676039 := by exact prefixLift 1676039
  have htrace : WordTrace (prefixWord ++ tailWord_1676039) baseStart_1676039 baseEnd_1676039 := by
    simpa [prefixWord, tailWord_1676039, baseEnd_1676039] using wordTrace_append hprefix tailTrace_1676039
  have hstable : (prefixWord ++ tailWord_1676039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676039).length < 2 ^ (prefixWord ++ tailWord_1676039).sum := by decide
  have hdescent : baseEnd_1676039 < baseStart_1676039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676075 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 5]
def baseStart_1676075 : Nat := 118140960795 + 1676075 * 2 ^ 59
def prefixEnd_1676075 : Nat := 4983230072969 + 3 ^ 40 * 1676075 * 2
def baseEnd_1676075 : Nat := 860632087984635082554377

theorem tailTrace_1676075 : CollatzResearch.WordTrace tailWord_1676075 prefixEnd_1676075 860632087984635082554377 := by
  unfold tailWord_1676075
  simp only [CollatzResearch.WordTrace]
  refine ⟨61131477402874000665517679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40754318268582667110345119 61131477402874000665517679)
  ·
    refine ⟨91697216104311000998276519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61131477402874000665517679 91697216104311000998276519)
    ·
      refine ⟨137545824156466501497414779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91697216104311000998276519 137545824156466501497414779)
      ·
        refine ⟨206318736234699752246122169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137545824156466501497414779 206318736234699752246122169)
        ·
          refine ⟨154739052176024814184591627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206318736234699752246122169 154739052176024814184591627)
          ·
            refine ⟨232108578264037221276887441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154739052176024814184591627 232108578264037221276887441)
            ·
              refine ⟨174081433698027915957665581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232108578264037221276887441 174081433698027915957665581)
              ·
                refine ⟨65280537636760468484124593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174081433698027915957665581 65280537636760468484124593)
                ·
                  refine ⟨48960403227570351363093445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65280537636760468484124593 48960403227570351363093445)
                  ·
                    refine ⟨9180075605169440880580021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48960403227570351363093445 9180075605169440880580021)
                    ·
                      refine ⟨860632087984635082554377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9180075605169440880580021 860632087984635082554377)
                      ·
                        rfl

theorem cell23_1676075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 5].length) (baseStart_1676075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676075 prefixEnd_1676075 := by exact prefixLift 1676075
  have htrace : WordTrace (prefixWord ++ tailWord_1676075) baseStart_1676075 baseEnd_1676075 := by
    simpa [prefixWord, tailWord_1676075, baseEnd_1676075] using wordTrace_append hprefix tailTrace_1676075
  have hstable : (prefixWord ++ tailWord_1676075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676075).length < 2 ^ (prefixWord ++ tailWord_1676075).sum := by decide
  have hdescent : baseEnd_1676075 < baseStart_1676075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676096 : List Nat := [2, 1, 1, 2, 2, 1, 1, 8, 1, 1, 3]
def baseStart_1676096 : Nat := 118140960795 + 1676096 * 2 ^ 59
def prefixEnd_1676096 : Nat := 4983230072969 + 3 ^ 40 * 1676096 * 2
def baseEnd_1676096 : Nat := 860642871078379500391781

theorem tailTrace_1676096 : CollatzResearch.WordTrace tailWord_1676096 prefixEnd_1676096 860642871078379500391781 := by
  unfold tailWord_1676096
  simp only [CollatzResearch.WordTrace]
  refine ⟨30566121667898960626016071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40754828890531947501354761 30566121667898960626016071)
  ·
    refine ⟨45849182501848440939024107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30566121667898960626016071 45849182501848440939024107)
    ·
      refine ⟨68773773752772661408536161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45849182501848440939024107 68773773752772661408536161)
      ·
        refine ⟨51580330314579496056402121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68773773752772661408536161 51580330314579496056402121)
        ·
          refine ⟨38685247735934622042301591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51580330314579496056402121 38685247735934622042301591)
          ·
            refine ⟨58027871603901933063452387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38685247735934622042301591 58027871603901933063452387)
            ·
              refine ⟨87041807405852899595178581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58027871603901933063452387 87041807405852899595178581)
              ·
                refine ⟨1020021180537338667130999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 87041807405852899595178581 1020021180537338667130999)
                ·
                  refine ⟨1530031770806008000696499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020021180537338667130999 1530031770806008000696499)
                  ·
                    refine ⟨2295047656209012001044749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1530031770806008000696499 2295047656209012001044749)
                    ·
                      refine ⟨860642871078379500391781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2295047656209012001044749 860642871078379500391781)
                      ·
                        rfl

theorem cell23_1676096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 1, 1, 3].length) (baseStart_1676096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676096 prefixEnd_1676096 := by exact prefixLift 1676096
  have htrace : WordTrace (prefixWord ++ tailWord_1676096) baseStart_1676096 baseEnd_1676096 := by
    simpa [prefixWord, tailWord_1676096, baseEnd_1676096] using wordTrace_append hprefix tailTrace_1676096
  have hstable : (prefixWord ++ tailWord_1676096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676096).length < 2 ^ (prefixWord ++ tailWord_1676096).sum := by decide
  have hdescent : baseEnd_1676096 < baseStart_1676096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676119 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 4]
def baseStart_1676119 : Nat := 118140960795 + 1676119 * 2 ^ 59
def prefixEnd_1676119 : Nat := 4983230072969 + 3 ^ 40 * 1676119 * 2
def baseEnd_1676119 : Nat := 860654681133432910404175

theorem tailTrace_1676119 : CollatzResearch.WordTrace tailWord_1676119 prefixEnd_1676119 860654681133432910404175 := by
  unfold tailWord_1676119
  simp only [CollatzResearch.WordTrace]
  refine ⟨61133082214714596180119411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40755388143143064120079607 61133082214714596180119411)
  ·
    refine ⟨91699623322071894270179117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61133082214714596180119411 91699623322071894270179117)
    ·
      refine ⟨34387358745776960351317169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91699623322071894270179117 34387358745776960351317169)
      ·
        refine ⟨25790519059332720263487877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34387358745776960351317169 25790519059332720263487877)
        ·
          refine ⟨4835722323624885049403977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25790519059332720263487877 4835722323624885049403977)
          ·
            refine ⟨3626791742718663787052983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4835722323624885049403977 3626791742718663787052983)
            ·
              refine ⟨5440187614077995680579475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3626791742718663787052983 5440187614077995680579475)
              ·
                refine ⟨8160281421116993520869213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5440187614077995680579475 8160281421116993520869213)
                ·
                  refine ⟨3060105532918872570325955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8160281421116993520869213 3060105532918872570325955)
                  ·
                    refine ⟨4590158299378308855488933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3060105532918872570325955 4590158299378308855488933)
                    ·
                      refine ⟨860654681133432910404175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4590158299378308855488933 860654681133432910404175)
                      ·
                        rfl

theorem cell23_1676119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_1676119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676119 prefixEnd_1676119 := by exact prefixLift 1676119
  have htrace : WordTrace (prefixWord ++ tailWord_1676119) baseStart_1676119 baseEnd_1676119 := by
    simpa [prefixWord, tailWord_1676119, baseEnd_1676119] using wordTrace_append hprefix tailTrace_1676119
  have hstable : (prefixWord ++ tailWord_1676119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676119).length < 2 ^ (prefixWord ++ tailWord_1676119).sum := by decide
  have hdescent : baseEnd_1676119 < baseStart_1676119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676139 : List Nat := [1, 1, 1, 1, 2, 2, 4, 5, 1, 2, 3]
def baseStart_1676139 : Nat := 118140960795 + 1676139 * 2 ^ 59
def prefixEnd_1676139 : Nat := 4983230072969 + 3 ^ 40 * 1676139 * 2
def baseEnd_1676139 : Nat := 860664950746522832154083

theorem tailTrace_1676139 : CollatzResearch.WordTrace tailWord_1676139 prefixEnd_1676139 860664950746522832154083 := by
  unfold tailWord_1676139
  simp only [CollatzResearch.WordTrace]
  refine ⟨61133811674642139595847471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40755874449761426397231647 61133811674642139595847471)
  ·
    refine ⟨91700717511963209393771207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61133811674642139595847471 91700717511963209393771207)
    ·
      refine ⟨137551076267944814090656811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91700717511963209393771207 137551076267944814090656811)
      ·
        refine ⟨206326614401917221135985217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137551076267944814090656811 206326614401917221135985217)
        ·
          refine ⟨154744960801437915851988913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206326614401917221135985217 154744960801437915851988913)
          ·
            refine ⟨116058720601078436888991685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154744960801437915851988913 116058720601078436888991685)
            ·
              refine ⟨21761010112702206916685941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116058720601078436888991685 21761010112702206916685941)
              ·
                refine ⟨2040094698065831898439307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21761010112702206916685941 2040094698065831898439307)
                ·
                  refine ⟨3060142047098747847658961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040094698065831898439307 3060142047098747847658961)
                  ·
                    refine ⟨2295106535324060885744221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3060142047098747847658961 2295106535324060885744221)
                    ·
                      refine ⟨860664950746522832154083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2295106535324060885744221 860664950746522832154083)
                      ·
                        rfl

theorem cell23_1676139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 2, 3].length) (baseStart_1676139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676139 prefixEnd_1676139 := by exact prefixLift 1676139
  have htrace : WordTrace (prefixWord ++ tailWord_1676139) baseStart_1676139 baseEnd_1676139 := by
    simpa [prefixWord, tailWord_1676139, baseEnd_1676139] using wordTrace_append hprefix tailTrace_1676139
  have hstable : (prefixWord ++ tailWord_1676139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676139).length < 2 ^ (prefixWord ++ tailWord_1676139).sum := by decide
  have hdescent : baseEnd_1676139 < baseStart_1676139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676142 : List Nat := [4, 1, 2, 3, 13]
def baseStart_1676142 : Nat := 118140960795 + 1676142 * 2 ^ 59
def prefixEnd_1676142 : Nat := 4983230072969 + 3 ^ 40 * 1676142 * 2
def baseEnd_1676142 : Nat := 1180612470766099204961

theorem tailTrace_1676142 : CollatzResearch.WordTrace tailWord_1676142 prefixEnd_1676142 1180612470766099204961 := by
  unfold tailWord_1676142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7641740136703908888525835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40755947395754180738804453 7641740136703908888525835)
  ·
    refine ⟨11462610205055863332788753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7641740136703908888525835 11462610205055863332788753)
    ·
      refine ⟨8596957653791897499591565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11462610205055863332788753 8596957653791897499591565)
      ·
        refine ⟨3223859120171961562346837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8596957653791897499591565 3223859120171961562346837)
        ·
          refine ⟨1180612470766099204961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 3223859120171961562346837 1180612470766099204961)
          ·
            rfl

theorem cell23_1676142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 13].length) (baseStart_1676142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676142 prefixEnd_1676142 := by exact prefixLift 1676142
  have htrace : WordTrace (prefixWord ++ tailWord_1676142) baseStart_1676142 baseEnd_1676142 := by
    simpa [prefixWord, tailWord_1676142, baseEnd_1676142] using wordTrace_append hprefix tailTrace_1676142
  have hstable : (prefixWord ++ tailWord_1676142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676142).length < 2 ^ (prefixWord ++ tailWord_1676142).sum := by decide
  have hdescent : baseEnd_1676142 < baseStart_1676142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676169 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 1, 3, 3]
def baseStart_1676169 : Nat := 118140960795 + 1676169 * 2 ^ 59
def prefixEnd_1676169 : Nat := 4983230072969 + 3 ^ 40 * 1676169 * 2
def baseEnd_1676169 : Nat := 860680355166157714778945

theorem tailTrace_1676169 : CollatzResearch.WordTrace tailWord_1676169 prefixEnd_1676169 860680355166157714778945 := by
  unfold tailWord_1676169
  simp only [CollatzResearch.WordTrace]
  refine ⟨61134905864533454719439561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40756603909688969812959707 61134905864533454719439561)
  ·
    refine ⟨45851179398400091039579671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61134905864533454719439561 45851179398400091039579671)
    ·
      refine ⟨68776769097600136559369507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45851179398400091039579671 68776769097600136559369507)
      ·
        refine ⟨103165153646400204839054261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68776769097600136559369507 103165153646400204839054261)
        ·
          refine ⟨9671733154350019203661337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103165153646400204839054261 9671733154350019203661337)
          ·
            refine ⟨7253799865762514402746003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9671733154350019203661337 7253799865762514402746003)
            ·
              refine ⟨10880699798643771604119005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7253799865762514402746003 10880699798643771604119005)
              ·
                refine ⟨4080262424491414351544627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10880699798643771604119005 4080262424491414351544627)
                ·
                  refine ⟨6120393636737121527316941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4080262424491414351544627 6120393636737121527316941)
                  ·
                    refine ⟨2295147613776420572743853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6120393636737121527316941 2295147613776420572743853)
                    ·
                      refine ⟨860680355166157714778945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2295147613776420572743853 860680355166157714778945)
                      ·
                        rfl

theorem cell23_1676169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 3, 3].length) (baseStart_1676169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676169 prefixEnd_1676169 := by exact prefixLift 1676169
  have htrace : WordTrace (prefixWord ++ tailWord_1676169) baseStart_1676169 baseEnd_1676169 := by
    simpa [prefixWord, tailWord_1676169, baseEnd_1676169] using wordTrace_append hprefix tailTrace_1676169
  have hstable : (prefixWord ++ tailWord_1676169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676169).length < 2 ^ (prefixWord ++ tailWord_1676169).sum := by decide
  have hdescent : baseEnd_1676169 < baseStart_1676169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676214 : List Nat := [5, 1, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1676214 : Nat := 118140960795 + 1676214 * 2 ^ 59
def prefixEnd_1676214 : Nat := 4983230072969 + 3 ^ 40 * 1676214 * 2
def baseEnd_1676214 : Nat := 286901153931870012905413

theorem tailTrace_1676214 : CollatzResearch.WordTrace tailWord_1676214 prefixEnd_1676214 286901153931870012905413 := by
  unfold tailWord_1676214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3821034196835651712801731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40757698099580284936551797 3821034196835651712801731)
  ·
    refine ⟨5731551295253477569202597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3821034196835651712801731 5731551295253477569202597)
    ·
      refine ⟨1074665867860027044225487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5731551295253477569202597 1074665867860027044225487)
      ·
        refine ⟨1611998801790040566338231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074665867860027044225487 1611998801790040566338231)
        ·
          refine ⟨2417998202685060849507347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611998801790040566338231 2417998202685060849507347)
          ·
            refine ⟨3626997304027591274261021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2417998202685060849507347 3626997304027591274261021)
            ·
              refine ⟨1360123989010346727847883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3626997304027591274261021 1360123989010346727847883)
              ·
                refine ⟨2040185983515520091771825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360123989010346727847883 2040185983515520091771825)
                ·
                  refine ⟨1530139487636640068828869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2040185983515520091771825 1530139487636640068828869)
                  ·
                    refine ⟨286901153931870012905413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1530139487636640068828869 286901153931870012905413)
                    ·
                      rfl

theorem cell23_1676214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1676214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676214 prefixEnd_1676214 := by exact prefixLift 1676214
  have htrace : WordTrace (prefixWord ++ tailWord_1676214) baseStart_1676214 baseEnd_1676214 := by
    simpa [prefixWord, tailWord_1676214, baseEnd_1676214] using wordTrace_append hprefix tailTrace_1676214
  have hstable : (prefixWord ++ tailWord_1676214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676214).length < 2 ^ (prefixWord ++ tailWord_1676214).sum := by decide
  have hdescent : baseEnd_1676214 < baseStart_1676214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676246 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1676246 : Nat := 118140960795 + 1676246 * 2 ^ 59
def prefixEnd_1676246 : Nat := 4983230072969 + 3 ^ 40 * 1676246 * 2
def baseEnd_1676246 : Nat := 860719893176553913516091

theorem tailTrace_1676246 : CollatzResearch.WordTrace tailWord_1676246 prefixEnd_1676246 860719893176553913516091 := by
  unfold tailWord_1676246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3821107142828406054374537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40758476190169664579995061 3821107142828406054374537)
  ·
    refine ⟨2865830357121304540780903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3821107142828406054374537 2865830357121304540780903)
    ·
      refine ⟨4298745535681956811171355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2865830357121304540780903 4298745535681956811171355)
      ·
        refine ⟨6448118303522935216757033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4298745535681956811171355 6448118303522935216757033)
        ·
          refine ⟨4836088727642201412567775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6448118303522935216757033 4836088727642201412567775)
          ·
            refine ⟨7254133091463302118851663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836088727642201412567775 7254133091463302118851663)
            ·
              refine ⟨10881199637194953178277495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7254133091463302118851663 10881199637194953178277495)
              ·
                refine ⟨16321799455792429767416243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10881199637194953178277495 16321799455792429767416243)
                ·
                  refine ⟨24482699183688644651124365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16321799455792429767416243 24482699183688644651124365)
                  ·
                    refine ⟨9181012193883241744171637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24482699183688644651124365 9181012193883241744171637)
                    ·
                      refine ⟨860719893176553913516091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9181012193883241744171637 860719893176553913516091)
                      ·
                        rfl

theorem cell23_1676246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1676246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676246 prefixEnd_1676246 := by exact prefixLift 1676246
  have htrace : WordTrace (prefixWord ++ tailWord_1676246) baseStart_1676246 baseEnd_1676246 := by
    simpa [prefixWord, tailWord_1676246, baseEnd_1676246] using wordTrace_append hprefix tailTrace_1676246
  have hstable : (prefixWord ++ tailWord_1676246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676246).length < 2 ^ (prefixWord ++ tailWord_1676246).sum := by decide
  have hdescent : baseEnd_1676246 < baseStart_1676246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676266 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 7]
def baseStart_1676266 : Nat := 118140960795 + 1676266 * 2 ^ 59
def prefixEnd_1676266 : Nat := 4983230072969 + 3 ^ 40 * 1676266 * 2
def baseEnd_1676266 : Nat := 95636684754404870585111

theorem tailTrace_1676266 : CollatzResearch.WordTrace tailWord_1676266 prefixEnd_1676266 95636684754404870585111 := by
  unfold tailWord_1676266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15284610936295510071430163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40758962496788026857147101 15284610936295510071430163)
  ·
    refine ⟨22926916404443265107145245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15284610936295510071430163 22926916404443265107145245)
    ·
      refine ⟨8597593651666224415179467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22926916404443265107145245 8597593651666224415179467)
      ·
        refine ⟨12896390477499336622769201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8597593651666224415179467 12896390477499336622769201)
        ·
          refine ⟨9672292858124502467076901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12896390477499336622769201 9672292858124502467076901)
          ·
            refine ⟨1813554910898344212576919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9672292858124502467076901 1813554910898344212576919)
            ·
              refine ⟨2720332366347516318865379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813554910898344212576919 2720332366347516318865379)
              ·
                refine ⟨4080498549521274478298069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720332366347516318865379 4080498549521274478298069)
                ·
                  refine ⟨95636684754404870585111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4080498549521274478298069 95636684754404870585111)
                  ·
                    rfl

theorem cell23_1676266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 7].length) (baseStart_1676266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676266 prefixEnd_1676266 := by exact prefixLift 1676266
  have htrace : WordTrace (prefixWord ++ tailWord_1676266) baseStart_1676266 baseEnd_1676266 := by
    simpa [prefixWord, tailWord_1676266, baseEnd_1676266] using wordTrace_append hprefix tailTrace_1676266
  have hstable : (prefixWord ++ tailWord_1676266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676266).length < 2 ^ (prefixWord ++ tailWord_1676266).sum := by decide
  have hdescent : baseEnd_1676266 < baseStart_1676266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676296 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 2, 5]
def baseStart_1676296 : Nat := 118140960795 + 1676296 * 2 ^ 59
def prefixEnd_1676296 : Nat := 4983230072969 + 3 ^ 40 * 1676296 * 2
def baseEnd_1676296 : Nat := 286915189069759572630287

theorem tailTrace_1676296 : CollatzResearch.WordTrace tailWord_1676296 prefixEnd_1676296 286915189069759572630287 := by
  unfold tailWord_1676296
  simp only [CollatzResearch.WordTrace]
  refine ⟨30569768967536677704656371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40759691956715570272875161 30569768967536677704656371)
  ·
    refine ⟨45854653451305016556984557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30569768967536677704656371 45854653451305016556984557)
    ·
      refine ⟨17195495044239381208869209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45854653451305016556984557 17195495044239381208869209)
      ·
        refine ⟨12896621283179535906651907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17195495044239381208869209 12896621283179535906651907)
        ·
          refine ⟨19344931924769303859977861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12896621283179535906651907 19344931924769303859977861)
          ·
            refine ⟨3627174735894244473745849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19344931924769303859977861 3627174735894244473745849)
            ·
              refine ⟨2720381051920683355309387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3627174735894244473745849 2720381051920683355309387)
              ·
                refine ⟨4080571577881025032964081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720381051920683355309387 4080571577881025032964081)
                ·
                  refine ⟨3060428683410768774723061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4080571577881025032964081 3060428683410768774723061)
                  ·
                    refine ⟨286915189069759572630287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3060428683410768774723061 286915189069759572630287)
                    ·
                      rfl

theorem cell23_1676296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_1676296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676296 prefixEnd_1676296 := by exact prefixLift 1676296
  have htrace : WordTrace (prefixWord ++ tailWord_1676296) baseStart_1676296 baseEnd_1676296 := by
    simpa [prefixWord, tailWord_1676296, baseEnd_1676296] using wordTrace_append hprefix tailTrace_1676296
  have hstable : (prefixWord ++ tailWord_1676296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676296).length < 2 ^ (prefixWord ++ tailWord_1676296).sum := by decide
  have hdescent : baseEnd_1676296 < baseStart_1676296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676317 : List Nat := [1, 4, 2, 2, 4, 1, 2, 2, 5]
def baseStart_1676317 : Nat := 118140960795 + 1676317 * 2 ^ 59
def prefixEnd_1676317 : Nat := 4983230072969 + 3 ^ 40 * 1676317 * 2
def baseEnd_1676317 : Nat := 95639594478113681747585

theorem tailTrace_1676317 : CollatzResearch.WordTrace tailWord_1676317 prefixEnd_1676317 95639594478113681747585 := by
  unfold tailWord_1676317
  simp only [CollatzResearch.WordTrace]
  refine ⟨61140303867997275995827205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40760202578664850663884803 61140303867997275995827205)
  ·
    refine ⟨11463806975249489249217601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61140303867997275995827205 11463806975249489249217601)
    ·
      refine ⟨8597855231437116936913201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11463806975249489249217601 8597855231437116936913201)
      ·
        refine ⟨6448391423577837702684901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8597855231437116936913201 6448391423577837702684901)
        ·
          refine ⟨1209073391920844569253419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6448391423577837702684901 1209073391920844569253419)
          ·
            refine ⟨1813610087881266853880129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209073391920844569253419 1813610087881266853880129)
            ·
              refine ⟨1360207565910950140410097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1813610087881266853880129 1360207565910950140410097)
              ·
                refine ⟨1020155674433212605307573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1360207565910950140410097 1020155674433212605307573)
                ·
                  refine ⟨95639594478113681747585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1020155674433212605307573 95639594478113681747585)
                  ·
                    rfl

theorem cell23_1676317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_1676317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676317 prefixEnd_1676317 := by exact prefixLift 1676317
  have htrace : WordTrace (prefixWord ++ tailWord_1676317) baseStart_1676317 baseEnd_1676317 := by
    simpa [prefixWord, tailWord_1676317, baseEnd_1676317] using wordTrace_append hprefix tailTrace_1676317
  have hstable : (prefixWord ++ tailWord_1676317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676317).length < 2 ^ (prefixWord ++ tailWord_1676317).sum := by decide
  have hdescent : baseEnd_1676317 < baseStart_1676317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676350 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_1676350 : Nat := 118140960795 + 1676350 * 2 ^ 59
def prefixEnd_1676350 : Nat := 4983230072969 + 3 ^ 40 * 1676350 * 2
def baseEnd_1676350 : Nat := 860773295164621506615613

theorem tailTrace_1676350 : CollatzResearch.WordTrace tailWord_1676350 prefixEnd_1676350 860773295164621506615613 := by
  unfold tailWord_1676350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7642688434609715328972313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40761004984585148421185669 7642688434609715328972313)
  ·
    refine ⟨5732016325957286496729235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7642688434609715328972313 5732016325957286496729235)
    ·
      refine ⟨8598024488935929745093853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5732016325957286496729235 8598024488935929745093853)
      ·
        refine ⟨3224259183350973654410195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8598024488935929745093853 3224259183350973654410195)
        ·
          refine ⟨4836388775026460481615293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3224259183350973654410195 4836388775026460481615293)
          ·
            refine ⟨1813645790634922680605735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4836388775026460481615293 1813645790634922680605735)
            ·
              refine ⟨2720468685952384020908603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813645790634922680605735 2720468685952384020908603)
              ·
                refine ⟨4080703028928576031362905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720468685952384020908603 4080703028928576031362905)
                ·
                  refine ⟨3060527271696432023522179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4080703028928576031362905 3060527271696432023522179)
                  ·
                    refine ⟨4590790907544648035283269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3060527271696432023522179 4590790907544648035283269)
                    ·
                      refine ⟨860773295164621506615613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4590790907544648035283269 860773295164621506615613)
                      ·
                        rfl

theorem cell23_1676350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_1676350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676350 prefixEnd_1676350 := by exact prefixLift 1676350
  have htrace : WordTrace (prefixWord ++ tailWord_1676350) baseStart_1676350 baseEnd_1676350 := by
    simpa [prefixWord, tailWord_1676350, baseEnd_1676350] using wordTrace_append hprefix tailTrace_1676350
  have hstable : (prefixWord ++ tailWord_1676350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676350).length < 2 ^ (prefixWord ++ tailWord_1676350).sum := by decide
  have hdescent : baseEnd_1676350 < baseStart_1676350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676353 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1676353 : Nat := 118140960795 + 1676353 * 2 ^ 59
def prefixEnd_1676353 : Nat := 4983230072969 + 3 ^ 40 * 1676353 * 2
def baseEnd_1676353 : Nat := 860774835606584994878099

theorem tailTrace_1676353 : CollatzResearch.WordTrace tailWord_1676353 prefixEnd_1676353 860774835606584994878099 := by
  unfold tailWord_1676353
  simp only [CollatzResearch.WordTrace]
  refine ⟨61141616895866854144137713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40761077930577902762758475 61141616895866854144137713)
  ·
    refine ⟨45856212671900140608103285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61141616895866854144137713 45856212671900140608103285)
    ·
      refine ⟨4299019937990638182009683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45856212671900140608103285 4299019937990638182009683)
      ·
        refine ⟨6448529906985957273014525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4299019937990638182009683 6448529906985957273014525)
        ·
          refine ⟨2418198715119733977380447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6448529906985957273014525 2418198715119733977380447)
          ·
            refine ⟨3627298072679600966070671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2418198715119733977380447 3627298072679600966070671)
            ·
              refine ⟨5440947109019401449106007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3627298072679600966070671 5440947109019401449106007)
              ·
                refine ⟨8161420663529102173659011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5440947109019401449106007 8161420663529102173659011)
                ·
                  refine ⟨12242130995293653260488517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8161420663529102173659011 12242130995293653260488517)
                  ·
                    refine ⟨2295399561617559986341597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12242130995293653260488517 2295399561617559986341597)
                    ·
                      refine ⟨860774835606584994878099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2295399561617559986341597 860774835606584994878099)
                      ·
                        rfl

theorem cell23_1676353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1676353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676353 prefixEnd_1676353 := by exact prefixLift 1676353
  have htrace : WordTrace (prefixWord ++ tailWord_1676353) baseStart_1676353 baseEnd_1676353 := by
    simpa [prefixWord, tailWord_1676353, baseEnd_1676353] using wordTrace_append hprefix tailTrace_1676353
  have hstable : (prefixWord ++ tailWord_1676353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676353).length < 2 ^ (prefixWord ++ tailWord_1676353).sum := by decide
  have hdescent : baseEnd_1676353 < baseStart_1676353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676383 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 3, 1, 3]
def baseStart_1676383 : Nat := 118140960795 + 1676383 * 2 ^ 59
def prefixEnd_1676383 : Nat := 4983230072969 + 3 ^ 40 * 1676383 * 2
def baseEnd_1676383 : Nat := 860790240026219877502961

theorem tailTrace_1676383 : CollatzResearch.WordTrace tailWord_1676383 prefixEnd_1676383 860790240026219877502961 := by
  unfold tailWord_1676383
  simp only [CollatzResearch.WordTrace]
  refine ⟨61142711085758169267729803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40761807390505446178486535 61142711085758169267729803)
  ·
    refine ⟨91714066628637253901594705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61142711085758169267729803 91714066628637253901594705)
    ·
      refine ⟨68785549971477940426196029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91714066628637253901594705 68785549971477940426196029)
      ·
        refine ⟨25794581239304227659823511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68785549971477940426196029 25794581239304227659823511)
        ·
          refine ⟨38691871858956341489735267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25794581239304227659823511 38691871858956341489735267)
          ·
            refine ⟨58037807788434512234602901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38691871858956341489735267 58037807788434512234602901)
            ·
              refine ⟨2720522240082867760997011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58037807788434512234602901 2720522240082867760997011)
              ·
                refine ⟨4080783360124301641495517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720522240082867760997011 4080783360124301641495517)
                ·
                  refine ⟨1530293760046613115560819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4080783360124301641495517 1530293760046613115560819)
                  ·
                    refine ⟨2295440640069919673341229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1530293760046613115560819 2295440640069919673341229)
                    ·
                      refine ⟨860790240026219877502961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2295440640069919673341229 860790240026219877502961)
                      ·
                        rfl

theorem cell23_1676383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_1676383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676383 prefixEnd_1676383 := by exact prefixLift 1676383
  have htrace : WordTrace (prefixWord ++ tailWord_1676383) baseStart_1676383 baseEnd_1676383 := by
    simpa [prefixWord, tailWord_1676383, baseEnd_1676383] using wordTrace_append hprefix tailTrace_1676383
  have hstable : (prefixWord ++ tailWord_1676383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676383).length < 2 ^ (prefixWord ++ tailWord_1676383).sum := by decide
  have hdescent : baseEnd_1676383 < baseStart_1676383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676416 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 4, 4]
def baseStart_1676416 : Nat := 118140960795 + 1676416 * 2 ^ 59
def prefixEnd_1676416 : Nat := 4983230072969 + 3 ^ 40 * 1676416 * 2
def baseEnd_1676416 : Nat := 286935728295939416130103

theorem tailTrace_1676416 : CollatzResearch.WordTrace tailWord_1676416 prefixEnd_1676416 286935728295939416130103 := by
  unfold tailWord_1676416
  simp only [CollatzResearch.WordTrace]
  refine ⟨30571957347319307951840551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40762609796425743935787401 30571957347319307951840551)
  ·
    refine ⟨45857936020978961927760827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30571957347319307951840551 45857936020978961927760827)
    ·
      refine ⟨68786904031468442891641241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45857936020978961927760827 68786904031468442891641241)
      ·
        refine ⟨51590178023601332168730931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68786904031468442891641241 51590178023601332168730931)
        ·
          refine ⟨77385267035401998253096397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51590178023601332168730931 77385267035401998253096397)
          ·
            refine ⟨29019475138275749344911149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77385267035401998253096397 29019475138275749344911149)
            ·
              refine ⟨10882303176853406004341681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29019475138275749344911149 10882303176853406004341681)
              ·
                refine ⟨8161727382640054503256261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10882303176853406004341681 8161727382640054503256261)
                ·
                  refine ⟨1530323884245010219360549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8161727382640054503256261 1530323884245010219360549)
                  ·
                    refine ⟨286935728295939416130103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1530323884245010219360549 286935728295939416130103)
                    ·
                      rfl

theorem cell23_1676416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 4, 4].length) (baseStart_1676416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676416 prefixEnd_1676416 := by exact prefixLift 1676416
  have htrace : WordTrace (prefixWord ++ tailWord_1676416) baseStart_1676416 baseEnd_1676416 := by
    simpa [prefixWord, tailWord_1676416, baseEnd_1676416] using wordTrace_append hprefix tailTrace_1676416
  have hstable : (prefixWord ++ tailWord_1676416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676416).length < 2 ^ (prefixWord ++ tailWord_1676416).sum := by decide
  have hdescent : baseEnd_1676416 < baseStart_1676416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676417 : List Nat := [1, 2, 4, 2, 2, 1, 3, 3, 1, 1, 3]
def baseStart_1676417 : Nat := 118140960795 + 1676417 * 2 ^ 59
def prefixEnd_1676417 : Nat := 4983230072969 + 3 ^ 40 * 1676417 * 2
def baseEnd_1676417 : Nat := 860807698368472744477805

theorem tailTrace_1676417 : CollatzResearch.WordTrace tailWord_1676417 prefixEnd_1676417 860807698368472744477805 := by
  unfold tailWord_1676417
  simp only [CollatzResearch.WordTrace]
  refine ⟨61143951167634993074467505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40762634111756662049645003 61143951167634993074467505)
  ·
    refine ⟨45857963375726244805850629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61143951167634993074467505 45857963375726244805850629)
    ·
      refine ⟨8598368132948670901096993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45857963375726244805850629 8598368132948670901096993)
      ·
        refine ⟨6448776099711503175822745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8598368132948670901096993 6448776099711503175822745)
        ·
          refine ⟨4836582074783627381867059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6448776099711503175822745 4836582074783627381867059)
          ·
            refine ⟨7254873112175441072800589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836582074783627381867059 7254873112175441072800589)
            ·
              refine ⟨2720577417065790402300221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7254873112175441072800589 2720577417065790402300221)
              ·
                refine ⟨1020216531399671400862583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2720577417065790402300221 1020216531399671400862583)
                ·
                  refine ⟨1530324797099507101293875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020216531399671400862583 1530324797099507101293875)
                  ·
                    refine ⟨2295487195649260651940813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1530324797099507101293875 2295487195649260651940813)
                    ·
                      refine ⟨860807698368472744477805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2295487195649260651940813 860807698368472744477805)
                      ·
                        rfl

theorem cell23_1676417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_1676417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676417 prefixEnd_1676417 := by exact prefixLift 1676417
  have htrace : WordTrace (prefixWord ++ tailWord_1676417) baseStart_1676417 baseEnd_1676417 := by
    simpa [prefixWord, tailWord_1676417, baseEnd_1676417] using wordTrace_append hprefix tailTrace_1676417
  have hstable : (prefixWord ++ tailWord_1676417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676417).length < 2 ^ (prefixWord ++ tailWord_1676417).sum := by decide
  have hdescent : baseEnd_1676417 < baseStart_1676417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676434 : List Nat := [3, 2, 3, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_1676434 : Nat := 118140960795 + 1676434 * 2 ^ 59
def prefixEnd_1676434 : Nat := 4983230072969 + 3 ^ 40 * 1676434 * 2
def baseEnd_1676434 : Nat := 860816427539599177965227

theorem tailTrace_1676434 : CollatzResearch.WordTrace tailWord_1676434 prefixEnd_1676434 860816427539599177965227 := by
  unfold tailWord_1676434
  simp only [CollatzResearch.WordTrace]
  refine ⟨15286142802143351244459089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40763047472382269985224237 15286142802143351244459089)
  ·
    refine ⟨11464607101607513433344317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15286142802143351244459089 11464607101607513433344317)
    ·
      refine ⟨4299227663102817537504119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11464607101607513433344317 4299227663102817537504119)
      ·
        refine ⟨6448841494654226306256179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4299227663102817537504119 6448841494654226306256179)
        ·
          refine ⟨9673262241981339459384269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6448841494654226306256179 9673262241981339459384269)
          ·
            refine ⟨3627473340743002297269101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9673262241981339459384269 3627473340743002297269101)
            ·
              refine ⟨1360302502778625861475913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3627473340743002297269101 1360302502778625861475913)
              ·
                refine ⟨1020226877083969396106935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1360302502778625861475913 1020226877083969396106935)
                ·
                  refine ⟨1530340315625954094160403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020226877083969396106935 1530340315625954094160403)
                  ·
                    refine ⟨2295510473438931141240605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1530340315625954094160403 2295510473438931141240605)
                    ·
                      refine ⟨860816427539599177965227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2295510473438931141240605 860816427539599177965227)
                      ·
                        rfl

theorem cell23_1676434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_1676434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676434 prefixEnd_1676434 := by exact prefixLift 1676434
  have htrace : WordTrace (prefixWord ++ tailWord_1676434) baseStart_1676434 baseEnd_1676434 := by
    simpa [prefixWord, tailWord_1676434, baseEnd_1676434] using wordTrace_append hprefix tailTrace_1676434
  have hstable : (prefixWord ++ tailWord_1676434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676434).length < 2 ^ (prefixWord ++ tailWord_1676434).sum := by decide
  have hdescent : baseEnd_1676434 < baseStart_1676434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676473 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 1, 3, 3]
def baseStart_1676473 : Nat := 118140960795 + 1676473 * 2 ^ 59
def prefixEnd_1676473 : Nat := 4983230072969 + 3 ^ 40 * 1676473 * 2
def baseEnd_1676473 : Nat := 860836453285124525377547

theorem tailTrace_1676473 : CollatzResearch.WordTrace tailWord_1676473 prefixEnd_1676473 860836453285124525377547 := by
  unfold tailWord_1676473
  simp only [CollatzResearch.WordTrace]
  refine ⟨61145993655432114638506073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40763995770288076425670715 61145993655432114638506073)
  ·
    refine ⟨45859495241574085978879555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61145993655432114638506073 45859495241574085978879555)
    ·
      refine ⟨68789242862361128968319333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45859495241574085978879555 68789242862361128968319333)
      ·
        refine ⟨12897983036692711681559875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68789242862361128968319333 12897983036692711681559875)
        ·
          refine ⟨19346974555039067522339813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12897983036692711681559875 19346974555039067522339813)
          ·
            refine ⟨3627557729069825160438715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19346974555039067522339813 3627557729069825160438715)
            ·
              refine ⟨5441336593604737740658073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3627557729069825160438715 5441336593604737740658073)
              ·
                refine ⟨4081002445203553305493555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5441336593604737740658073 4081002445203553305493555)
                ·
                  refine ⟨6121503667805329958240333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4081002445203553305493555 6121503667805329958240333)
                  ·
                    refine ⟨2295563875426998734340125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6121503667805329958240333 2295563875426998734340125)
                    ·
                      refine ⟨860836453285124525377547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2295563875426998734340125 860836453285124525377547)
                      ·
                        rfl

theorem cell23_1676473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_1676473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676473 prefixEnd_1676473 := by exact prefixLift 1676473
  have htrace : WordTrace (prefixWord ++ tailWord_1676473) baseStart_1676473 baseEnd_1676473 := by
    simpa [prefixWord, tailWord_1676473, baseEnd_1676473] using wordTrace_append hprefix tailTrace_1676473
  have hstable : (prefixWord ++ tailWord_1676473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676473).length < 2 ^ (prefixWord ++ tailWord_1676473).sum := by decide
  have hdescent : baseEnd_1676473 < baseStart_1676473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676490 : List Nat := [3, 1, 2, 1, 3, 2, 1, 4, 2, 1, 3]
def baseStart_1676490 : Nat := 118140960795 + 1676490 * 2 ^ 59
def prefixEnd_1676490 : Nat := 4983230072969 + 3 ^ 40 * 1676490 * 2
def baseEnd_1676490 : Nat := 860845182456250958864969

theorem tailTrace_1676490 : CollatzResearch.WordTrace tailWord_1676490 prefixEnd_1676490 860845182456250958864969 := by
  unfold tailWord_1676490
  simp only [CollatzResearch.WordTrace]
  refine ⟨15286653424092631635468731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40764409130913684361249949 15286653424092631635468731)
  ·
    refine ⟨22929980136138947453203097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15286653424092631635468731 22929980136138947453203097)
    ·
      refine ⟨17197485102104210589902323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22929980136138947453203097 17197485102104210589902323)
      ·
        refine ⟨25796227653156315884853485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17197485102104210589902323 25796227653156315884853485)
        ·
          refine ⟨9673585369933618456820057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25796227653156315884853485 9673585369933618456820057)
          ·
            refine ⟨7255189027450213842615043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9673585369933618456820057 7255189027450213842615043)
            ·
              refine ⟨10882783541175320763922565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7255189027450213842615043 10882783541175320763922565)
              ·
                refine ⟨2040521913970372643235481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10882783541175320763922565 2040521913970372643235481)
                ·
                  refine ⟨1530391435477779482426611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2040521913970372643235481 1530391435477779482426611)
                  ·
                    refine ⟨2295587153216669223639917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1530391435477779482426611 2295587153216669223639917)
                    ·
                      refine ⟨860845182456250958864969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2295587153216669223639917 860845182456250958864969)
                      ·
                        rfl

theorem cell23_1676490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_1676490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676490 prefixEnd_1676490 := by exact prefixLift 1676490
  have htrace : WordTrace (prefixWord ++ tailWord_1676490) baseStart_1676490 baseEnd_1676490 := by
    simpa [prefixWord, tailWord_1676490, baseEnd_1676490] using wordTrace_append hprefix tailTrace_1676490
  have hstable : (prefixWord ++ tailWord_1676490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676490).length < 2 ^ (prefixWord ++ tailWord_1676490).sum := by decide
  have hdescent : baseEnd_1676490 < baseStart_1676490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676516 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_1676516 : Nat := 118140960795 + 1676516 * 2 ^ 59
def prefixEnd_1676516 : Nat := 4983230072969 + 3 ^ 40 * 1676516 * 2
def baseEnd_1676516 : Nat := 860858532953267857139849

theorem tailTrace_1676516 : CollatzResearch.WordTrace tailWord_1676516 prefixEnd_1676516 860858532953267857139849 := by
  unfold tailWord_1676516
  simp only [CollatzResearch.WordTrace]
  refine ⟨30573780997138166491160701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40765041329517555321547601 30573780997138166491160701)
  ·
    refine ⟨11465167873926812434185263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30573780997138166491160701 11465167873926812434185263)
    ·
      refine ⟨17197751810890218651277895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11465167873926812434185263 17197751810890218651277895)
      ·
        refine ⟨25796627716335327976916843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17197751810890218651277895 25796627716335327976916843)
        ·
          refine ⟨38694941574502991965375265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25796627716335327976916843 38694941574502991965375265)
          ·
            refine ⟨29021206180877243974031449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38694941574502991965375265 29021206180877243974031449)
            ·
              refine ⟨21765904635657932980523587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29021206180877243974031449 21765904635657932980523587)
              ·
                refine ⟨32648856953486899470785381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21765904635657932980523587 32648856953486899470785381)
                ·
                  refine ⟨6121660678778793650772259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32648856953486899470785381 6121660678778793650772259)
                  ·
                    refine ⟨9182491018168190476158389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6121660678778793650772259 9182491018168190476158389)
                    ·
                      refine ⟨860858532953267857139849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9182491018168190476158389 860858532953267857139849)
                      ·
                        rfl

theorem cell23_1676516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_1676516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676516 prefixEnd_1676516 := by exact prefixLift 1676516
  have htrace : WordTrace (prefixWord ++ tailWord_1676516) baseStart_1676516 baseEnd_1676516 := by
    simpa [prefixWord, tailWord_1676516, baseEnd_1676516] using wordTrace_append hprefix tailTrace_1676516
  have hstable : (prefixWord ++ tailWord_1676516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676516).length < 2 ^ (prefixWord ++ tailWord_1676516).sum := by decide
  have hdescent : baseEnd_1676516 < baseStart_1676516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676547 : List Nat := [1, 1, 1, 3, 2, 4, 3, 2, 2, 2, 2]
def baseStart_1676547 : Nat := 118140960795 + 1676547 * 2 ^ 59
def prefixEnd_1676547 : Nat := 4983230072969 + 3 ^ 40 * 1676547 * 2
def baseEnd_1676547 : Nat := 860874450853557235852207

theorem tailTrace_1676547 : CollatzResearch.WordTrace tailWord_1676547 prefixEnd_1676547 860874450853557235852207 := by
  unfold tailWord_1676547
  simp only [CollatzResearch.WordTrace]
  refine ⟨61148692657164025276699895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40765795104776016851133263 61148692657164025276699895)
  ·
    refine ⟨91723038985746037915049843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61148692657164025276699895 91723038985746037915049843)
    ·
      refine ⟨137584558478619056872574765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91723038985746037915049843 137584558478619056872574765)
      ·
        refine ⟨51594209429482146327215537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137584558478619056872574765 51594209429482146327215537)
        ·
          refine ⟨38695657072111609745411653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51594209429482146327215537 38695657072111609745411653)
          ·
            refine ⟨7255435701020926827264685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38695657072111609745411653 7255435701020926827264685)
            ·
              refine ⟨2720788387882847560224257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7255435701020926827264685 2720788387882847560224257)
              ·
                refine ⟨2040591290912135670168193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2720788387882847560224257 2040591290912135670168193)
                ·
                  refine ⟨1530443468184101752626145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2040591290912135670168193 1530443468184101752626145)
                  ·
                    refine ⟨1147832601138076314469609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1530443468184101752626145 1147832601138076314469609)
                    ·
                      refine ⟨860874450853557235852207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1147832601138076314469609 860874450853557235852207)
                      ·
                        rfl

theorem cell23_1676547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 2, 2].length) (baseStart_1676547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676547 prefixEnd_1676547 := by exact prefixLift 1676547
  have htrace : WordTrace (prefixWord ++ tailWord_1676547) baseStart_1676547 baseEnd_1676547 := by
    simpa [prefixWord, tailWord_1676547, baseEnd_1676547] using wordTrace_append hprefix tailTrace_1676547
  have hstable : (prefixWord ++ tailWord_1676547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676547).length < 2 ^ (prefixWord ++ tailWord_1676547).sum := by decide
  have hdescent : baseEnd_1676547 < baseStart_1676547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676553 : List Nat := [1, 2, 1, 1, 3, 3, 1, 6, 5]
def baseStart_1676553 : Nat := 118140960795 + 1676553 * 2 ^ 59
def prefixEnd_1676553 : Nat := 4983230072969 + 3 ^ 40 * 1676553 * 2
def baseEnd_1676553 : Nat := 95653059081942690264131

theorem tailTrace_1676553 : CollatzResearch.WordTrace tailWord_1676553 prefixEnd_1676553 95653059081942690264131 := by
  unfold tailWord_1676553
  simp only [CollatzResearch.WordTrace]
  refine ⟨61148911495142288301418313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40765940996761525534278875 61148911495142288301418313)
  ·
    refine ⟨45861683621356716226063735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61148911495142288301418313 45861683621356716226063735)
    ·
      refine ⟨68792525432035074339095603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45861683621356716226063735 68792525432035074339095603)
      ·
        refine ⟨103188788148052611508643405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68792525432035074339095603 103188788148052611508643405)
        ·
          refine ⟨38695795555519729315741277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103188788148052611508643405 38695795555519729315741277)
          ·
            refine ⟨14510923333319898493402979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38695795555519729315741277 14510923333319898493402979)
            ·
              refine ⟨21766384999979847740104469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14510923333319898493402979 21766384999979847740104469)
              ·
                refine ⟨1020299296874055362817397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21766384999979847740104469 1020299296874055362817397)
                ·
                  refine ⟨95653059081942690264131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1020299296874055362817397 95653059081942690264131)
                  ·
                    rfl

theorem cell23_1676553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 5].length) (baseStart_1676553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676553 prefixEnd_1676553 := by exact prefixLift 1676553
  have htrace : WordTrace (prefixWord ++ tailWord_1676553) baseStart_1676553 baseEnd_1676553 := by
    simpa [prefixWord, tailWord_1676553, baseEnd_1676553] using wordTrace_append hprefix tailTrace_1676553
  have hstable : (prefixWord ++ tailWord_1676553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676553).length < 2 ^ (prefixWord ++ tailWord_1676553).sum := by decide
  have hdescent : baseEnd_1676553 < baseStart_1676553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676640 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 3]
def baseStart_1676640 : Nat := 118140960795 + 1676640 * 2 ^ 59
def prefixEnd_1676640 : Nat := 4983230072969 + 3 ^ 40 * 1676640 * 2
def baseEnd_1676640 : Nat := 860922204554425371989279

theorem tailTrace_1676640 : CollatzResearch.WordTrace tailWord_1676640 prefixEnd_1676640 860922204554425371989279 := by
  unfold tailWord_1676640
  simp only [CollatzResearch.WordTrace]
  refine ⟨30576042322913551079917687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40768056430551401439890249 30576042322913551079917687)
  ·
    refine ⟨45864063484370326619876531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30576042322913551079917687 45864063484370326619876531)
    ·
      refine ⟨68796095226555489929814797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45864063484370326619876531 68796095226555489929814797)
      ·
        refine ⟨25798535709958308723680549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68796095226555489929814797 25798535709958308723680549)
        ·
          refine ⟨4837225445617182885690103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25798535709958308723680549 4837225445617182885690103)
          ·
            refine ⟨7255838168425774328535155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4837225445617182885690103 7255838168425774328535155)
            ·
              refine ⟨10883757252638661492802733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7255838168425774328535155 10883757252638661492802733)
              ·
                refine ⟨4081408969739498059801025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10883757252638661492802733 4081408969739498059801025)
                ·
                  refine ⟨3061056727304623544850769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4081408969739498059801025 3061056727304623544850769)
                  ·
                    refine ⟨2295792545478467658638077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3061056727304623544850769 2295792545478467658638077)
                    ·
                      refine ⟨860922204554425371989279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2295792545478467658638077 860922204554425371989279)
                      ·
                        rfl

theorem cell23_1676640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_1676640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676640 prefixEnd_1676640 := by exact prefixLift 1676640
  have htrace : WordTrace (prefixWord ++ tailWord_1676640) baseStart_1676640 baseEnd_1676640 := by
    simpa [prefixWord, tailWord_1676640, baseEnd_1676640] using wordTrace_append hprefix tailTrace_1676640
  have hstable : (prefixWord ++ tailWord_1676640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676640).length < 2 ^ (prefixWord ++ tailWord_1676640).sum := by decide
  have hdescent : baseEnd_1676640 < baseStart_1676640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676697 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 2, 3, 2]
def baseStart_1676697 : Nat := 118140960795 + 1676697 * 2 ^ 59
def prefixEnd_1676697 : Nat := 4983230072969 + 3 ^ 40 * 1676697 * 2
def baseEnd_1676697 : Nat := 860951472951731648976517

theorem tailTrace_1676697 : CollatzResearch.WordTrace tailWord_1676697 prefixEnd_1676697 860951472951731648976517 := by
  unfold tailWord_1676697
  simp only [CollatzResearch.WordTrace]
  refine ⟨61154163606620600894660345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40769442404413733929773563 61154163606620600894660345)
  ·
    refine ⟨45865622704965450670995259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61154163606620600894660345 45865622704965450670995259)
    ·
      refine ⟨68798434057448176006492889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45865622704965450670995259 68798434057448176006492889)
      ·
        refine ⟨51598825543086132004869667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68798434057448176006492889 51598825543086132004869667)
        ·
          refine ⟨77398238314629198007304501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51598825543086132004869667 77398238314629198007304501)
          ·
            refine ⟨7256084841996487313184797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77398238314629198007304501 7256084841996487313184797)
            ·
              refine ⟨2721031815748682742444299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7256084841996487313184797 2721031815748682742444299)
              ·
                refine ⟨4081547723623024113666449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2721031815748682742444299 4081547723623024113666449)
                ·
                  refine ⟨3061160792717268085249837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4081547723623024113666449 3061160792717268085249837)
                  ·
                    refine ⟨1147935297268975531968689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3061160792717268085249837 1147935297268975531968689)
                    ·
                      refine ⟨860951472951731648976517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1147935297268975531968689 860951472951731648976517)
                      ·
                        rfl

theorem cell23_1676697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 3, 2].length) (baseStart_1676697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676697 prefixEnd_1676697 := by exact prefixLift 1676697
  have htrace : WordTrace (prefixWord ++ tailWord_1676697) baseStart_1676697 baseEnd_1676697 := by
    simpa [prefixWord, tailWord_1676697, baseEnd_1676697] using wordTrace_append hprefix tailTrace_1676697
  have hstable : (prefixWord ++ tailWord_1676697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676697).length < 2 ^ (prefixWord ++ tailWord_1676697).sum := by decide
  have hdescent : baseEnd_1676697 < baseStart_1676697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676704 : List Nat := [2, 1, 1, 4, 1, 2, 4, 3, 1, 1, 3]
def baseStart_1676704 : Nat := 118140960795 + 1676704 * 2 ^ 59
def prefixEnd_1676704 : Nat := 4983230072969 + 3 ^ 40 * 1676704 * 2
def baseEnd_1676704 : Nat := 860955067316313121588985

theorem tailTrace_1676704 : CollatzResearch.WordTrace tailWord_1676704 prefixEnd_1676704 860955067316313121588985 := by
  unfold tailWord_1676704
  simp only [CollatzResearch.WordTrace]
  refine ⟨30577209458797620545082583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40769612611730160726776777 30577209458797620545082583)
  ·
    refine ⟨45865814188196430817623875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30577209458797620545082583 45865814188196430817623875)
    ·
      refine ⟨68798721282294646226435813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45865814188196430817623875 68798721282294646226435813)
      ·
        refine ⟨12899760240430246167456715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68798721282294646226435813 12899760240430246167456715)
        ·
          refine ⟨19349640360645369251185073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12899760240430246167456715 19349640360645369251185073)
          ·
            refine ⟨14512230270484026938388805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19349640360645369251185073 14512230270484026938388805)
            ·
              refine ⟨2721043175715755050947901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14512230270484026938388805 2721043175715755050947901)
              ·
                refine ⟨1020391190893408144105463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2721043175715755050947901 1020391190893408144105463)
                ·
                  refine ⟨1530586786340112216158195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020391190893408144105463 1530586786340112216158195)
                  ·
                    refine ⟨2295880179510168324237293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1530586786340112216158195 2295880179510168324237293)
                    ·
                      refine ⟨860955067316313121588985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2295880179510168324237293 860955067316313121588985)
                      ·
                        rfl

theorem cell23_1676704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_1676704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676704 prefixEnd_1676704 := by exact prefixLift 1676704
  have htrace : WordTrace (prefixWord ++ tailWord_1676704) baseStart_1676704 baseEnd_1676704 := by
    simpa [prefixWord, tailWord_1676704, baseEnd_1676704] using wordTrace_append hprefix tailTrace_1676704
  have hstable : (prefixWord ++ tailWord_1676704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676704).length < 2 ^ (prefixWord ++ tailWord_1676704).sum := by decide
  have hdescent : baseEnd_1676704 < baseStart_1676704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676720 : List Nat := [2, 1, 1, 1, 2, 1, 1, 8, 2, 4]
def baseStart_1676720 : Nat := 118140960795 + 1676720 * 2 ^ 59
def prefixEnd_1676720 : Nat := 4983230072969 + 3 ^ 40 * 1676720 * 2
def baseEnd_1676720 : Nat := 286987761002261686329637

theorem tailTrace_1676720 : CollatzResearch.WordTrace tailWord_1676720 prefixEnd_1676720 286987761002261686329637 := by
  unfold tailWord_1676720
  simp only [CollatzResearch.WordTrace]
  refine ⟨30577501242768637911373807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40770001657024850548498409 30577501242768637911373807)
  ·
    refine ⟨45866251864152956867060711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30577501242768637911373807 45866251864152956867060711)
    ·
      refine ⟨68799377796229435300591067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45866251864152956867060711 68799377796229435300591067)
      ·
        refine ⟨103199066694344152950886601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68799377796229435300591067 103199066694344152950886601)
        ·
          refine ⟨77399300020758114713164951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103199066694344152950886601 77399300020758114713164951)
          ·
            refine ⟨116098950031137172069747427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77399300020758114713164951 116098950031137172069747427)
            ·
              refine ⟨174148425046705758104621141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116098950031137172069747427 174148425046705758104621141)
              ·
                refine ⟨2040801856016083102788529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 174148425046705758104621141 2040801856016083102788529)
                ·
                  refine ⟨1530601392012062327091397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2040801856016083102788529 1530601392012062327091397)
                  ·
                    refine ⟨286987761002261686329637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1530601392012062327091397 286987761002261686329637)
                    ·
                      rfl

theorem cell23_1676720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 2, 4].length) (baseStart_1676720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676720 prefixEnd_1676720 := by exact prefixLift 1676720
  have htrace : WordTrace (prefixWord ++ tailWord_1676720) baseStart_1676720 baseEnd_1676720 := by
    simpa [prefixWord, tailWord_1676720, baseEnd_1676720] using wordTrace_append hprefix tailTrace_1676720
  have hstable : (prefixWord ++ tailWord_1676720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676720).length < 2 ^ (prefixWord ++ tailWord_1676720).sum := by decide
  have hdescent : baseEnd_1676720 < baseStart_1676720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676723 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 4]
def baseStart_1676723 : Nat := 118140960795 + 1676723 * 2 ^ 59
def prefixEnd_1676723 : Nat := 4983230072969 + 3 ^ 40 * 1676723 * 2
def baseEnd_1676723 : Nat := 860964823448748547251397

theorem tailTrace_1676723 : CollatzResearch.WordTrace tailWord_1676723 prefixEnd_1676723 860964823448748547251397 := by
  unfold tailWord_1676723
  simp only [CollatzResearch.WordTrace]
  refine ⟨61155111904526407335106823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40770074603017604890071215 61155111904526407335106823)
  ·
    refine ⟨91732667856789611002660235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61155111904526407335106823 91732667856789611002660235)
    ·
      refine ⟨137599001785184416503990353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91732667856789611002660235 137599001785184416503990353)
      ·
        refine ⟨103199251338888312377992765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137599001785184416503990353 103199251338888312377992765)
        ·
          refine ⟨38699719252083117141747287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103199251338888312377992765 38699719252083117141747287)
          ·
            refine ⟨58049578878124675712620931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38699719252083117141747287 58049578878124675712620931)
            ·
              refine ⟨87074368317187013568931397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58049578878124675712620931 87074368317187013568931397)
              ·
                refine ⟨16326444059472565044174637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87074368317187013568931397 16326444059472565044174637)
                ·
                  refine ⟨6122416522302211891565489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16326444059472565044174637 6122416522302211891565489)
                  ·
                    refine ⟨4591812391726658918674117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6122416522302211891565489 4591812391726658918674117)
                    ·
                      refine ⟨860964823448748547251397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4591812391726658918674117 860964823448748547251397)
                      ·
                        rfl

theorem cell23_1676723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_1676723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676723 prefixEnd_1676723 := by exact prefixLift 1676723
  have htrace : WordTrace (prefixWord ++ tailWord_1676723) baseStart_1676723 baseEnd_1676723 := by
    simpa [prefixWord, tailWord_1676723, baseEnd_1676723] using wordTrace_append hprefix tailTrace_1676723
  have hstable : (prefixWord ++ tailWord_1676723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676723).length < 2 ^ (prefixWord ++ tailWord_1676723).sum := by decide
  have hdescent : baseEnd_1676723 < baseStart_1676723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676733 : List Nat := [1, 4, 1, 2, 2, 1, 2, 10]
def baseStart_1676733 : Nat := 118140960795 + 1676733 * 2 ^ 59
def prefixEnd_1676733 : Nat := 4983230072969 + 3 ^ 40 * 1676733 * 2
def baseEnd_1676733 : Nat := 31887776231677537338013

theorem tailTrace_1676733 : CollatzResearch.WordTrace tailWord_1676733 prefixEnd_1676733 31887776231677537338013 := by
  unfold tailWord_1676733
  simp only [CollatzResearch.WordTrace]
  refine ⟨61155476634490179042970853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40770317756326786028647235 61155476634490179042970853)
  ·
    refine ⟨11466651868966908570557035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61155476634490179042970853 11466651868966908570557035)
    ·
      refine ⟨17199977803450362855835553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11466651868966908570557035 17199977803450362855835553)
      ·
        refine ⟨12899983352587772141876665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17199977803450362855835553 12899983352587772141876665)
        ·
          refine ⟨9674987514440829106407499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12899983352587772141876665 9674987514440829106407499)
          ·
            refine ⟨14512481271661243659611249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9674987514440829106407499 14512481271661243659611249)
            ·
              refine ⟨10884360953745932744708437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14512481271661243659611249 10884360953745932744708437)
              ·
                refine ⟨31887776231677537338013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10884360953745932744708437 31887776231677537338013)
                ·
                  rfl

theorem cell23_1676733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 10].length) (baseStart_1676733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676733 prefixEnd_1676733 := by exact prefixLift 1676733
  have htrace : WordTrace (prefixWord ++ tailWord_1676733) baseStart_1676733 baseEnd_1676733 := by
    simpa [prefixWord, tailWord_1676733, baseEnd_1676733] using wordTrace_append hprefix tailTrace_1676733
  have hstable : (prefixWord ++ tailWord_1676733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676733).length < 2 ^ (prefixWord ++ tailWord_1676733).sum := by decide
  have hdescent : baseEnd_1676733 < baseStart_1676733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676750 : List Nat := [4, 1, 1, 1, 2, 1, 6, 7]
def baseStart_1676750 : Nat := 118140960795 + 1676750 * 2 ^ 59
def prefixEnd_1676750 : Nat := 4983230072969 + 3 ^ 40 * 1676750 * 2
def baseEnd_1676750 : Nat := 31888099534311849689399

theorem tailTrace_1676750 : CollatzResearch.WordTrace tailWord_1676750 prefixEnd_1676750 31888099534311849689399 := by
  unfold tailWord_1676750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7644512084428573868292463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40770731116952393964226469 7644512084428573868292463)
  ·
    refine ⟨11466768126642860802438695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7644512084428573868292463 11466768126642860802438695)
    ·
      refine ⟨17200152189964291203658043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11466768126642860802438695 17200152189964291203658043)
      ·
        refine ⟨25800228284946436805487065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17200152189964291203658043 25800228284946436805487065)
        ·
          refine ⟨19350171213709827604115299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25800228284946436805487065 19350171213709827604115299)
          ·
            refine ⟨29025256820564741406172949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19350171213709827604115299 29025256820564741406172949)
            ·
              refine ⟨1360558913463972253414357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29025256820564741406172949 1360558913463972253414357)
              ·
                refine ⟨31888099534311849689399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1360558913463972253414357 31888099534311849689399)
                ·
                  rfl

theorem cell23_1676750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 7].length) (baseStart_1676750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676750 prefixEnd_1676750 := by exact prefixLift 1676750
  have htrace : WordTrace (prefixWord ++ tailWord_1676750) baseStart_1676750 baseEnd_1676750 := by
    simpa [prefixWord, tailWord_1676750, baseEnd_1676750] using wordTrace_append hprefix tailTrace_1676750
  have hstable : (prefixWord ++ tailWord_1676750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676750).length < 2 ^ (prefixWord ++ tailWord_1676750).sum := by decide
  have hdescent : baseEnd_1676750 < baseStart_1676750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676760 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 1, 3, 3]
def baseStart_1676760 : Nat := 118140960795 + 1676760 * 2 ^ 59
def prefixEnd_1676760 : Nat := 4983230072969 + 3 ^ 40 * 1676760 * 2
def baseEnd_1676760 : Nat := 860983822232964902488727

theorem tailTrace_1676760 : CollatzResearch.WordTrace tailWord_1676760 prefixEnd_1676760 860983822232964902488727 := by
  unfold tailWord_1676760
  simp only [CollatzResearch.WordTrace]
  refine ⟨30578230702696181327101867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40770974270261575102802489 30578230702696181327101867)
  ·
    refine ⟨45867346054044271990652801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30578230702696181327101867 45867346054044271990652801)
    ·
      refine ⟨34400509540533203992989601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45867346054044271990652801 34400509540533203992989601)
      ·
        refine ⟨25800382155399902994742201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34400509540533203992989601 25800382155399902994742201)
        ·
          refine ⟨19350286616549927246056651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25800382155399902994742201 19350286616549927246056651)
          ·
            refine ⟨29025429924824890869084977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19350286616549927246056651 29025429924824890869084977)
            ·
              refine ⟨21769072443618668151813733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29025429924824890869084977 21769072443618668151813733)
              ·
                refine ⟨4081701083178500278465075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21769072443618668151813733 4081701083178500278465075)
                ·
                  refine ⟨6122551624767750417697613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4081701083178500278465075 6122551624767750417697613)
                  ·
                    refine ⟨2295956859287906406636605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6122551624767750417697613 2295956859287906406636605)
                    ·
                      refine ⟨860983822232964902488727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2295956859287906406636605 860983822232964902488727)
                      ·
                        rfl

theorem cell23_1676760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_1676760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676760 prefixEnd_1676760 := by exact prefixLift 1676760
  have htrace : WordTrace (prefixWord ++ tailWord_1676760) baseStart_1676760 baseEnd_1676760 := by
    simpa [prefixWord, tailWord_1676760, baseEnd_1676760] using wordTrace_append hprefix tailTrace_1676760
  have hstable : (prefixWord ++ tailWord_1676760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676760).length < 2 ^ (prefixWord ++ tailWord_1676760).sum := by decide
  have hdescent : baseEnd_1676760 < baseStart_1676760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676761 : List Nat := [1, 2, 1, 2, 4, 2, 3, 3, 1, 2, 2]
def baseStart_1676761 : Nat := 118140960795 + 1676761 * 2 ^ 59
def prefixEnd_1676761 : Nat := 4983230072969 + 3 ^ 40 * 1676761 * 2
def baseEnd_1676761 : Nat := 860984335713619398576223

theorem tailTrace_1676761 : CollatzResearch.WordTrace tailWord_1676761 prefixEnd_1676761 860984335713619398576223 := by
  unfold tailWord_1676761
  simp only [CollatzResearch.WordTrace]
  refine ⟨61156497878388739824990137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40770998585592493216660091 61156497878388739824990137)
  ·
    refine ⟨45867373408791554868742603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61156497878388739824990137 45867373408791554868742603)
    ·
      refine ⟨68801060113187332303113905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45867373408791554868742603 68801060113187332303113905)
      ·
        refine ⟨51600795084890499227335429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68801060113187332303113905 51600795084890499227335429)
        ·
          refine ⟨9675149078416968605125393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51600795084890499227335429 9675149078416968605125393)
          ·
            refine ⟨7256361808812726453844045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9675149078416968605125393 7256361808812726453844045)
            ·
              refine ⟨2721135678304772420191517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7256361808812726453844045 2721135678304772420191517)
              ·
                refine ⟨1020425879364289657571819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2721135678304772420191517 1020425879364289657571819)
                ·
                  refine ⟨1530638819046434486357729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020425879364289657571819 1530638819046434486357729)
                  ·
                    refine ⟨1147979114284825864768297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1530638819046434486357729 1147979114284825864768297)
                    ·
                      refine ⟨860984335713619398576223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1147979114284825864768297 860984335713619398576223)
                      ·
                        rfl

theorem cell23_1676761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 1, 2, 2].length) (baseStart_1676761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676761 prefixEnd_1676761 := by exact prefixLift 1676761
  have htrace : WordTrace (prefixWord ++ tailWord_1676761) baseStart_1676761 baseEnd_1676761 := by
    simpa [prefixWord, tailWord_1676761, baseEnd_1676761] using wordTrace_append hprefix tailTrace_1676761
  have hstable : (prefixWord ++ tailWord_1676761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676761).length < 2 ^ (prefixWord ++ tailWord_1676761).sum := by decide
  have hdescent : baseEnd_1676761 < baseStart_1676761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676778 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 3, 2, 2]
def baseStart_1676778 : Nat := 118140960795 + 1676778 * 2 ^ 59
def prefixEnd_1676778 : Nat := 4983230072969 + 3 ^ 40 * 1676778 * 2
def baseEnd_1676778 : Nat := 860993064884745832063645

theorem tailTrace_1676778 : CollatzResearch.WordTrace tailWord_1676778 prefixEnd_1676778 860993064884745832063645 := by
  unfold tailWord_1676778
  simp only [CollatzResearch.WordTrace]
  refine ⟨15289279479831787932089747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40771411946218101152239325 15289279479831787932089747)
  ·
    refine ⟨22933919219747681898134621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15289279479831787932089747 22933919219747681898134621)
    ·
      refine ⟨8600219707405380711800483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22933919219747681898134621 8600219707405380711800483)
      ·
        refine ⟨12900329561108071067700725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8600219707405380711800483 12900329561108071067700725)
        ·
          refine ⟨1209405896353881662596943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12900329561108071067700725 1209405896353881662596943)
          ·
            refine ⟨1814108844530822493895415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209405896353881662596943 1814108844530822493895415)
            ·
              refine ⟨2721163266796233740843123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1814108844530822493895415 2721163266796233740843123)
              ·
                refine ⟨4081744900194350611264685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2721163266796233740843123 4081744900194350611264685)
                ·
                  refine ⟨1530654337572881479224257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4081744900194350611264685 1530654337572881479224257)
                  ·
                    refine ⟨1147990753179661109418193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1530654337572881479224257 1147990753179661109418193)
                    ·
                      refine ⟨860993064884745832063645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1147990753179661109418193 860993064884745832063645)
                      ·
                        rfl

theorem cell23_1676778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_1676778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676778 prefixEnd_1676778 := by exact prefixLift 1676778
  have htrace : WordTrace (prefixWord ++ tailWord_1676778) baseStart_1676778 baseEnd_1676778 := by
    simpa [prefixWord, tailWord_1676778, baseEnd_1676778] using wordTrace_append hprefix tailTrace_1676778
  have hstable : (prefixWord ++ tailWord_1676778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676778).length < 2 ^ (prefixWord ++ tailWord_1676778).sum := by decide
  have hdescent : baseEnd_1676778 < baseStart_1676778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676793 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 1, 8]
def baseStart_1676793 : Nat := 118140960795 + 1676793 * 2 ^ 59
def prefixEnd_1676793 : Nat := 4983230072969 + 3 ^ 40 * 1676793 * 2
def baseEnd_1676793 : Nat := 287000255698187757792025

theorem tailTrace_1676793 : CollatzResearch.WordTrace tailWord_1676793 prefixEnd_1676793 287000255698187757792025 := by
  unfold tailWord_1676793
  simp only [CollatzResearch.WordTrace]
  refine ⟨61157665014272809290155033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40771776676181872860103355 61157665014272809290155033)
  ·
    refine ⟨45868248760704606967616275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61157665014272809290155033 45868248760704606967616275)
    ·
      refine ⟨68802373141056910451424413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45868248760704606967616275 68802373141056910451424413)
      ·
        refine ⟨25800889927896341419284155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68802373141056910451424413 25800889927896341419284155)
        ·
          refine ⟨38701334891844512128926233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25800889927896341419284155 38701334891844512128926233)
          ·
            refine ⟨29026001168883384096694675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38701334891844512128926233 29026001168883384096694675)
            ·
              refine ⟨43539001753325076145042013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29026001168883384096694675 43539001753325076145042013)
              ·
                refine ⟨16327125657496903554390755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43539001753325076145042013 16327125657496903554390755)
                ·
                  refine ⟨24490688486245355331586133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16327125657496903554390755 24490688486245355331586133)
                  ·
                    refine ⟨287000255698187757792025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24490688486245355331586133 287000255698187757792025)
                    ·
                      rfl

theorem cell23_1676793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 8].length) (baseStart_1676793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676793 prefixEnd_1676793 := by exact prefixLift 1676793
  have htrace : WordTrace (prefixWord ++ tailWord_1676793) baseStart_1676793 baseEnd_1676793 := by
    simpa [prefixWord, tailWord_1676793, baseEnd_1676793] using wordTrace_append hprefix tailTrace_1676793
  have hstable : (prefixWord ++ tailWord_1676793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676793).length < 2 ^ (prefixWord ++ tailWord_1676793).sum := by decide
  have hdescent : baseEnd_1676793 < baseStart_1676793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676798 : List Nat := [4, 2, 2, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1676798 : Nat := 118140960795 + 1676798 * 2 ^ 59
def prefixEnd_1676798 : Nat := 4983230072969 + 3 ^ 40 * 1676798 * 2
def baseEnd_1676798 : Nat := 861003334497835753813553

theorem tailTrace_1676798 : CollatzResearch.WordTrace tailWord_1676798 prefixEnd_1676798 861003334497835753813553 := by
  unfold tailWord_1676798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7644730922406836893010881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40771898252836463429391365 7644730922406836893010881)
  ·
    refine ⟨5733548191805127669758161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7644730922406836893010881 5733548191805127669758161)
    ·
      refine ⟨4300161143853845752318621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5733548191805127669758161 4300161143853845752318621)
      ·
        refine ⟨1612560428945192157119483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4300161143853845752318621 1612560428945192157119483)
        ·
          refine ⟨2418840643417788235679225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1612560428945192157119483 2418840643417788235679225)
          ·
            refine ⟨1814130482563341176759419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2418840643417788235679225 1814130482563341176759419)
            ·
              refine ⟨2721195723845011765139129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1814130482563341176759419 2721195723845011765139129)
              ·
                refine ⟨2040896792883758823854347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2721195723845011765139129 2040896792883758823854347)
                ·
                  refine ⟨3061345189325638235781521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040896792883758823854347 3061345189325638235781521)
                  ·
                    refine ⟨2296008891994228676836141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3061345189325638235781521 2296008891994228676836141)
                    ·
                      refine ⟨861003334497835753813553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2296008891994228676836141 861003334497835753813553)
                      ·
                        rfl

theorem cell23_1676798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1676798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676798 prefixEnd_1676798 := by exact prefixLift 1676798
  have htrace : WordTrace (prefixWord ++ tailWord_1676798) baseStart_1676798 baseEnd_1676798 := by
    simpa [prefixWord, tailWord_1676798, baseEnd_1676798] using wordTrace_append hprefix tailTrace_1676798
  have hstable : (prefixWord ++ tailWord_1676798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676798).length < 2 ^ (prefixWord ++ tailWord_1676798).sum := by decide
  have hdescent : baseEnd_1676798 < baseStart_1676798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676817 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 1, 4, 2]
def baseStart_1676817 : Nat := 118140960795 + 1676817 * 2 ^ 59
def prefixEnd_1676817 : Nat := 4983230072969 + 3 ^ 40 * 1676817 * 2
def baseEnd_1676817 : Nat := 861013090630271179475965

theorem tailTrace_1676817 : CollatzResearch.WordTrace tailWord_1676817 prefixEnd_1676817 861013090630271179475965 := by
  unfold tailWord_1676817
  simp only [CollatzResearch.WordTrace]
  refine ⟨61158540366185861389028705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40772360244123907592685803 61158540366185861389028705)
  ·
    refine ⟨45868905274639396041771529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61158540366185861389028705 45868905274639396041771529)
    ·
      refine ⟨34401678955979547031328647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45868905274639396041771529 34401678955979547031328647)
      ·
        refine ⟨51602518433969320546992971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34401678955979547031328647 51602518433969320546992971)
        ·
          refine ⟨77403777650953980820489457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51602518433969320546992971 77403777650953980820489457)
          ·
            refine ⟨58052833238215485615367093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77403777650953980820489457 58052833238215485615367093)
            ·
              refine ⟨5442453116082701776440665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58052833238215485615367093 5442453116082701776440665)
              ·
                refine ⟨4081839837062026332330499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5442453116082701776440665 4081839837062026332330499)
                ·
                  refine ⟨6122759755593039498495749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4081839837062026332330499 6122759755593039498495749)
                  ·
                    refine ⟨1148017454173694905967953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6122759755593039498495749 1148017454173694905967953)
                    ·
                      refine ⟨861013090630271179475965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1148017454173694905967953 861013090630271179475965)
                      ·
                        rfl

theorem cell23_1676817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 4, 2].length) (baseStart_1676817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676817 prefixEnd_1676817 := by exact prefixLift 1676817
  have htrace : WordTrace (prefixWord ++ tailWord_1676817) baseStart_1676817 baseEnd_1676817 := by
    simpa [prefixWord, tailWord_1676817, baseEnd_1676817] using wordTrace_append hprefix tailTrace_1676817
  have hstable : (prefixWord ++ tailWord_1676817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676817).length < 2 ^ (prefixWord ++ tailWord_1676817).sum := by decide
  have hdescent : baseEnd_1676817 < baseStart_1676817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676821 : List Nat := [1, 3, 2, 1, 3, 3, 3, 1, 1, 3, 2]
def baseStart_1676821 : Nat := 118140960795 + 1676821 * 2 ^ 59
def prefixEnd_1676821 : Nat := 4983230072969 + 3 ^ 40 * 1676821 * 2
def baseEnd_1676821 : Nat := 861015144552889163825947

theorem tailTrace_1676821 : CollatzResearch.WordTrace tailWord_1676821 prefixEnd_1676821 861015144552889163825947 := by
  unfold tailWord_1676821
  simp only [CollatzResearch.WordTrace]
  refine ⟨61158686258171370072174317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40772457505447580048116211 61158686258171370072174317)
  ·
    refine ⟨22934507346814263777065369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61158686258171370072174317 22934507346814263777065369)
    ·
      refine ⟨17200880510110697832799027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22934507346814263777065369 17200880510110697832799027)
      ·
        refine ⟨25801320765166046749198541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17200880510110697832799027 25801320765166046749198541)
        ·
          refine ⟨9675495286937267530949453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25801320765166046749198541 9675495286937267530949453)
          ·
            refine ⟨3628310732601475324106045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9675495286937267530949453 3628310732601475324106045)
            ·
              refine ⟨1360616524725553246539767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3628310732601475324106045 1360616524725553246539767)
              ·
                refine ⟨2040924787088329869809651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360616524725553246539767 2040924787088329869809651)
                ·
                  refine ⟨3061387180632494804714477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040924787088329869809651 3061387180632494804714477)
                  ·
                    refine ⟨1148020192737185551767929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3061387180632494804714477 1148020192737185551767929)
                    ·
                      refine ⟨861015144552889163825947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1148020192737185551767929 861015144552889163825947)
                      ·
                        rfl

theorem cell23_1676821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_1676821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676821 prefixEnd_1676821 := by exact prefixLift 1676821
  have htrace : WordTrace (prefixWord ++ tailWord_1676821) baseStart_1676821 baseEnd_1676821 := by
    simpa [prefixWord, tailWord_1676821, baseEnd_1676821] using wordTrace_append hprefix tailTrace_1676821
  have hstable : (prefixWord ++ tailWord_1676821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676821).length < 2 ^ (prefixWord ++ tailWord_1676821).sum := by decide
  have hdescent : baseEnd_1676821 < baseStart_1676821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676834 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 4, 2, 2]
def baseStart_1676834 : Nat := 118140960795 + 1676834 * 2 ^ 59
def prefixEnd_1676834 : Nat := 4983230072969 + 3 ^ 40 * 1676834 * 2
def baseEnd_1676834 : Nat := 861021819801397612963387

theorem tailTrace_1676834 : CollatzResearch.WordTrace tailWord_1676834 prefixEnd_1676834 861021819801397612963387 := by
  unfold tailWord_1676834
  simp only [CollatzResearch.WordTrace]
  refine ⟨15289790101781068323099389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40772773604749515528265037 15289790101781068323099389)
  ·
    refine ⟨5733671288167900621162271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15289790101781068323099389 5733671288167900621162271)
    ·
      refine ⟨8600506932251850931743407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5733671288167900621162271 8600506932251850931743407)
      ·
        refine ⟨12900760398377776397615111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8600506932251850931743407 12900760398377776397615111)
        ·
          refine ⟨19351140597566664596422667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12900760398377776397615111 19351140597566664596422667)
          ·
            refine ⟨29026710896349996894634001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19351140597566664596422667 29026710896349996894634001)
            ·
              refine ⟨21770033172262497670975501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29026710896349996894634001 21770033172262497670975501)
              ·
                refine ⟨8163762439598436626615813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21770033172262497670975501 8163762439598436626615813)
                ·
                  refine ⟨1530705457424706867490465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8163762439598436626615813 1530705457424706867490465)
                  ·
                    refine ⟨1148029093068530150617849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1530705457424706867490465 1148029093068530150617849)
                    ·
                      refine ⟨861021819801397612963387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1148029093068530150617849 861021819801397612963387)
                      ·
                        rfl

theorem cell23_1676834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_1676834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676834 prefixEnd_1676834 := by exact prefixLift 1676834
  have htrace : WordTrace (prefixWord ++ tailWord_1676834) baseStart_1676834 baseEnd_1676834 := by
    simpa [prefixWord, tailWord_1676834, baseEnd_1676834] using wordTrace_append hprefix tailTrace_1676834
  have hstable : (prefixWord ++ tailWord_1676834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676834).length < 2 ^ (prefixWord ++ tailWord_1676834).sum := by decide
  have hdescent : baseEnd_1676834 < baseStart_1676834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676843 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 8]
def baseStart_1676843 : Nat := 118140960795 + 1676843 * 2 ^ 59
def prefixEnd_1676843 : Nat := 4983230072969 + 3 ^ 40 * 1676843 * 2
def baseEnd_1676843 : Nat := 861026441127288077750845

theorem tailTrace_1676843 : CollatzResearch.WordTrace tailWord_1676843 prefixEnd_1676843 861026441127288077750845 := by
  unfold tailWord_1676843
  simp only [CollatzResearch.WordTrace]
  refine ⟨61159488664091667829475183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40772992442727778552983455 61159488664091667829475183)
  ·
    refine ⟨91739232996137501744212775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61159488664091667829475183 91739232996137501744212775)
    ·
      refine ⟨137608849494206252616319163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91739232996137501744212775 137608849494206252616319163)
      ·
        refine ⟨206413274241309378924478745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137608849494206252616319163 206413274241309378924478745)
        ·
          refine ⟨154809955680982034193359059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206413274241309378924478745 154809955680982034193359059)
          ·
            refine ⟨232214933521473051290038589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154809955680982034193359059 232214933521473051290038589)
            ·
              refine ⟨87080600070552394233764471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232214933521473051290038589 87080600070552394233764471)
              ·
                refine ⟨130620900105828591350646707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87080600070552394233764471 130620900105828591350646707)
                ·
                  refine ⟨195931350158742887025970061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130620900105828591350646707 195931350158742887025970061)
                  ·
                    refine ⟨73474256309528582634738773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195931350158742887025970061 73474256309528582634738773)
                    ·
                      refine ⟨861026441127288077750845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 73474256309528582634738773 861026441127288077750845)
                      ·
                        rfl

theorem cell23_1676843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 8].length) (baseStart_1676843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676843 prefixEnd_1676843 := by exact prefixLift 1676843
  have htrace : WordTrace (prefixWord ++ tailWord_1676843) baseStart_1676843 baseEnd_1676843 := by
    simpa [prefixWord, tailWord_1676843, baseEnd_1676843] using wordTrace_append hprefix tailTrace_1676843
  have hstable : (prefixWord ++ tailWord_1676843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676843).length < 2 ^ (prefixWord ++ tailWord_1676843).sum := by decide
  have hdescent : baseEnd_1676843 < baseStart_1676843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676964 : List Nat := [2, 3, 1, 2, 2, 2, 4, 1, 6]
def baseStart_1676964 : Nat := 118140960795 + 1676964 * 2 ^ 59
def prefixEnd_1676964 : Nat := 4983230072969 + 3 ^ 40 * 1676964 * 2
def baseEnd_1676964 : Nat := 95676508031831344926421

theorem tailTrace_1676964 : CollatzResearch.WordTrace tailWord_1676964 prefixEnd_1676964 95676508031831344926421 := by
  unfold tailWord_1676964
  simp only [CollatzResearch.WordTrace]
  refine ⟨30581950948326652747314973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40775934597768870329753297 30581950948326652747314973)
  ·
    refine ⟨11468231605622494780243115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30581950948326652747314973 11468231605622494780243115)
    ·
      refine ⟨17202347408433742170364673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11468231605622494780243115 17202347408433742170364673)
      ·
        refine ⟨12901760556325306627773505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17202347408433742170364673 12901760556325306627773505)
        ·
          refine ⟨9676320417243979970830129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12901760556325306627773505 9676320417243979970830129)
          ·
            refine ⟨7257240312932984978122597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9676320417243979970830129 7257240312932984978122597)
            ·
              refine ⟨1360732558674934683397987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7257240312932984978122597 1360732558674934683397987)
              ·
                refine ⟨2041098838012402025096981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360732558674934683397987 2041098838012402025096981)
                ·
                  refine ⟨95676508031831344926421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2041098838012402025096981 95676508031831344926421)
                  ·
                    rfl

theorem cell23_1676964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_1676964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676964 prefixEnd_1676964 := by exact prefixLift 1676964
  have htrace : WordTrace (prefixWord ++ tailWord_1676964) baseStart_1676964 baseEnd_1676964 := by
    simpa [prefixWord, tailWord_1676964, baseEnd_1676964] using wordTrace_append hprefix tailTrace_1676964
  have hstable : (prefixWord ++ tailWord_1676964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676964).length < 2 ^ (prefixWord ++ tailWord_1676964).sum := by decide
  have hdescent : baseEnd_1676964 < baseStart_1676964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676991 : List Nat := [1, 1, 2, 2, 2, 3, 2, 5, 1, 1, 3]
def baseStart_1676991 : Nat := 118140960795 + 1676991 * 2 ^ 59
def prefixEnd_1676991 : Nat := 4983230072969 + 3 ^ 40 * 1676991 * 2
def baseEnd_1676991 : Nat := 861102436264153498700165

theorem tailTrace_1676991 : CollatzResearch.WordTrace tailWord_1676991 prefixEnd_1676991 861102436264153498700165 := by
  unfold tailWord_1676991
  simp only [CollatzResearch.WordTrace]
  refine ⟨61164886667555489105862827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40776591111703659403908551 61164886667555489105862827)
  ·
    refine ⟨91747330001333233658794241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61164886667555489105862827 91747330001333233658794241)
    ·
      refine ⟨68810497500999925244095681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91747330001333233658794241 68810497500999925244095681)
      ·
        refine ⟨51607873125749943933071761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68810497500999925244095681 51607873125749943933071761)
        ·
          refine ⟨38705904844312457949803821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51607873125749943933071761 38705904844312457949803821)
          ·
            refine ⟨14514714316617171731176433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38705904844312457949803821 14514714316617171731176433)
            ·
              refine ⟨10886035737462878798382325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14514714316617171731176433 10886035737462878798382325)
              ·
                refine ⟨1020565850387144887348343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10886035737462878798382325 1020565850387144887348343)
                ·
                  refine ⟨1530848775580717331022515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020565850387144887348343 1530848775580717331022515)
                  ·
                    refine ⟨2296273163371075996533773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1530848775580717331022515 2296273163371075996533773)
                    ·
                      refine ⟨861102436264153498700165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2296273163371075996533773 861102436264153498700165)
                      ·
                        rfl

theorem cell23_1676991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 1, 1, 3].length) (baseStart_1676991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676991 prefixEnd_1676991 := by exact prefixLift 1676991
  have htrace : WordTrace (prefixWord ++ tailWord_1676991) baseStart_1676991 baseEnd_1676991 := by
    simpa [prefixWord, tailWord_1676991, baseEnd_1676991] using wordTrace_append hprefix tailTrace_1676991
  have hstable : (prefixWord ++ tailWord_1676991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676991).length < 2 ^ (prefixWord ++ tailWord_1676991).sum := by decide
  have hdescent : baseEnd_1676991 < baseStart_1676991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676998 : List Nat := [6, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_1676998 : Nat := 118140960795 + 1676998 * 2 ^ 59
def prefixEnd_1676998 : Nat := 4983230072969 + 3 ^ 40 * 1676998 * 2
def baseEnd_1676998 : Nat := 95678447847637219034737

theorem tailTrace_1676998 : CollatzResearch.WordTrace tailWord_1676998 prefixEnd_1676998 95678447847637219034737 := by
  unfold tailWord_1676998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1911410686829066540667739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40776761319020086200911765 1911410686829066540667739)
  ·
    refine ⟨2867116030243599811001609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1911410686829066540667739 2867116030243599811001609)
    ·
      refine ⟨2150337022682699858251207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2867116030243599811001609 2150337022682699858251207)
      ·
        refine ⟨3225505534024049787376811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2150337022682699858251207 3225505534024049787376811)
        ·
          refine ⟨4838258301036074681065217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3225505534024049787376811 4838258301036074681065217)
          ·
            refine ⟨3628693725777056010798913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4838258301036074681065217 3628693725777056010798913)
            ·
              refine ⟨2721520294332792008099185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3628693725777056010798913 2721520294332792008099185)
              ·
                refine ⟨2041140220749594006074389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2721520294332792008099185 2041140220749594006074389)
                ·
                  refine ⟨95678447847637219034737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2041140220749594006074389 95678447847637219034737)
                  ·
                    rfl

theorem cell23_1676998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_1676998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1676998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1676998 prefixEnd_1676998 := by exact prefixLift 1676998
  have htrace : WordTrace (prefixWord ++ tailWord_1676998) baseStart_1676998 baseEnd_1676998 := by
    simpa [prefixWord, tailWord_1676998, baseEnd_1676998] using wordTrace_append hprefix tailTrace_1676998
  have hstable : (prefixWord ++ tailWord_1676998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676998).length < 2 ^ (prefixWord ++ tailWord_1676998).sum := by decide
  have hdescent : baseEnd_1676998 < baseStart_1676998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677007 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 4, 4]
def baseStart_1677007 : Nat := 118140960795 + 1677007 * 2 ^ 59
def prefixEnd_1677007 : Nat := 4983230072969 + 3 ^ 40 * 1677007 * 2
def baseEnd_1677007 : Nat := 287036883984875145366697

theorem tailTrace_1677007 : CollatzResearch.WordTrace tailWord_1677007 prefixEnd_1677007 287036883984875145366697 := by
  unfold tailWord_1677007
  simp only [CollatzResearch.WordTrace]
  refine ⟨61165470235497523838445275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40776980156998349225630183 61165470235497523838445275)
  ·
    refine ⟨91748205353246285757667913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61165470235497523838445275 91748205353246285757667913)
    ·
      refine ⟨68811154014934714318250935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91748205353246285757667913 68811154014934714318250935)
      ·
        refine ⟨103216731022402071477376403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68811154014934714318250935 103216731022402071477376403)
        ·
          refine ⟨154825096533603107216064605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103216731022402071477376403 154825096533603107216064605)
          ·
            refine ⟨58059411200101165206024227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154825096533603107216064605 58059411200101165206024227)
            ·
              refine ⟨87089116800151747809036341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58059411200101165206024227 87089116800151747809036341)
              ·
                refine ⟨8164604700014226357097157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87089116800151747809036341 8164604700014226357097157)
                ·
                  refine ⟨1530863381252667441955717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8164604700014226357097157 1530863381252667441955717)
                  ·
                    refine ⟨287036883984875145366697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1530863381252667441955717 287036883984875145366697)
                    ·
                      rfl

theorem cell23_1677007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 4].length) (baseStart_1677007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677007 prefixEnd_1677007 := by exact prefixLift 1677007
  have htrace : WordTrace (prefixWord ++ tailWord_1677007) baseStart_1677007 baseEnd_1677007 := by
    simpa [prefixWord, tailWord_1677007, baseEnd_1677007] using wordTrace_append hprefix tailTrace_1677007
  have hstable : (prefixWord ++ tailWord_1677007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677007).length < 2 ^ (prefixWord ++ tailWord_1677007).sum := by decide
  have hdescent : baseEnd_1677007 < baseStart_1677007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677024 : List Nat := [2, 1, 1, 3, 1, 2, 4, 3, 2, 4]
def baseStart_1677024 : Nat := 118140960795 + 1677024 * 2 ^ 59
def prefixEnd_1677024 : Nat := 4983230072969 + 3 ^ 40 * 1677024 * 2
def baseEnd_1677024 : Nat := 287039793708583956529171

theorem tailTrace_1677024 : CollatzResearch.WordTrace tailWord_1677024 prefixEnd_1677024 287039793708583956529171 := by
  unfold tailWord_1677024
  simp only [CollatzResearch.WordTrace]
  refine ⟨30583045138217967870907063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40777393517623957161209417 30583045138217967870907063)
  ·
    refine ⟨45874567707326951806360595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30583045138217967870907063 45874567707326951806360595)
    ·
      refine ⟨68811851560990427709540893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45874567707326951806360595 68811851560990427709540893)
      ·
        refine ⟨25804444335371410391077835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68811851560990427709540893 25804444335371410391077835)
        ·
          refine ⟨38706666503057115586616753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25804444335371410391077835 38706666503057115586616753)
          ·
            refine ⟨29029999877292836689962565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38706666503057115586616753 29029999877292836689962565)
            ·
              refine ⟨5443124976992406879367981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29029999877292836689962565 5443124976992406879367981)
              ·
                refine ⟨2041171866372152579762993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5443124976992406879367981 2041171866372152579762993)
                ·
                  refine ⟨1530878899779114434822245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2041171866372152579762993 1530878899779114434822245)
                  ·
                    refine ⟨287039793708583956529171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1530878899779114434822245 287039793708583956529171)
                    ·
                      rfl

theorem cell23_1677024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 2, 4].length) (baseStart_1677024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677024 prefixEnd_1677024 := by exact prefixLift 1677024
  have htrace : WordTrace (prefixWord ++ tailWord_1677024) baseStart_1677024 baseEnd_1677024 := by
    simpa [prefixWord, tailWord_1677024, baseEnd_1677024] using wordTrace_append hprefix tailTrace_1677024
  have hstable : (prefixWord ++ tailWord_1677024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677024).length < 2 ^ (prefixWord ++ tailWord_1677024).sum := by decide
  have hdescent : baseEnd_1677024 < baseStart_1677024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677034 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_1677034 : Nat := 118140960795 + 1677034 * 2 ^ 59
def prefixEnd_1677034 : Nat := 4983230072969 + 3 ^ 40 * 1677034 * 2
def baseEnd_1677034 : Nat := 861124515932296830462467

theorem tailTrace_1677034 : CollatzResearch.WordTrace tailWord_1677034 prefixEnd_1677034 861124515932296830462467 := by
  unfold tailWord_1677034
  simp only [CollatzResearch.WordTrace]
  refine ⟨15291613751599926862419539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40777636670933138299785437 15291613751599926862419539)
  ·
    refine ⟨22937420627399890293629309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15291613751599926862419539 22937420627399890293629309)
    ·
      refine ⟨8601532735274958860110991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22937420627399890293629309 8601532735274958860110991)
      ·
        refine ⟨12902299102912438290166487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8601532735274958860110991 12902299102912438290166487)
        ·
          refine ⟨19353448654368657435249731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12902299102912438290166487 19353448654368657435249731)
          ·
            refine ⟨29030172981552986152874597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19353448654368657435249731 29030172981552986152874597)
            ·
              refine ⟨5443157434041184903663987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29030172981552986152874597 5443157434041184903663987)
              ·
                refine ⟨8164736151061777355495981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5443157434041184903663987 8164736151061777355495981)
                ·
                  refine ⟨3061776056648166508310993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8164736151061777355495981 3061776056648166508310993)
                  ·
                    refine ⟨2296332042486124881233245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3061776056648166508310993 2296332042486124881233245)
                    ·
                      refine ⟨861124515932296830462467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2296332042486124881233245 861124515932296830462467)
                      ·
                        rfl

theorem cell23_1677034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_1677034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677034 prefixEnd_1677034 := by exact prefixLift 1677034
  have htrace : WordTrace (prefixWord ++ tailWord_1677034) baseStart_1677034 baseEnd_1677034 := by
    simpa [prefixWord, tailWord_1677034, baseEnd_1677034] using wordTrace_append hprefix tailTrace_1677034
  have hstable : (prefixWord ++ tailWord_1677034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677034).length < 2 ^ (prefixWord ++ tailWord_1677034).sum := by decide
  have hdescent : baseEnd_1677034 < baseStart_1677034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677054 : List Nat := [4, 2, 2, 1, 3, 1, 10]
def baseStart_1677054 : Nat := 118140960795 + 1677054 * 2 ^ 59
def prefixEnd_1677054 : Nat := 4983230072969 + 3 ^ 40 * 1677054 * 2
def baseEnd_1677054 : Nat := 10631293648708478422375

theorem tailTrace_1677054 : CollatzResearch.WordTrace tailWord_1677054 prefixEnd_1677054 10631293648708478422375 := by
  unfold tailWord_1677054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7645898058290906358175777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40778122977551500576937477 7645898058290906358175777)
  ·
    refine ⟨5734423543718179768631833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7645898058290906358175777 5734423543718179768631833)
    ·
      refine ⟨4300817657788634826473875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5734423543718179768631833 4300817657788634826473875)
      ·
        refine ⟨6451226486682952239710813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4300817657788634826473875 6451226486682952239710813)
        ·
          refine ⟨2419209932506107089891555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6451226486682952239710813 2419209932506107089891555)
          ·
            refine ⟨3628814898759160634837333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2419209932506107089891555 3628814898759160634837333)
            ·
              refine ⟨10631293648708478422375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3628814898759160634837333 10631293648708478422375)
              ·
                rfl

theorem cell23_1677054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 10].length) (baseStart_1677054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677054 prefixEnd_1677054 := by exact prefixLift 1677054
  have htrace : WordTrace (prefixWord ++ tailWord_1677054) baseStart_1677054 baseEnd_1677054 := by
    simpa [prefixWord, tailWord_1677054, baseEnd_1677054] using wordTrace_append hprefix tailTrace_1677054
  have hstable : (prefixWord ++ tailWord_1677054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677054).length < 2 ^ (prefixWord ++ tailWord_1677054).sum := by decide
  have hdescent : baseEnd_1677054 < baseStart_1677054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677091 : List Nat := [1, 1, 1, 4, 2, 1, 3, 4, 1, 3, 2]
def baseStart_1677091 : Nat := 118140960795 + 1677091 * 2 ^ 59
def prefixEnd_1677091 : Nat := 4983230072969 + 3 ^ 40 * 1677091 * 2
def baseEnd_1677091 : Nat := 861153784329603107449705

theorem tailTrace_1677091 : CollatzResearch.WordTrace tailWord_1677091 prefixEnd_1677091 861153784329603107449705 := by
  unfold tailWord_1677091
  simp only [CollatzResearch.WordTrace]
  refine ⟨61168533967193206184503127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40779022644795470789668751 61168533967193206184503127)
  ·
    refine ⟨91752800950789809276754691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61168533967193206184503127 91752800950789809276754691)
    ·
      refine ⟨137629201426184713915132037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91752800950789809276754691 137629201426184713915132037)
      ·
        refine ⟨25805475267409633859087257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137629201426184713915132037 25805475267409633859087257)
        ·
          refine ⟨19354106450557225394315443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25805475267409633859087257 19354106450557225394315443)
          ·
            refine ⟨29031159675835838091473165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19354106450557225394315443 29031159675835838091473165)
            ·
              refine ⟨10886684878438439284302437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29031159675835838091473165 10886684878438439284302437)
              ·
                refine ⟨2041253414707207365806707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10886684878438439284302437 2041253414707207365806707)
                ·
                  refine ⟨3061880122060811048710061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2041253414707207365806707 3061880122060811048710061)
                  ·
                    refine ⟨1148205045772804143266273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3061880122060811048710061 1148205045772804143266273)
                    ·
                      refine ⟨861153784329603107449705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1148205045772804143266273 861153784329603107449705)
                      ·
                        rfl

theorem cell23_1677091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_1677091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677091 prefixEnd_1677091 := by exact prefixLift 1677091
  have htrace : WordTrace (prefixWord ++ tailWord_1677091) baseStart_1677091 baseEnd_1677091 := by
    simpa [prefixWord, tailWord_1677091, baseEnd_1677091] using wordTrace_append hprefix tailTrace_1677091
  have hstable : (prefixWord ++ tailWord_1677091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677091).length < 2 ^ (prefixWord ++ tailWord_1677091).sum := by decide
  have hdescent : baseEnd_1677091 < baseStart_1677091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677132 : List Nat := [2, 2, 1, 3, 5, 1, 2, 1, 2, 1, 3]
def baseStart_1677132 : Nat := 118140960795 + 1677132 * 2 ^ 59
def prefixEnd_1677132 : Nat := 4983230072969 + 3 ^ 40 * 1677132 * 2
def baseEnd_1677132 : Nat := 861174837036437447037017

theorem tailTrace_1677132 : CollatzResearch.WordTrace tailWord_1677132 prefixEnd_1677132 861174837036437447037017 := by
  unfold tailWord_1677132
  simp only [CollatzResearch.WordTrace]
  refine ⟨30585014680022335093372825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40780019573363113457830433 30585014680022335093372825)
  ·
    refine ⟨22938761010016751320029619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30585014680022335093372825 22938761010016751320029619)
    ·
      refine ⟨34408141515025126980044429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22938761010016751320029619 34408141515025126980044429)
      ·
        refine ⟨12903053068134422617516661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34408141515025126980044429 12903053068134422617516661)
        ·
          refine ⟨1209661225137602120392187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12903053068134422617516661 1209661225137602120392187)
          ·
            refine ⟨1814491837706403180588281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209661225137602120392187 1814491837706403180588281)
            ·
              refine ⟨1360868878279802385441211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1814491837706403180588281 1360868878279802385441211)
              ·
                refine ⟨2041303317419703578161817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360868878279802385441211 2041303317419703578161817)
                ·
                  refine ⟨1530977488064777683621363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2041303317419703578161817 1530977488064777683621363)
                  ·
                    refine ⟨2296466232097166525432045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1530977488064777683621363 2296466232097166525432045)
                    ·
                      refine ⟨861174837036437447037017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2296466232097166525432045 861174837036437447037017)
                      ·
                        rfl

theorem cell23_1677132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_1677132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677132 prefixEnd_1677132 := by exact prefixLift 1677132
  have htrace : WordTrace (prefixWord ++ tailWord_1677132) baseStart_1677132 baseEnd_1677132 := by
    simpa [prefixWord, tailWord_1677132, baseEnd_1677132] using wordTrace_append hprefix tailTrace_1677132
  have hstable : (prefixWord ++ tailWord_1677132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677132).length < 2 ^ (prefixWord ++ tailWord_1677132).sum := by decide
  have hdescent : baseEnd_1677132 < baseStart_1677132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677264 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 3, 5]
def baseStart_1677264 : Nat := 118140960795 + 1677264 * 2 ^ 59
def prefixEnd_1677264 : Nat := 4983230072969 + 3 ^ 40 * 1677264 * 2
def baseEnd_1677264 : Nat := 287080872160943643528803

theorem tailTrace_1677264 : CollatzResearch.WordTrace tailWord_1677264 prefixEnd_1677264 287080872160943643528803 := by
  unfold tailWord_1677264
  simp only [CollatzResearch.WordTrace]
  refine ⟨30587421897783228365275423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40783229197044304487033897 30587421897783228365275423)
  ·
    refine ⟨45881132846674842547913135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30587421897783228365275423 45881132846674842547913135)
    ·
      refine ⟨68821699270012263821869703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45881132846674842547913135 68821699270012263821869703)
      ·
        refine ⟨103232548905018395732804555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68821699270012263821869703 103232548905018395732804555)
        ·
          refine ⟨154848823357527593599206833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103232548905018395732804555 154848823357527593599206833)
          ·
            refine ⟨116136617518145695199405125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154848823357527593599206833 116136617518145695199405125)
            ·
              refine ⟨21775615784652317849888461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116136617518145695199405125 21775615784652317849888461)
              ·
                refine ⟨8165855919244619193708173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21775615784652317849888461 8165855919244619193708173)
                ·
                  refine ⟨3062195969716732197640565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8165855919244619193708173 3062195969716732197640565)
                  ·
                    refine ⟨287080872160943643528803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3062195969716732197640565 287080872160943643528803)
                    ·
                      rfl

theorem cell23_1677264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 3, 5].length) (baseStart_1677264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677264 prefixEnd_1677264 := by exact prefixLift 1677264
  have htrace : WordTrace (prefixWord ++ tailWord_1677264) baseStart_1677264 baseEnd_1677264 := by
    simpa [prefixWord, tailWord_1677264, baseEnd_1677264] using wordTrace_append hprefix tailTrace_1677264
  have hstable : (prefixWord ++ tailWord_1677264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677264).length < 2 ^ (prefixWord ++ tailWord_1677264).sum := by decide
  have hdescent : baseEnd_1677264 < baseStart_1677264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677271 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 1, 5, 2]
def baseStart_1677271 : Nat := 118140960795 + 1677271 * 2 ^ 59
def prefixEnd_1677271 : Nat := 4983230072969 + 3 ^ 40 * 1677271 * 2
def baseEnd_1677271 : Nat := 861246210847412403198877

theorem tailTrace_1677271 : CollatzResearch.WordTrace tailWord_1677271 prefixEnd_1677271 861246210847412403198877 := by
  unfold tailWord_1677271
  simp only [CollatzResearch.WordTrace]
  refine ⟨61175099106541096926055667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40783399404360731284037111 61175099106541096926055667)
  ·
    refine ⟨91762648659811645389083501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61175099106541096926055667 91762648659811645389083501)
    ·
      refine ⟨34410993247429367020906313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91762648659811645389083501 34410993247429367020906313)
      ·
        refine ⟨25808244935572025265679735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34410993247429367020906313 25808244935572025265679735)
        ·
          refine ⟨38712367403358037898519603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25808244935572025265679735 38712367403358037898519603)
          ·
            refine ⟨58068551105037056847779405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38712367403358037898519603 58068551105037056847779405)
            ·
              refine ⟨21775706664388896317917277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58068551105037056847779405 21775706664388896317917277)
              ·
                refine ⟨8165889999145836119218979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21775706664388896317917277 8165889999145836119218979)
                ·
                  refine ⟨12248834998718754178828469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8165889999145836119218979 12248834998718754178828469)
                  ·
                    refine ⟨1148328281129883204265169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12248834998718754178828469 1148328281129883204265169)
                    ·
                      refine ⟨861246210847412403198877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1148328281129883204265169 861246210847412403198877)
                      ·
                        rfl

theorem cell23_1677271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_1677271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677271 prefixEnd_1677271 := by exact prefixLift 1677271
  have htrace : WordTrace (prefixWord ++ tailWord_1677271) baseStart_1677271 baseEnd_1677271 := by
    simpa [prefixWord, tailWord_1677271, baseEnd_1677271] using wordTrace_append hprefix tailTrace_1677271
  have hstable : (prefixWord ++ tailWord_1677271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677271).length < 2 ^ (prefixWord ++ tailWord_1677271).sum := by decide
  have hdescent : baseEnd_1677271 < baseStart_1677271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677281 : List Nat := [1, 2, 3, 1, 2, 1, 4, 3, 1, 5]
def baseStart_1677281 : Nat := 118140960795 + 1677281 * 2 ^ 59
def prefixEnd_1677281 : Nat := 4983230072969 + 3 ^ 40 * 1677281 * 2
def baseEnd_1677281 : Nat := 287083781884652454691277

theorem tailTrace_1677281 : CollatzResearch.WordTrace tailWord_1677281 prefixEnd_1677281 287083781884652454691277 := by
  unfold tailWord_1677281
  simp only [CollatzResearch.WordTrace]
  refine ⟨61175463836504868633919697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40783642557669912422613131 61175463836504868633919697)
  ·
    refine ⟨45881597877378651475439773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61175463836504868633919697 45881597877378651475439773)
    ·
      refine ⟨17205599204016994303289915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45881597877378651475439773 17205599204016994303289915)
      ·
        refine ⟨25808398806025491454934873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17205599204016994303289915 25808398806025491454934873)
        ·
          refine ⟨19356299104519118591201155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25808398806025491454934873 19356299104519118591201155)
          ·
            refine ⟨29034448656778677886801733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19356299104519118591201155 29034448656778677886801733)
            ·
              refine ⟨5443959123146002103775325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29034448656778677886801733 5443959123146002103775325)
              ·
                refine ⟨2041484671179750788915747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5443959123146002103775325 2041484671179750788915747)
                ·
                  refine ⟨3062227006769626183373621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2041484671179750788915747 3062227006769626183373621)
                  ·
                    refine ⟨287083781884652454691277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3062227006769626183373621 287083781884652454691277)
                    ·
                      rfl

theorem cell23_1677281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_1677281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677281 prefixEnd_1677281 := by exact prefixLift 1677281
  have htrace : WordTrace (prefixWord ++ tailWord_1677281) baseStart_1677281 baseEnd_1677281 := by
    simpa [prefixWord, tailWord_1677281, baseEnd_1677281] using wordTrace_append hprefix tailTrace_1677281
  have hstable : (prefixWord ++ tailWord_1677281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677281).length < 2 ^ (prefixWord ++ tailWord_1677281).sum := by decide
  have hdescent : baseEnd_1677281 < baseStart_1677281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677302 : List Nat := [5, 1, 1, 1, 5, 1, 2, 1, 6]
def baseStart_1677302 : Nat := 118140960795 + 1677302 * 2 ^ 59
def prefixEnd_1677302 : Nat := 4983230072969 + 3 ^ 40 * 1677302 * 2
def baseEnd_1677302 : Nat := 95695792083077975767915

theorem tailTrace_1677302 : CollatzResearch.WordTrace tailWord_1677302 prefixEnd_1677302 95695792083077975767915 := by
  unfold tailWord_1677302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3823514360589299326277135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40784153179619192813622773 3823514360589299326277135)
  ·
    refine ⟨5735271540883948989415703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3823514360589299326277135 5735271540883948989415703)
    ·
      refine ⟨8602907311325923484123555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5735271540883948989415703 8602907311325923484123555)
      ·
        refine ⟨12904360966988885226185333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8602907311325923484123555 12904360966988885226185333)
        ·
          refine ⟨1209783840655207989954875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12904360966988885226185333 1209783840655207989954875)
          ·
            refine ⟨1814675760982811984932313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209783840655207989954875 1814675760982811984932313)
            ·
              refine ⟨1361006820737108988699235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1814675760982811984932313 1361006820737108988699235)
              ·
                refine ⟨2041510231105663483048853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361006820737108988699235 2041510231105663483048853)
                ·
                  refine ⟨95695792083077975767915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2041510231105663483048853 95695792083077975767915)
                  ·
                    rfl

theorem cell23_1677302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_1677302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677302 prefixEnd_1677302 := by exact prefixLift 1677302
  have htrace : WordTrace (prefixWord ++ tailWord_1677302) baseStart_1677302 baseEnd_1677302 := by
    simpa [prefixWord, tailWord_1677302, baseEnd_1677302] using wordTrace_append hprefix tailTrace_1677302
  have hstable : (prefixWord ++ tailWord_1677302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677302).length < 2 ^ (prefixWord ++ tailWord_1677302).sum := by decide
  have hdescent : baseEnd_1677302 < baseStart_1677302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677324 : List Nat := [2, 2, 1, 2, 3, 1, 1, 11]
def baseStart_1677324 : Nat := 118140960795 + 1677324 * 2 ^ 59
def prefixEnd_1677324 : Nat := 4983230072969 + 3 ^ 40 * 1677324 * 2
def baseEnd_1677324 : Nat := 31899015752670396142079

theorem tailTrace_1677324 : CollatzResearch.WordTrace tailWord_1677324 prefixEnd_1677324 31899015752670396142079 := by
  unfold tailWord_1677324
  simp only [CollatzResearch.WordTrace]
  refine ⟨30588516087674543488867513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40784688116899391318490017 30588516087674543488867513)
  ·
    refine ⟨22941387065755907616650635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30588516087674543488867513 22941387065755907616650635)
    ·
      refine ⟨34412080598633861424975953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22941387065755907616650635 34412080598633861424975953)
      ·
        refine ⟨25809060448975396068731965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34412080598633861424975953 25809060448975396068731965)
        ·
          refine ⟨9678397668365773525774487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25809060448975396068731965 9678397668365773525774487)
          ·
            refine ⟨14517596502548660288661731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9678397668365773525774487 14517596502548660288661731)
            ·
              refine ⟨21776394753822990432992597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14517596502548660288661731 21776394753822990432992597)
              ·
                refine ⟨31899015752670396142079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 21776394753822990432992597 31899015752670396142079)
                ·
                  rfl

theorem cell23_1677324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 11].length) (baseStart_1677324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677324 prefixEnd_1677324 := by exact prefixLift 1677324
  have htrace : WordTrace (prefixWord ++ tailWord_1677324) baseStart_1677324 baseEnd_1677324 := by
    simpa [prefixWord, tailWord_1677324, baseEnd_1677324] using wordTrace_append hprefix tailTrace_1677324
  have hstable : (prefixWord ++ tailWord_1677324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677324).length < 2 ^ (prefixWord ++ tailWord_1677324).sum := by decide
  have hdescent : baseEnd_1677324 < baseStart_1677324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677338 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5]
def baseStart_1677338 : Nat := 118140960795 + 1677338 * 2 ^ 59
def prefixEnd_1677338 : Nat := 4983230072969 + 3 ^ 40 * 1677338 * 2
def baseEnd_1677338 : Nat := 861280614051263641061069

theorem tailTrace_1677338 : CollatzResearch.WordTrace tailWord_1677338 prefixEnd_1677338 861280614051263641061069 := by
  unfold tailWord_1677338
  simp only [CollatzResearch.WordTrace]
  refine ⟨15294385699324591842186167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40785028531532244912496445 15294385699324591842186167)
  ·
    refine ⟨22941578548986887763279251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15294385699324591842186167 22941578548986887763279251)
    ·
      refine ⟨34412367823480331644918877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22941578548986887763279251 34412367823480331644918877)
      ·
        refine ⟨12904637933805124366844579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34412367823480331644918877 12904637933805124366844579)
        ·
          refine ⟨19356956900707686550266869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12904637933805124366844579 19356956900707686550266869)
          ·
            refine ⟨1814714709441345614087519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19356956900707686550266869 1814714709441345614087519)
            ·
              refine ⟨2722072064162018421131279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1814714709441345614087519 2722072064162018421131279)
              ·
                refine ⟨4083108096243027631696919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2722072064162018421131279 4083108096243027631696919)
                ·
                  refine ⟨6124662144364541447545379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4083108096243027631696919 6124662144364541447545379)
                  ·
                    refine ⟨9186993216546812171318069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6124662144364541447545379 9186993216546812171318069)
                    ·
                      refine ⟨861280614051263641061069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9186993216546812171318069 861280614051263641061069)
                      ·
                        rfl

theorem cell23_1677338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_1677338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677338 prefixEnd_1677338 := by exact prefixLift 1677338
  have htrace : WordTrace (prefixWord ++ tailWord_1677338) baseStart_1677338 baseEnd_1677338 := by
    simpa [prefixWord, tailWord_1677338, baseEnd_1677338] using wordTrace_append hprefix tailTrace_1677338
  have hstable : (prefixWord ++ tailWord_1677338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677338).length < 2 ^ (prefixWord ++ tailWord_1677338).sum := by decide
  have hdescent : baseEnd_1677338 < baseStart_1677338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677345 : List Nat := [1, 2, 3, 2, 4, 1, 2, 2, 2, 4]
def baseStart_1677345 : Nat := 118140960795 + 1677345 * 2 ^ 59
def prefixEnd_1677345 : Nat := 4983230072969 + 3 ^ 40 * 1677345 * 2
def baseEnd_1677345 : Nat := 287094736138615037891179

theorem tailTrace_1677345 : CollatzResearch.WordTrace tailWord_1677345 prefixEnd_1677345 287094736138615037891179 := by
  unfold tailWord_1677345
  simp only [CollatzResearch.WordTrace]
  refine ⟨61177798108273007564249489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40785198738848671709499659 61177798108273007564249489)
  ·
    refine ⟨45883348581204755673187117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61177798108273007564249489 45883348581204755673187117)
    ·
      refine ⟨17206255717951783377445169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45883348581204755673187117 17206255717951783377445169)
      ·
        refine ⟨12904691788463837533083877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17206255717951783377445169 12904691788463837533083877)
        ·
          refine ⟨2419629710336969537453227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12904691788463837533083877 2419629710336969537453227)
          ·
            refine ⟨3629444565505454306179841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2419629710336969537453227 3629444565505454306179841)
            ·
              refine ⟨2722083424129090729634881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3629444565505454306179841 2722083424129090729634881)
              ·
                refine ⟨2041562568096818047226161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2722083424129090729634881 2041562568096818047226161)
                ·
                  refine ⟨1531171926072613535419621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2041562568096818047226161 1531171926072613535419621)
                  ·
                    refine ⟨287094736138615037891179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1531171926072613535419621 287094736138615037891179)
                    ·
                      rfl

theorem cell23_1677345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_1677345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677345 prefixEnd_1677345 := by exact prefixLift 1677345
  have htrace : WordTrace (prefixWord ++ tailWord_1677345) baseStart_1677345 baseEnd_1677345 := by
    simpa [prefixWord, tailWord_1677345, baseEnd_1677345] using wordTrace_append hprefix tailTrace_1677345
  have hstable : (prefixWord ++ tailWord_1677345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677345).length < 2 ^ (prefixWord ++ tailWord_1677345).sum := by decide
  have hdescent : baseEnd_1677345 < baseStart_1677345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677358 : List Nat := [4, 1, 3, 1, 1, 4, 1, 8]
def baseStart_1677358 : Nat := 118140960795 + 1677358 * 2 ^ 59
def prefixEnd_1677358 : Nat := 4983230072969 + 3 ^ 40 * 1677358 * 2
def baseEnd_1677358 : Nat := 31899662357939020844851

theorem tailTrace_1677358 : CollatzResearch.WordTrace tailWord_1677358 prefixEnd_1677358 31899662357939020844851 := by
  unfold tailWord_1677358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7647284032153238848059091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40785514838150607189648485 7647284032153238848059091)
  ·
    refine ⟨11470926048229858272088637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7647284032153238848059091 11470926048229858272088637)
    ·
      refine ⟨4301597268086196852033239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11470926048229858272088637 4301597268086196852033239)
      ·
        refine ⟨6452395902129295278049859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4301597268086196852033239 6452395902129295278049859)
        ·
          refine ⟨9678593853193942917074789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6452395902129295278049859 9678593853193942917074789)
          ·
            refine ⟨1814736347473864296951523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9678593853193942917074789 1814736347473864296951523)
            ·
              refine ⟨2722104521210796445427285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1814736347473864296951523 2722104521210796445427285)
              ·
                refine ⟨31899662357939020844851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2722104521210796445427285 31899662357939020844851)
                ·
                  rfl

theorem cell23_1677358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 8].length) (baseStart_1677358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677358 prefixEnd_1677358 := by exact prefixLift 1677358
  have htrace : WordTrace (prefixWord ++ tailWord_1677358) baseStart_1677358 baseEnd_1677358 := by
    simpa [prefixWord, tailWord_1677358, baseEnd_1677358] using wordTrace_append hprefix tailTrace_1677358
  have hstable : (prefixWord ++ tailWord_1677358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677358).length < 2 ^ (prefixWord ++ tailWord_1677358).sum := by decide
  have hdescent : baseEnd_1677358 < baseStart_1677358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677411 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 3]
def baseStart_1677411 : Nat := 118140960795 + 1677411 * 2 ^ 59
def prefixEnd_1677411 : Nat := 4983230072969 + 3 ^ 40 * 1677411 * 2
def baseEnd_1677411 : Nat := 861318098139041855448233

theorem tailTrace_1677411 : CollatzResearch.WordTrace tailWord_1677411 prefixEnd_1677411 861318098139041855448233 := by
  unfold tailWord_1677411
  simp only [CollatzResearch.WordTrace]
  refine ⟨61180205326033900836152087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40786803550689267224101391 61180205326033900836152087)
  ·
    refine ⟨91770307989050851254228131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61180205326033900836152087 91770307989050851254228131)
    ·
      refine ⟨137655461983576276881342197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91770307989050851254228131 137655461983576276881342197)
      ·
        refine ⟨12905199560960275957625831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137655461983576276881342197 12905199560960275957625831)
        ·
          refine ⟨19357799341440413936438747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12905199560960275957625831 19357799341440413936438747)
          ·
            refine ⟨29036699012160620904658121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19357799341440413936438747 29036699012160620904658121)
            ·
              refine ⟨21777524259120465678493591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29036699012160620904658121 21777524259120465678493591)
              ·
                refine ⟨32666286388680698517740387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21777524259120465678493591 32666286388680698517740387)
                ·
                  refine ⟨48999429583021047776610581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32666286388680698517740387 48999429583021047776610581)
                  ·
                    refine ⟨2296848261704111614528621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48999429583021047776610581 2296848261704111614528621)
                    ·
                      refine ⟨861318098139041855448233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2296848261704111614528621 861318098139041855448233)
                      ·
                        rfl

theorem cell23_1677411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_1677411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677411 prefixEnd_1677411 := by exact prefixLift 1677411
  have htrace : WordTrace (prefixWord ++ tailWord_1677411) baseStart_1677411 baseEnd_1677411 := by
    simpa [prefixWord, tailWord_1677411, baseEnd_1677411] using wordTrace_append hprefix tailTrace_1677411
  have hstable : (prefixWord ++ tailWord_1677411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677411).length < 2 ^ (prefixWord ++ tailWord_1677411).sum := by decide
  have hdescent : baseEnd_1677411 < baseStart_1677411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677431 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 7]
def baseStart_1677431 : Nat := 118140960795 + 1677431 * 2 ^ 59
def prefixEnd_1677431 : Nat := 4983230072969 + 3 ^ 40 * 1677431 * 2
def baseEnd_1677431 : Nat := 95703151972459086355349

theorem tailTrace_1677431 : CollatzResearch.WordTrace tailWord_1677431 prefixEnd_1677431 95703151972459086355349 := by
  unfold tailWord_1677431
  simp only [CollatzResearch.WordTrace]
  refine ⟨61180934785961444251880147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40787289857307629501253431 61180934785961444251880147)
  ·
    refine ⟨91771402178942166377820221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61180934785961444251880147 91771402178942166377820221)
    ·
      refine ⟨34414275817103312391682583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91771402178942166377820221 34414275817103312391682583)
      ·
        refine ⟨51621413725654968587523875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34414275817103312391682583 51621413725654968587523875)
        ·
          refine ⟨77432120588482452881285813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51621413725654968587523875 77432120588482452881285813)
          ·
            refine ⟨7259261305170229957620545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77432120588482452881285813 7259261305170229957620545)
            ·
              refine ⟨5444445978877672468215409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7259261305170229957620545 5444445978877672468215409)
              ·
                refine ⟨4083334484158254351161557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5444445978877672468215409 4083334484158254351161557)
                ·
                  refine ⟨95703151972459086355349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4083334484158254351161557 95703151972459086355349)
                  ·
                    rfl

theorem cell23_1677431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 7].length) (baseStart_1677431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677431 prefixEnd_1677431 := by exact prefixLift 1677431
  have htrace : WordTrace (prefixWord ++ tailWord_1677431) baseStart_1677431 baseEnd_1677431 := by
    simpa [prefixWord, tailWord_1677431, baseEnd_1677431] using wordTrace_append hprefix tailTrace_1677431
  have hstable : (prefixWord ++ tailWord_1677431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677431).length < 2 ^ (prefixWord ++ tailWord_1677431).sum := by decide
  have hdescent : baseEnd_1677431 < baseStart_1677431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677476 : List Nat := [2, 3, 1, 2, 4, 2, 2, 1, 2, 2, 2]
def baseStart_1677476 : Nat := 118140960795 + 1677476 * 2 ^ 59
def prefixEnd_1677476 : Nat := 4983230072969 + 3 ^ 40 * 1677476 * 2
def baseEnd_1677476 : Nat := 861351474381584101135435

theorem tailTrace_1677476 : CollatzResearch.WordTrace tailWord_1677476 prefixEnd_1677476 861351474381584101135435 := by
  unfold tailWord_1677476
  simp only [CollatzResearch.WordTrace]
  refine ⟨30591288035399208468634141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40788384047198944624845521 30591288035399208468634141)
  ·
    refine ⟨11471733013274703175737803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30591288035399208468634141 11471733013274703175737803)
    ·
      refine ⟨17207599519912054763606705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11471733013274703175737803 17207599519912054763606705)
      ·
        refine ⟨12905699639934041072705029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17207599519912054763606705 12905699639934041072705029)
        ·
          refine ⟨2419818682487632701132193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12905699639934041072705029 2419818682487632701132193)
          ·
            refine ⟨1814864011865724525849145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2419818682487632701132193 1814864011865724525849145)
            ·
              refine ⟨1361148008899293394386859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1814864011865724525849145 1361148008899293394386859)
              ·
                refine ⟨2041722013348940091580289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361148008899293394386859 2041722013348940091580289)
                ·
                  refine ⟨1531291510011705068685217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2041722013348940091580289 1531291510011705068685217)
                  ·
                    refine ⟨1148468632508778801513913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1531291510011705068685217 1148468632508778801513913)
                    ·
                      refine ⟨861351474381584101135435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1148468632508778801513913 861351474381584101135435)
                      ·
                        rfl

theorem cell23_1677476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_1677476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677476 prefixEnd_1677476 := by exact prefixLift 1677476
  have htrace : WordTrace (prefixWord ++ tailWord_1677476) baseStart_1677476 baseEnd_1677476 := by
    simpa [prefixWord, tailWord_1677476, baseEnd_1677476] using wordTrace_append hprefix tailTrace_1677476
  have hstable : (prefixWord ++ tailWord_1677476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677476).length < 2 ^ (prefixWord ++ tailWord_1677476).sum := by decide
  have hdescent : baseEnd_1677476 < baseStart_1677476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677498 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4]
def baseStart_1677498 : Nat := 118140960795 + 1677498 * 2 ^ 59
def prefixEnd_1677498 : Nat := 4983230072969 + 3 ^ 40 * 1677498 * 2
def baseEnd_1677498 : Nat := 861362770955983015060333

theorem tailTrace_1677498 : CollatzResearch.WordTrace tailWord_1677498 prefixEnd_1677498 861362770955983015060333 := by
  unfold tailWord_1677498
  simp only [CollatzResearch.WordTrace]
  refine ⟨15295844619179678673642287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40788918984479143129712765 15295844619179678673642287)
  ·
    refine ⟨22943766928769518010463431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15295844619179678673642287 22943766928769518010463431)
    ·
      refine ⟨34415650393154277015695147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22943766928769518010463431 34415650393154277015695147)
      ·
        refine ⟨51623475589731415523542721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34415650393154277015695147 51623475589731415523542721)
        ·
          refine ⟨38717606692298561642657041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51623475589731415523542721 38717606692298561642657041)
          ·
            refine ⟨29038205019223921231992781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38717606692298561642657041 29038205019223921231992781)
            ·
              refine ⟨10889326882208970461997293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29038205019223921231992781 10889326882208970461997293)
              ·
                refine ⟨4083497580828363923248985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10889326882208970461997293 4083497580828363923248985)
                ·
                  refine ⟨3062623185621272942436739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4083497580828363923248985 3062623185621272942436739)
                  ·
                    refine ⟨4593934778431909413655109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3062623185621272942436739 4593934778431909413655109)
                    ·
                      refine ⟨861362770955983015060333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4593934778431909413655109 861362770955983015060333)
                      ·
                        rfl

theorem cell23_1677498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_1677498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677498 prefixEnd_1677498 := by exact prefixLift 1677498
  have htrace : WordTrace (prefixWord ++ tailWord_1677498) baseStart_1677498 baseEnd_1677498 := by
    simpa [prefixWord, tailWord_1677498, baseEnd_1677498] using wordTrace_append hprefix tailTrace_1677498
  have hstable : (prefixWord ++ tailWord_1677498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677498).length < 2 ^ (prefixWord ++ tailWord_1677498).sum := by decide
  have hdescent : baseEnd_1677498 < baseStart_1677498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677516 : List Nat := [2, 2, 1, 6, 2, 1, 2, 2, 5]
def baseStart_1677516 : Nat := 118140960795 + 1677516 * 2 ^ 59
def prefixEnd_1677516 : Nat := 4983230072969 + 3 ^ 40 * 1677516 * 2
def baseEnd_1677516 : Nat := 95708001511973771626139

theorem tailTrace_1677516 : CollatzResearch.WordTrace tailWord_1677516 prefixEnd_1677516 95708001511973771626139 := by
  unfold tailWord_1677516
  simp only [CollatzResearch.WordTrace]
  refine ⟨30592017495326751884362201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40789356660435669179149601 30592017495326751884362201)
  ·
    refine ⟨22944013121495063913271651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30592017495326751884362201 22944013121495063913271651)
    ·
      refine ⟨34416019682242595869907477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22944013121495063913271651 34416019682242595869907477)
      ·
        refine ⟨1613250922605121681401913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34416019682242595869907477 1613250922605121681401913)
        ·
          refine ⟨1209938191953841261051435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1613250922605121681401913 1209938191953841261051435)
          ·
            refine ⟨1814907287930761891577153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209938191953841261051435 1814907287930761891577153)
            ·
              refine ⟨1361180465948071418682865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1814907287930761891577153 1361180465948071418682865)
              ·
                refine ⟨1020885349461053564012149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1361180465948071418682865 1020885349461053564012149)
                ·
                  refine ⟨95708001511973771626139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1020885349461053564012149 95708001511973771626139)
                  ·
                    rfl

theorem cell23_1677516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 5].length) (baseStart_1677516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677516 prefixEnd_1677516 := by exact prefixLift 1677516
  have htrace : WordTrace (prefixWord ++ tailWord_1677516) baseStart_1677516 baseEnd_1677516 := by
    simpa [prefixWord, tailWord_1677516, baseEnd_1677516] using wordTrace_append hprefix tailTrace_1677516
  have hstable : (prefixWord ++ tailWord_1677516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677516).length < 2 ^ (prefixWord ++ tailWord_1677516).sum := by decide
  have hdescent : baseEnd_1677516 < baseStart_1677516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677521 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 8]
def baseStart_1677521 : Nat := 118140960795 + 1677521 * 2 ^ 59
def prefixEnd_1677521 : Nat := 4983230072969 + 3 ^ 40 * 1677521 * 2
def baseEnd_1677521 : Nat := 95708286779004047230303

theorem tailTrace_1677521 : CollatzResearch.WordTrace tailWord_1677521 prefixEnd_1677521 95708286779004047230303 := by
  unfold tailWord_1677521
  simp only [CollatzResearch.WordTrace]
  refine ⟨61184217355635389622656417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40789478237090259748437611 61184217355635389622656417)
  ·
    refine ⟨45888163016726542216992313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61184217355635389622656417 45888163016726542216992313)
    ·
      refine ⟨34416122262544906662744235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45888163016726542216992313 34416122262544906662744235)
      ·
        refine ⟨51624183393817359994116353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34416122262544906662744235 51624183393817359994116353)
        ·
          refine ⟨38718137545363019995587265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51624183393817359994116353 38718137545363019995587265)
          ·
            refine ⟨29038603159022264996690449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38718137545363019995587265 29038603159022264996690449)
            ·
              refine ⟨21778952369266698747517837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29038603159022264996690449 21778952369266698747517837)
              ·
                refine ⟨8167107138475012030319189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21778952369266698747517837 8167107138475012030319189)
                ·
                  refine ⟨95708286779004047230303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8167107138475012030319189 95708286779004047230303)
                  ·
                    rfl

theorem cell23_1677521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 8].length) (baseStart_1677521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677521 prefixEnd_1677521 := by exact prefixLift 1677521
  have htrace : WordTrace (prefixWord ++ tailWord_1677521) baseStart_1677521 baseEnd_1677521 := by
    simpa [prefixWord, tailWord_1677521, baseEnd_1677521] using wordTrace_append hprefix tailTrace_1677521
  have hstable : (prefixWord ++ tailWord_1677521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677521).length < 2 ^ (prefixWord ++ tailWord_1677521).sum := by decide
  have hdescent : baseEnd_1677521 < baseStart_1677521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677549 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 2, 1, 4]
def baseStart_1677549 : Nat := 118140960795 + 1677549 * 2 ^ 59
def prefixEnd_1677549 : Nat := 4983230072969 + 3 ^ 40 * 1677549 * 2
def baseEnd_1677549 : Nat := 861388958469362315522599

theorem tailTrace_1677549 : CollatzResearch.WordTrace tailWord_1677549 prefixEnd_1677549 861388958469362315522599 := by
  unfold tailWord_1677549
  simp only [CollatzResearch.WordTrace]
  refine ⟨61185238599533950404675701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40790159066355966936450467 61185238599533950404675701)
  ·
    refine ⟨5736116118706307850438347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61185238599533950404675701 5736116118706307850438347)
    ·
      refine ⟨8604174178059461775657521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5736116118706307850438347 8604174178059461775657521)
      ·
        refine ⟨6453130633544596331743141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8604174178059461775657521 6453130633544596331743141)
        ·
          refine ⟨1209961993789611812201839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6453130633544596331743141 1209961993789611812201839)
          ·
            refine ⟨1814942990684417718302759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209961993789611812201839 1814942990684417718302759)
            ·
              refine ⟨2722414486026626577454139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1814942990684417718302759 2722414486026626577454139)
              ·
                refine ⟨4083621729039939866181209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2722414486026626577454139 4083621729039939866181209)
                ·
                  refine ⟨3062716296779954899635907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4083621729039939866181209 3062716296779954899635907)
                  ·
                    refine ⟨4594074445169932349453861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3062716296779954899635907 4594074445169932349453861)
                    ·
                      refine ⟨861388958469362315522599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4594074445169932349453861 861388958469362315522599)
                      ·
                        rfl

theorem cell23_1677549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_1677549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677549 prefixEnd_1677549 := by exact prefixLift 1677549
  have htrace : WordTrace (prefixWord ++ tailWord_1677549) baseStart_1677549 baseEnd_1677549 := by
    simpa [prefixWord, tailWord_1677549, baseEnd_1677549] using wordTrace_append hprefix tailTrace_1677549
  have hstable : (prefixWord ++ tailWord_1677549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677549).length < 2 ^ (prefixWord ++ tailWord_1677549).sum := by decide
  have hdescent : baseEnd_1677549 < baseStart_1677549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677572 : List Nat := [2, 3, 2, 2, 3, 2, 1, 2, 6]
def baseStart_1677572 : Nat := 118140960795 + 1677572 * 2 ^ 59
def prefixEnd_1677572 : Nat := 4983230072969 + 3 ^ 40 * 1677572 * 2
def baseEnd_1677572 : Nat := 95711196502712858392777

theorem tailTrace_1677572 : CollatzResearch.WordTrace tailWord_1677572 prefixEnd_1677572 95711196502712858392777 := by
  unfold tailWord_1677572
  simp only [CollatzResearch.WordTrace]
  refine ⟨30593038739225312666381485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40790718318967083555175313 30593038739225312666381485)
  ·
    refine ⟨11472389527209492249893057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30593038739225312666381485 11472389527209492249893057)
    ·
      refine ⟨8604292145407119187419793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11472389527209492249893057 8604292145407119187419793)
      ·
        refine ⟨6453219109055339390564845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8604292145407119187419793 6453219109055339390564845)
        ·
          refine ⟨2419957165895752271461817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6453219109055339390564845 2419957165895752271461817)
          ·
            refine ⟨1814967874421814203596363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2419957165895752271461817 1814967874421814203596363)
            ·
              refine ⟨2722451811632721305394545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1814967874421814203596363 2722451811632721305394545)
              ·
                refine ⟨2041838858724540979045909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2722451811632721305394545 2041838858724540979045909)
                ·
                  refine ⟨95711196502712858392777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2041838858724540979045909 95711196502712858392777)
                  ·
                    rfl

theorem cell23_1677572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_1677572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677572 prefixEnd_1677572 := by exact prefixLift 1677572
  have htrace : WordTrace (prefixWord ++ tailWord_1677572) baseStart_1677572 baseEnd_1677572 := by
    simpa [prefixWord, tailWord_1677572, baseEnd_1677572] using wordTrace_append hprefix tailTrace_1677572
  have hstable : (prefixWord ++ tailWord_1677572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677572).length < 2 ^ (prefixWord ++ tailWord_1677572).sum := by decide
  have hdescent : baseEnd_1677572 < baseStart_1677572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677582 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3]
def baseStart_1677582 : Nat := 118140960795 + 1677582 * 2 ^ 59
def prefixEnd_1677582 : Nat := 4983230072969 + 3 ^ 40 * 1677582 * 2
def baseEnd_1677582 : Nat := 861405903330960686409947

theorem tailTrace_1677582 : CollatzResearch.WordTrace tailWord_1677582 prefixEnd_1677582 861405903330960686409947 := by
  unfold tailWord_1677582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7648305276051799630078375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40790961472276264693751333 7648305276051799630078375)
  ·
    refine ⟨11472457914077699445117563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7648305276051799630078375 11472457914077699445117563)
    ·
      refine ⟨17208686871116549167676345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11472457914077699445117563 17208686871116549167676345)
      ·
        refine ⟨12906515153337411875757259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17208686871116549167676345 12906515153337411875757259)
        ·
          refine ⟨19359772730006117813635889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12906515153337411875757259 19359772730006117813635889)
          ·
            refine ⟨14519829547504588360226917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19359772730006117813635889 14519829547504588360226917)
            ·
              refine ⟨2722468040157110317542547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14519829547504588360226917 2722468040157110317542547)
              ·
                refine ⟨4083702060235665476313821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2722468040157110317542547 4083702060235665476313821)
                ·
                  refine ⟨1531388272588374553617683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4083702060235665476313821 1531388272588374553617683)
                  ·
                    refine ⟨2297082408882561830426525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1531388272588374553617683 2297082408882561830426525)
                    ·
                      refine ⟨861405903330960686409947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2297082408882561830426525 861405903330960686409947)
                      ·
                        rfl

theorem cell23_1677582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_1677582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677582 prefixEnd_1677582 := by exact prefixLift 1677582
  have htrace : WordTrace (prefixWord ++ tailWord_1677582) baseStart_1677582 baseEnd_1677582 := by
    simpa [prefixWord, tailWord_1677582, baseEnd_1677582] using wordTrace_append hprefix tailTrace_1677582
  have hstable : (prefixWord ++ tailWord_1677582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677582).length < 2 ^ (prefixWord ++ tailWord_1677582).sum := by decide
  have hdescent : baseEnd_1677582 < baseStart_1677582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677602 : List Nat := [3, 3, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_1677602 : Nat := 118140960795 + 1677602 * 2 ^ 59
def prefixEnd_1677602 : Nat := 4983230072969 + 3 ^ 40 * 1677602 * 2
def baseEnd_1677602 : Nat := 287138724314683536053285

theorem tailTrace_1677602 : CollatzResearch.WordTrace tailWord_1677602 prefixEnd_1677602 287138724314683536053285 := by
  unfold tailWord_1677602
  simp only [CollatzResearch.WordTrace]
  refine ⟨15296792917085485114088765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40791447778894626970903373 15296792917085485114088765)
  ·
    refine ⟨5736297343907056917783287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15296792917085485114088765 5736297343907056917783287)
    ·
      refine ⟨8604446015860585376674931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5736297343907056917783287 8604446015860585376674931)
      ·
        refine ⟨12906669023790878065012397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8604446015860585376674931 12906669023790878065012397)
        ·
          refine ⟨4840000883921579274379649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12906669023790878065012397 4840000883921579274379649)
          ·
            refine ⟨3630000662941184455784737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4840000883921579274379649 3630000662941184455784737)
            ·
              refine ⟨2722500497205888341838553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3630000662941184455784737 2722500497205888341838553)
              ·
                refine ⟨2041875372904416256378915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2722500497205888341838553 2041875372904416256378915)
                ·
                  refine ⟨3062813059356624384568373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2041875372904416256378915 3062813059356624384568373)
                  ·
                    refine ⟨287138724314683536053285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3062813059356624384568373 287138724314683536053285)
                    ·
                      rfl

theorem cell23_1677602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_1677602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677602 prefixEnd_1677602 := by exact prefixLift 1677602
  have htrace : WordTrace (prefixWord ++ tailWord_1677602) baseStart_1677602 baseEnd_1677602 := by
    simpa [prefixWord, tailWord_1677602, baseEnd_1677602] using wordTrace_append hprefix tailTrace_1677602
  have hstable : (prefixWord ++ tailWord_1677602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677602).length < 2 ^ (prefixWord ++ tailWord_1677602).sum := by decide
  have hdescent : baseEnd_1677602 < baseStart_1677602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677625 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1677625 : Nat := 118140960795 + 1677625 * 2 ^ 59
def prefixEnd_1677625 : Nat := 4983230072969 + 3 ^ 40 * 1677625 * 2
def baseEnd_1677625 : Nat := 861427982999104018172249

theorem tailTrace_1677625 : CollatzResearch.WordTrace tailWord_1677625 prefixEnd_1677625 861427982999104018172249 := by
  unfold tailWord_1677625
  simp only [CollatzResearch.WordTrace]
  refine ⟨61188010547258615384442329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40792007031505743589628219 61188010547258615384442329)
  ·
    refine ⟨45891007910443961538331747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61188010547258615384442329 45891007910443961538331747)
    ·
      refine ⟨68836511865665942307497621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45891007910443961538331747 68836511865665942307497621)
      ·
        refine ⟨3226711493703091045663951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68836511865665942307497621 3226711493703091045663951)
        ·
          refine ⟨4840067240554636568495927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3226711493703091045663951 4840067240554636568495927)
          ·
            refine ⟨7260100860831954852743891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4840067240554636568495927 7260100860831954852743891)
            ·
              refine ⟨10890151291247932279115837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7260100860831954852743891 10890151291247932279115837)
              ·
                refine ⟨4083806734217974604668439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10890151291247932279115837 4083806734217974604668439)
                ·
                  refine ⟨6125710101326961907002659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4083806734217974604668439 6125710101326961907002659)
                  ·
                    refine ⟨9188565151990442860503989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6125710101326961907002659 9188565151990442860503989)
                    ·
                      refine ⟨861427982999104018172249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9188565151990442860503989 861427982999104018172249)
                      ·
                        rfl

theorem cell23_1677625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1677625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677625 prefixEnd_1677625 := by exact prefixLift 1677625
  have htrace : WordTrace (prefixWord ++ tailWord_1677625) baseStart_1677625 baseEnd_1677625 := by
    simpa [prefixWord, tailWord_1677625, baseEnd_1677625] using wordTrace_append hprefix tailTrace_1677625
  have hstable : (prefixWord ++ tailWord_1677625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677625).length < 2 ^ (prefixWord ++ tailWord_1677625).sum := by decide
  have hdescent : baseEnd_1677625 < baseStart_1677625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677633 : List Nat := [1, 2, 5, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_1677633 : Nat := 118140960795 + 1677633 * 2 ^ 59
def prefixEnd_1677633 : Nat := 4983230072969 + 3 ^ 40 * 1677633 * 2
def baseEnd_1677633 : Nat := 861432090844339986872213

theorem tailTrace_1677633 : CollatzResearch.WordTrace tailWord_1677633 prefixEnd_1677633 861432090844339986872213 := by
  unfold tailWord_1677633
  simp only [CollatzResearch.WordTrace]
  refine ⟨61188302331229632750733553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40792201554153088500489035 61188302331229632750733553)
  ·
    refine ⟨45891226748422224563050165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61188302331229632750733553 45891226748422224563050165)
    ·
      refine ⟨4302302507664583552785953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45891226748422224563050165 4302302507664583552785953)
      ·
        refine ⟨3226726880748437664589465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4302302507664583552785953 3226726880748437664589465)
        ·
          refine ⟨2420045160561328248442099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3226726880748437664589465 2420045160561328248442099)
          ·
            refine ⟨3630067740841992372663149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420045160561328248442099 3630067740841992372663149)
            ·
              refine ⟨1361275402815747139748681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3630067740841992372663149 1361275402815747139748681)
              ·
                refine ⟨1020956552111810354811511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1361275402815747139748681 1020956552111810354811511)
                ·
                  refine ⟨1531434828167715532217267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020956552111810354811511 1531434828167715532217267)
                  ·
                    refine ⟨2297152242251573298325901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1531434828167715532217267 2297152242251573298325901)
                    ·
                      refine ⟨861432090844339986872213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2297152242251573298325901 861432090844339986872213)
                      ·
                        rfl

theorem cell23_1677633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_1677633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677633 prefixEnd_1677633 := by exact prefixLift 1677633
  have htrace : WordTrace (prefixWord ++ tailWord_1677633) baseStart_1677633 baseEnd_1677633 := by
    simpa [prefixWord, tailWord_1677633, baseEnd_1677633] using wordTrace_append hprefix tailTrace_1677633
  have hstable : (prefixWord ++ tailWord_1677633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677633).length < 2 ^ (prefixWord ++ tailWord_1677633).sum := by decide
  have hdescent : baseEnd_1677633 < baseStart_1677633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677649 : List Nat := [1, 2, 2, 1, 4, 4, 2, 1, 2, 4]
def baseStart_1677649 : Nat := 118140960795 + 1677649 * 2 ^ 59
def prefixEnd_1677649 : Nat := 4983230072969 + 3 ^ 40 * 1677649 * 2
def baseEnd_1677649 : Nat := 287146768844937308090713

theorem tailTrace_1677649 : CollatzResearch.WordTrace tailWord_1677649 prefixEnd_1677649 287146768844937308090713 := by
  unfold tailWord_1677649
  simp only [CollatzResearch.WordTrace]
  refine ⟨61188885899171667483316001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40792590599447778322210667 61188885899171667483316001)
  ·
    refine ⟨45891664424378750612487001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61188885899171667483316001 45891664424378750612487001)
    ·
      refine ⟨34418748318284062959365251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45891664424378750612487001 34418748318284062959365251)
      ·
        refine ⟨51628122477426094439047877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34418748318284062959365251 51628122477426094439047877)
        ·
          refine ⟨9680272964517392707321477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51628122477426094439047877 9680272964517392707321477)
          ·
            refine ⟨1815051180847011132622777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9680272964517392707321477 1815051180847011132622777)
            ·
              refine ⟨1361288385635258349467083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1815051180847011132622777 1361288385635258349467083)
              ·
                refine ⟨2041932578452887524200625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361288385635258349467083 2041932578452887524200625)
                ·
                  refine ⟨1531449433839665643150469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2041932578452887524200625 1531449433839665643150469)
                  ·
                    refine ⟨287146768844937308090713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1531449433839665643150469 287146768844937308090713)
                    ·
                      rfl

theorem cell23_1677649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_1677649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677649 prefixEnd_1677649 := by exact prefixLift 1677649
  have htrace : WordTrace (prefixWord ++ tailWord_1677649) baseStart_1677649 baseEnd_1677649 := by
    simpa [prefixWord, tailWord_1677649, baseEnd_1677649] using wordTrace_append hprefix tailTrace_1677649
  have hstable : (prefixWord ++ tailWord_1677649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677649).length < 2 ^ (prefixWord ++ tailWord_1677649).sum := by decide
  have hdescent : baseEnd_1677649 < baseStart_1677649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677655 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 3]
def baseStart_1677655 : Nat := 118140960795 + 1677655 * 2 ^ 59
def prefixEnd_1677655 : Nat := 4983230072969 + 3 ^ 40 * 1677655 * 2
def baseEnd_1677655 : Nat := 861443387418738900797111

theorem tailTrace_1677655 : CollatzResearch.WordTrace tailWord_1677655 prefixEnd_1677655 861443387418738900797111 := by
  unfold tailWord_1677655
  simp only [CollatzResearch.WordTrace]
  refine ⟨61189104737149930508034419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40792736491433287005356279 61189104737149930508034419)
  ·
    refine ⟨91783657105724895762051629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61189104737149930508034419 91783657105724895762051629)
    ·
      refine ⟨34418871414646835910769361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91783657105724895762051629 34418871414646835910769361)
      ·
        refine ⟨25814153560985126933077021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34418871414646835910769361 25814153560985126933077021)
        ·
          refine ⟨9680307585369422599903883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25814153560985126933077021 9680307585369422599903883)
          ·
            refine ⟨14520461378054133899855825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9680307585369422599903883 14520461378054133899855825)
            ·
              refine ⟨10890346033540600424891869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14520461378054133899855825 10890346033540600424891869)
              ·
                refine ⟨4083879762577725159334451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10890346033540600424891869 4083879762577725159334451)
                ·
                  refine ⟨6125819643866587739001677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4083879762577725159334451 6125819643866587739001677)
                  ·
                    refine ⟨2297182366449970402125629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6125819643866587739001677 2297182366449970402125629)
                    ·
                      refine ⟨861443387418738900797111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2297182366449970402125629 861443387418738900797111)
                      ·
                        rfl

theorem cell23_1677655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_1677655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677655 prefixEnd_1677655 := by exact prefixLift 1677655
  have htrace : WordTrace (prefixWord ++ tailWord_1677655) baseStart_1677655 baseEnd_1677655 := by
    simpa [prefixWord, tailWord_1677655, baseEnd_1677655] using wordTrace_append hprefix tailTrace_1677655
  have hstable : (prefixWord ++ tailWord_1677655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677655).length < 2 ^ (prefixWord ++ tailWord_1677655).sum := by decide
  have hdescent : baseEnd_1677655 < baseStart_1677655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677672 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_1677672 : Nat := 118140960795 + 1677672 * 2 ^ 59
def prefixEnd_1677672 : Nat := 4983230072969 + 3 ^ 40 * 1677672 * 2
def baseEnd_1677672 : Nat := 861452116589865334284533

theorem tailTrace_1677672 : CollatzResearch.WordTrace tailWord_1677672 prefixEnd_1677672 861452116589865334284533 := by
  unfold tailWord_1677672
  simp only [CollatzResearch.WordTrace]
  refine ⟨30594862389044171205701635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40793149852058894940935513 30594862389044171205701635)
  ·
    refine ⟨45892293583566256808552453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30594862389044171205701635 45892293583566256808552453)
    ·
      refine ⟨8604805046918673151603585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45892293583566256808552453 8604805046918673151603585)
      ·
        refine ⟨6453603785189004863702689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8604805046918673151603585 6453603785189004863702689)
        ·
          refine ⟨4840202838891753647777017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6453603785189004863702689 4840202838891753647777017)
          ·
            refine ⟨3630152129168815235832763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4840202838891753647777017 3630152129168815235832763)
            ·
              refine ⟨5445228193753222853749145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3630152129168815235832763 5445228193753222853749145)
              ·
                refine ⟨4083921145314917140311859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5445228193753222853749145 4083921145314917140311859)
                ·
                  refine ⟨6125881717972375710467789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4083921145314917140311859 6125881717972375710467789)
                  ·
                    refine ⟨2297205644239640891425421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6125881717972375710467789 2297205644239640891425421)
                    ·
                      refine ⟨861452116589865334284533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2297205644239640891425421 861452116589865334284533)
                      ·
                        rfl

theorem cell23_1677672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_1677672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677672 prefixEnd_1677672 := by exact prefixLift 1677672
  have htrace : WordTrace (prefixWord ++ tailWord_1677672) baseStart_1677672 baseEnd_1677672 := by
    simpa [prefixWord, tailWord_1677672, baseEnd_1677672] using wordTrace_append hprefix tailTrace_1677672
  have hstable : (prefixWord ++ tailWord_1677672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677672).length < 2 ^ (prefixWord ++ tailWord_1677672).sum := by decide
  have hdescent : baseEnd_1677672 < baseStart_1677672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677705 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 2, 6]
def baseStart_1677705 : Nat := 118140960795 + 1677705 * 2 ^ 59
def prefixEnd_1677705 : Nat := 4983230072969 + 3 ^ 40 * 1677705 * 2
def baseEnd_1677705 : Nat := 287156353817154568390627

theorem tailTrace_1677705 : CollatzResearch.WordTrace tailWord_1677705 prefixEnd_1677705 287156353817154568390627 := by
  unfold tailWord_1677705
  simp only [CollatzResearch.WordTrace]
  refine ⟨61190928386968789047354569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40793952257979192698236379 61190928386968789047354569)
  ·
    refine ⟨45893196290226591785515927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61190928386968789047354569 45893196290226591785515927)
    ·
      refine ⟨68839794435339887678273891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45893196290226591785515927 68839794435339887678273891)
      ·
        refine ⟨103259691653009831517410837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68839794435339887678273891 103259691653009831517410837)
        ·
          refine ⟨4840298046234835852378633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103259691653009831517410837 4840298046234835852378633)
          ·
            refine ⟨3630223534676126889283975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4840298046234835852378633 3630223534676126889283975)
            ·
              refine ⟨5445335302014190333925963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3630223534676126889283975 5445335302014190333925963)
              ·
                refine ⟨8168002953021285500888945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5445335302014190333925963 8168002953021285500888945)
                ·
                  refine ⟨6126002214765964125666709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8168002953021285500888945 6126002214765964125666709)
                  ·
                    refine ⟨287156353817154568390627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6126002214765964125666709 287156353817154568390627)
                    ·
                      rfl

theorem cell23_1677705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 6].length) (baseStart_1677705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677705 prefixEnd_1677705 := by exact prefixLift 1677705
  have htrace : WordTrace (prefixWord ++ tailWord_1677705) baseStart_1677705 baseEnd_1677705 := by
    simpa [prefixWord, tailWord_1677705, baseEnd_1677705] using wordTrace_append hprefix tailTrace_1677705
  have hstable : (prefixWord ++ tailWord_1677705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677705).length < 2 ^ (prefixWord ++ tailWord_1677705).sum := by decide
  have hdescent : baseEnd_1677705 < baseStart_1677705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677782 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_1677782 : Nat := 118140960795 + 1677782 * 2 ^ 59
def prefixEnd_1677782 : Nat := 4983230072969 + 3 ^ 40 * 1677782 * 2
def baseEnd_1677782 : Nat := 287169533153953301303009

theorem tailTrace_1677782 : CollatzResearch.WordTrace tailWord_1677782 prefixEnd_1677782 287169533153953301303009 := by
  unfold tailWord_1677782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3824608550480614449869225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40795824538459887465271733 3824608550480614449869225)
  ·
    refine ⟨2868456412860460837401919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3824608550480614449869225 2868456412860460837401919)
    ·
      refine ⟨4302684619290691256102879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2868456412860460837401919 4302684619290691256102879)
      ·
        refine ⟨6454026928936036884154319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4302684619290691256102879 6454026928936036884154319)
        ·
          refine ⟨9681040393404055326231479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6454026928936036884154319 9681040393404055326231479)
          ·
            refine ⟨14521560590106082989347219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9681040393404055326231479 14521560590106082989347219)
            ·
              refine ⟨21782340885159124484020829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14521560590106082989347219 21782340885159124484020829)
              ·
                refine ⟨8168377831934671681507811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21782340885159124484020829 8168377831934671681507811)
                ·
                  refine ⟨12252566747902007522261717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8168377831934671681507811 12252566747902007522261717)
                  ·
                    refine ⟨287169533153953301303009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12252566747902007522261717 287169533153953301303009)
                    ·
                      rfl

theorem cell23_1677782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_1677782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677782 prefixEnd_1677782 := by exact prefixLift 1677782
  have htrace : WordTrace (prefixWord ++ tailWord_1677782) baseStart_1677782 baseEnd_1677782 := by
    simpa [prefixWord, tailWord_1677782, baseEnd_1677782] using wordTrace_append hprefix tailTrace_1677782
  have hstable : (prefixWord ++ tailWord_1677782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677782).length < 2 ^ (prefixWord ++ tailWord_1677782).sum := by decide
  have hdescent : baseEnd_1677782 < baseStart_1677782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677785 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 1, 3, 4]
def baseStart_1677785 : Nat := 118140960795 + 1677785 * 2 ^ 59
def prefixEnd_1677785 : Nat := 4983230072969 + 3 ^ 40 * 1677785 * 2
def baseEnd_1677785 : Nat := 861510139903823392171513

theorem tailTrace_1677785 : CollatzResearch.WordTrace tailWord_1677785 prefixEnd_1677785 861510139903823392171513 := by
  unfold tailWord_1677785
  simp only [CollatzResearch.WordTrace]
  refine ⟨61193846226678962710266809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40795897484452641806844539 61193846226678962710266809)
  ·
    refine ⟨45895384670009222032700107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61193846226678962710266809 45895384670009222032700107)
    ·
      refine ⟨68843077005013833049050161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45895384670009222032700107 68843077005013833049050161)
      ·
        refine ⟨51632307753760374786787621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68843077005013833049050161 51632307753760374786787621)
        ·
          refine ⟨9681057703830070272522679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51632307753760374786787621 9681057703830070272522679)
          ·
            refine ⟨14521586555745105408784019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9681057703830070272522679 14521586555745105408784019)
            ·
              refine ⟨21782379833617658113176029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14521586555745105408784019 21782379833617658113176029)
              ·
                refine ⟨8168392437606621792441011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21782379833617658113176029 8168392437606621792441011)
                ·
                  refine ⟨12252588656409932688661517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8168392437606621792441011 12252588656409932688661517)
                  ·
                    refine ⟨4594720746153724758248069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12252588656409932688661517 4594720746153724758248069)
                    ·
                      refine ⟨861510139903823392171513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4594720746153724758248069 861510139903823392171513)
                      ·
                        rfl

theorem cell23_1677785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_1677785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677785 prefixEnd_1677785 := by exact prefixLift 1677785
  have htrace : WordTrace (prefixWord ++ tailWord_1677785) baseStart_1677785 baseEnd_1677785 := by
    simpa [prefixWord, tailWord_1677785, baseEnd_1677785] using wordTrace_append hprefix tailTrace_1677785
  have hstable : (prefixWord ++ tailWord_1677785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677785).length < 2 ^ (prefixWord ++ tailWord_1677785).sum := by decide
  have hdescent : baseEnd_1677785 < baseStart_1677785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677802 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_1677802 : Nat := 118140960795 + 1677802 * 2 ^ 59
def prefixEnd_1677802 : Nat := 4983230072969 + 3 ^ 40 * 1677802 * 2
def baseEnd_1677802 : Nat := 861518869074949825658935

theorem tailTrace_1677802 : CollatzResearch.WordTrace tailWord_1677802 prefixEnd_1677802 861518869074949825658935 := by
  unfold tailWord_1677802
  simp only [CollatzResearch.WordTrace]
  refine ⟨15298616566904343653408915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40796310845078249742423773 15298616566904343653408915)
  ·
    refine ⟨22947924850356515480113373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15298616566904343653408915 22947924850356515480113373)
    ·
      refine ⟨8605471818883693305042515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22947924850356515480113373 8605471818883693305042515)
      ·
        refine ⟨12908207728325539957563773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8605471818883693305042515 12908207728325539957563773)
        ·
          refine ⟨4840577898122077484086415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12908207728325539957563773 4840577898122077484086415)
          ·
            refine ⟨7260866847183116226129623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4840577898122077484086415 7260866847183116226129623)
            ·
              refine ⟨10891300270774674339194435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7260866847183116226129623 10891300270774674339194435)
              ·
                refine ⟨16336950406162011508791653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10891300270774674339194435 16336950406162011508791653)
                ·
                  refine ⟨3063178201155377157898435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16336950406162011508791653 3063178201155377157898435)
                  ·
                    refine ⟨4594767301733065736847653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3063178201155377157898435 4594767301733065736847653)
                    ·
                      refine ⟨861518869074949825658935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4594767301733065736847653 861518869074949825658935)
                      ·
                        rfl

theorem cell23_1677802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_1677802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677802 prefixEnd_1677802 := by exact prefixLift 1677802
  have htrace : WordTrace (prefixWord ++ tailWord_1677802) baseStart_1677802 baseEnd_1677802 := by
    simpa [prefixWord, tailWord_1677802, baseEnd_1677802] using wordTrace_append hprefix tailTrace_1677802
  have hstable : (prefixWord ++ tailWord_1677802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677802).length < 2 ^ (prefixWord ++ tailWord_1677802).sum := by decide
  have hdescent : baseEnd_1677802 < baseStart_1677802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677902 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 1, 6]
def baseStart_1677902 : Nat := 118140960795 + 1677902 * 2 ^ 59
def prefixEnd_1677902 : Nat := 4983230072969 + 3 ^ 40 * 1677902 * 2
def baseEnd_1677902 : Nat := 287190072380133144802825

theorem tailTrace_1677902 : CollatzResearch.WordTrace tailWord_1677902 prefixEnd_1677902 287190072380133144802825 := by
  unfold tailWord_1677902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7649764195906886461534495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40798742378170061128183973 7649764195906886461534495)
  ·
    refine ⟨11474646293860329692301743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7649764195906886461534495 11474646293860329692301743)
    ·
      refine ⟨17211969440790494538452615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11474646293860329692301743 17211969440790494538452615)
      ·
        refine ⟨25817954161185741807678923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17211969440790494538452615 25817954161185741807678923)
        ·
          refine ⟨38726931241778612711518385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25817954161185741807678923 38726931241778612711518385)
          ·
            refine ⟨29045198431333959533638789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38726931241778612711518385 29045198431333959533638789)
            ·
              refine ⟨5445974705875117412557273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29045198431333959533638789 5445974705875117412557273)
              ·
                refine ⟨4084481029406338059417955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5445974705875117412557273 4084481029406338059417955)
                ·
                  refine ⟨6126721544109507089126933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4084481029406338059417955 6126721544109507089126933)
                  ·
                    refine ⟨287190072380133144802825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6126721544109507089126933 287190072380133144802825)
                    ·
                      rfl

theorem cell23_1677902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_1677902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677902 prefixEnd_1677902 := by exact prefixLift 1677902
  have htrace : WordTrace (prefixWord ++ tailWord_1677902) baseStart_1677902 baseEnd_1677902 := by
    simpa [prefixWord, tailWord_1677902, baseEnd_1677902] using wordTrace_append hprefix tailTrace_1677902
  have hstable : (prefixWord ++ tailWord_1677902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677902).length < 2 ^ (prefixWord ++ tailWord_1677902).sum := by decide
  have hdescent : baseEnd_1677902 < baseStart_1677902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677936 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 1, 6]
def baseStart_1677936 : Nat := 118140960795 + 1677936 * 2 ^ 59
def prefixEnd_1677936 : Nat := 4983230072969 + 3 ^ 40 * 1677936 * 2
def baseEnd_1677936 : Nat := 287195891827550767127773

theorem tailTrace_1677936 : CollatzResearch.WordTrace tailWord_1677936 prefixEnd_1677936 287195891827550767127773 := by
  unfold tailWord_1677936
  simp only [CollatzResearch.WordTrace]
  refine ⟨30599676824565957749506831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40799569099421276999342441 30599676824565957749506831)
  ·
    refine ⟨45899515236848936624260247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30599676824565957749506831 45899515236848936624260247)
    ·
      refine ⟨68849272855273404936390371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45899515236848936624260247 68849272855273404936390371)
      ·
        refine ⟨103273909282910107404585557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68849272855273404936390371 103273909282910107404585557)
        ·
          refine ⟨1210241124409102821147487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 103273909282910107404585557 1210241124409102821147487)
          ·
            refine ⟨1815361686613654231721231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210241124409102821147487 1815361686613654231721231)
            ·
              refine ⟨2723042529920481347581847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815361686613654231721231 2723042529920481347581847)
              ·
                refine ⟨4084563794880722021372771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2723042529920481347581847 4084563794880722021372771)
                ·
                  refine ⟨6126845692321083032059157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4084563794880722021372771 6126845692321083032059157)
                  ·
                    refine ⟨287195891827550767127773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6126845692321083032059157 287195891827550767127773)
                    ·
                      rfl

theorem cell23_1677936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 1, 6].length) (baseStart_1677936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677936 prefixEnd_1677936 := by exact prefixLift 1677936
  have htrace : WordTrace (prefixWord ++ tailWord_1677936) baseStart_1677936 baseEnd_1677936 := by
    simpa [prefixWord, tailWord_1677936, baseEnd_1677936] using wordTrace_append hprefix tailTrace_1677936
  have hstable : (prefixWord ++ tailWord_1677936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677936).length < 2 ^ (prefixWord ++ tailWord_1677936).sum := by decide
  have hdescent : baseEnd_1677936 < baseStart_1677936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677959 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 6, 1, 3]
def baseStart_1677959 : Nat := 118140960795 + 1677959 * 2 ^ 59
def prefixEnd_1677959 : Nat := 4983230072969 + 3 ^ 40 * 1677959 * 2
def baseEnd_1677959 : Nat := 861599485537705711395713

theorem tailTrace_1677959 : CollatzResearch.WordTrace tailWord_1677959 prefixEnd_1677959 861599485537705711395713 := by
  unfold tailWord_1677959
  simp only [CollatzResearch.WordTrace]
  refine ⟨61200192528048590427100931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40800128352032393618067287 61200192528048590427100931)
  ·
    refine ⟨91800288792072885640651397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61200192528048590427100931 91800288792072885640651397)
    ·
      refine ⟨17212554148513666057622137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91800288792072885640651397 17212554148513666057622137)
      ·
        refine ⟨12909415611385249543216603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17212554148513666057622137 12909415611385249543216603)
        ·
          refine ⟨19364123417077874314824905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12909415611385249543216603 19364123417077874314824905)
          ·
            refine ⟨14523092562808405736118679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19364123417077874314824905 14523092562808405736118679)
            ·
              refine ⟨21784638844212608604178019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14523092562808405736118679 21784638844212608604178019)
              ·
                refine ⟨32676958266318912906267029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21784638844212608604178019 32676958266318912906267029)
                ·
                  refine ⟨1531732418733699042481267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32676958266318912906267029 1531732418733699042481267)
                  ·
                    refine ⟨2297598628100548563721901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1531732418733699042481267 2297598628100548563721901)
                    ·
                      refine ⟨861599485537705711395713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2297598628100548563721901 861599485537705711395713)
                      ·
                        rfl

theorem cell23_1677959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_1677959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677959 prefixEnd_1677959 := by exact prefixLift 1677959
  have htrace : WordTrace (prefixWord ++ tailWord_1677959) baseStart_1677959 baseEnd_1677959 := by
    simpa [prefixWord, tailWord_1677959, baseEnd_1677959] using wordTrace_append hprefix tailTrace_1677959
  have hstable : (prefixWord ++ tailWord_1677959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677959).length < 2 ^ (prefixWord ++ tailWord_1677959).sum := by decide
  have hdescent : baseEnd_1677959 < baseStart_1677959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677976 : List Nat := [2, 1, 2, 4, 1, 1, 2, 4, 2, 1, 3]
def baseStart_1677976 : Nat := 118140960795 + 1677976 * 2 ^ 59
def prefixEnd_1677976 : Nat := 4983230072969 + 3 ^ 40 * 1677976 * 2
def baseEnd_1677976 : Nat := 861608214708832144883135

theorem tailTrace_1677976 : CollatzResearch.WordTrace tailWord_1677976 prefixEnd_1677976 861608214708832144883135 := by
  unfold tailWord_1677976
  simp only [CollatzResearch.WordTrace]
  refine ⟨30600406284493501165234891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40800541712658001553646521 30600406284493501165234891)
  ·
    refine ⟨45900609426740251747852337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30600406284493501165234891 45900609426740251747852337)
    ·
      refine ⟨34425457070055188810889253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45900609426740251747852337 34425457070055188810889253)
      ·
        refine ⟨6454773200635347902041735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34425457070055188810889253 6454773200635347902041735)
        ·
          refine ⟨9682159800953021853062603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6454773200635347902041735 9682159800953021853062603)
          ·
            refine ⟨14523239701429532779593905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9682159800953021853062603 14523239701429532779593905)
            ·
              refine ⟨10892429776072149584695429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14523239701429532779593905 10892429776072149584695429)
              ·
                refine ⟨2042330583013528047130393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10892429776072149584695429 2042330583013528047130393)
                ·
                  refine ⟨1531747937260146035347795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2042330583013528047130393 1531747937260146035347795)
                  ·
                    refine ⟨2297621905890219053021693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1531747937260146035347795 2297621905890219053021693)
                    ·
                      refine ⟨861608214708832144883135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2297621905890219053021693 861608214708832144883135)
                      ·
                        rfl

theorem cell23_1677976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_1677976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1677976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1677976 prefixEnd_1677976 := by exact prefixLift 1677976
  have htrace : WordTrace (prefixWord ++ tailWord_1677976) baseStart_1677976 baseEnd_1677976 := by
    simpa [prefixWord, tailWord_1677976, baseEnd_1677976] using wordTrace_append hprefix tailTrace_1677976
  have hstable : (prefixWord ++ tailWord_1677976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677976).length < 2 ^ (prefixWord ++ tailWord_1677976).sum := by decide
  have hdescent : baseEnd_1677976 < baseStart_1677976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678003 : List Nat := [1, 1, 1, 2, 3, 6, 1, 2, 1, 3, 2]
def baseStart_1678003 : Nat := 118140960795 + 1678003 * 2 ^ 59
def prefixEnd_1678003 : Nat := 4983230072969 + 3 ^ 40 * 1678003 * 2
def baseEnd_1678003 : Nat := 861622078686503539245511

theorem tailTrace_1678003 : CollatzResearch.WordTrace tailWord_1678003 prefixEnd_1678003 861622078686503539245511 := by
  unfold tailWord_1678003
  simp only [CollatzResearch.WordTrace]
  refine ⟨61201797339889185941702663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40801198226592790627801775 61201797339889185941702663)
  ·
    refine ⟨91802696009833778912553995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61201797339889185941702663 91802696009833778912553995)
    ·
      refine ⟨137704044014750668368830993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91802696009833778912553995 137704044014750668368830993)
      ·
        refine ⟨103278033011063001276623245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137704044014750668368830993 103278033011063001276623245)
        ·
          refine ⟨38729262379148625478733717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103278033011063001276623245 38729262379148625478733717)
          ·
            refine ⟨1815434174022591819315643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38729262379148625478733717 1815434174022591819315643)
            ·
              refine ⟨2723151261033887728973465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815434174022591819315643 2723151261033887728973465)
              ·
                refine ⟨2042363445775415796730099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2723151261033887728973465 2042363445775415796730099)
                ·
                  refine ⟨3063545168663123695095149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042363445775415796730099 3063545168663123695095149)
                  ·
                    refine ⟨1148829438248671385660681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3063545168663123695095149 1148829438248671385660681)
                    ·
                      refine ⟨861622078686503539245511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1148829438248671385660681 861622078686503539245511)
                      ·
                        rfl

theorem cell23_1678003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 3, 2].length) (baseStart_1678003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678003 prefixEnd_1678003 := by exact prefixLift 1678003
  have htrace : WordTrace (prefixWord ++ tailWord_1678003) baseStart_1678003 baseEnd_1678003 := by
    simpa [prefixWord, tailWord_1678003, baseEnd_1678003] using wordTrace_append hprefix tailTrace_1678003
  have hstable : (prefixWord ++ tailWord_1678003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678003).length < 2 ^ (prefixWord ++ tailWord_1678003).sum := by decide
  have hdescent : baseEnd_1678003 < baseStart_1678003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678016 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 1, 4, 2]
def baseStart_1678016 : Nat := 118140960795 + 1678016 * 2 ^ 59
def prefixEnd_1678016 : Nat := 4983230072969 + 3 ^ 40 * 1678016 * 2
def baseEnd_1678016 : Nat := 861628753935011988382951

theorem tailTrace_1678016 : CollatzResearch.WordTrace tailWord_1678016 prefixEnd_1678016 861628753935011988382951 := by
  unfold tailWord_1678016
  simp only [CollatzResearch.WordTrace]
  refine ⟨30601135744421044580962951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40801514325894726107950601 30601135744421044580962951)
  ·
    refine ⟨45901703616631566871444427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30601135744421044580962951 45901703616631566871444427)
    ·
      refine ⟨68852555424947350307166641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45901703616631566871444427 68852555424947350307166641)
      ·
        refine ⟨51639416568710512730374981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68852555424947350307166641 51639416568710512730374981)
        ·
          refine ⟨9682390606633221136945309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51639416568710512730374981 9682390606633221136945309)
          ·
            refine ⟨3630896477487457926354491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9682390606633221136945309 3630896477487457926354491)
            ·
              refine ⟨5446344716231186889531737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3630896477487457926354491 5446344716231186889531737)
              ·
                refine ⟨4084758537173390167148803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5446344716231186889531737 4084758537173390167148803)
                ·
                  refine ⟨6127137805760085250723205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4084758537173390167148803 6127137805760085250723205)
                  ·
                    refine ⟨1148838338580015984510601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6127137805760085250723205 1148838338580015984510601)
                    ·
                      refine ⟨861628753935011988382951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1148838338580015984510601 861628753935011988382951)
                      ·
                        rfl

theorem cell23_1678016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 1, 4, 2].length) (baseStart_1678016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678016 prefixEnd_1678016 := by exact prefixLift 1678016
  have htrace : WordTrace (prefixWord ++ tailWord_1678016) baseStart_1678016 baseEnd_1678016 := by
    simpa [prefixWord, tailWord_1678016, baseEnd_1678016] using wordTrace_append hprefix tailTrace_1678016
  have hstable : (prefixWord ++ tailWord_1678016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678016).length < 2 ^ (prefixWord ++ tailWord_1678016).sum := by decide
  have hdescent : baseEnd_1678016 < baseStart_1678016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678020 : List Nat := [2, 3, 3, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_1678020 : Nat := 118140960795 + 1678020 * 2 ^ 59
def prefixEnd_1678020 : Nat := 4983230072969 + 3 ^ 40 * 1678020 * 2
def baseEnd_1678020 : Nat := 861630807857629972732933

theorem tailTrace_1678020 : CollatzResearch.WordTrace tailWord_1678020 prefixEnd_1678020 861630807857629972732933 := by
  unfold tailWord_1678020
  simp only [CollatzResearch.WordTrace]
  refine ⟨30601208690413798922535757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40801611587218398563381009 30601208690413798922535757)
  ·
    refine ⟨11475453258905174595950909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30601208690413798922535757 11475453258905174595950909)
    ·
      refine ⟨4303294972089440473481591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11475453258905174595950909 4303294972089440473481591)
      ·
        refine ⟨6454942458134160710222387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4303294972089440473481591 6454942458134160710222387)
        ·
          refine ⟨9682413687201241065333581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6454942458134160710222387 9682413687201241065333581)
          ·
            refine ⟨3630905132700465399500093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9682413687201241065333581 3630905132700465399500093)
            ·
              refine ⟨1361589424762674524812535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3630905132700465399500093 1361589424762674524812535)
              ·
                refine ⟨2042384137144011787218803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361589424762674524812535 2042384137144011787218803)
                ·
                  refine ⟨3063576205716017680828205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042384137144011787218803 3063576205716017680828205)
                  ·
                    refine ⟨1148841077143506630310577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3063576205716017680828205 1148841077143506630310577)
                    ·
                      refine ⟨861630807857629972732933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1148841077143506630310577 861630807857629972732933)
                      ·
                        rfl

theorem cell23_1678020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_1678020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678020 prefixEnd_1678020 := by exact prefixLift 1678020
  have htrace : WordTrace (prefixWord ++ tailWord_1678020) baseStart_1678020 baseEnd_1678020 := by
    simpa [prefixWord, tailWord_1678020, baseEnd_1678020] using wordTrace_append hprefix tailTrace_1678020
  have hstable : (prefixWord ++ tailWord_1678020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678020).length < 2 ^ (prefixWord ++ tailWord_1678020).sum := by decide
  have hdescent : baseEnd_1678020 < baseStart_1678020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678033 : List Nat := [1, 2, 2, 1, 2, 3, 4, 2, 2, 2, 2]
def baseStart_1678033 : Nat := 118140960795 + 1678033 * 2 ^ 59
def prefixEnd_1678033 : Nat := 4983230072969 + 3 ^ 40 * 1678033 * 2
def baseEnd_1678033 : Nat := 861637483106138421870373

theorem tailTrace_1678033 : CollatzResearch.WordTrace tailWord_1678033 prefixEnd_1678033 861637483106138421870373 := by
  unfold tailWord_1678033
  simp only [CollatzResearch.WordTrace]
  refine ⟨61202891529780501065294753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40801927686520334043529835 61202891529780501065294753)
  ·
    refine ⟨45902168647335375798971065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61202891529780501065294753 45902168647335375798971065)
    ·
      refine ⟨34426626485501531849228299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45902168647335375798971065 34426626485501531849228299)
      ·
        refine ⟨51639939728252297773842449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34426626485501531849228299 51639939728252297773842449)
        ·
          refine ⟨38729954796189223330381837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51639939728252297773842449 38729954796189223330381837)
          ·
            refine ⟨14523733048570958748893189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38729954796189223330381837 14523733048570958748893189)
            ·
              refine ⟨2723199946607054765417473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14523733048570958748893189 2723199946607054765417473)
              ·
                refine ⟨2042399959955291074063105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2723199946607054765417473 2042399959955291074063105)
                ·
                  refine ⟨1531799969966468305547329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2042399959955291074063105 1531799969966468305547329)
                  ·
                    refine ⟨1148849977474851229160497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1531799969966468305547329 1148849977474851229160497)
                    ·
                      refine ⟨861637483106138421870373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1148849977474851229160497 861637483106138421870373)
                      ·
                        rfl

theorem cell23_1678033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 2, 2].length) (baseStart_1678033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678033 prefixEnd_1678033 := by exact prefixLift 1678033
  have htrace : WordTrace (prefixWord ++ tailWord_1678033) baseStart_1678033 baseEnd_1678033 := by
    simpa [prefixWord, tailWord_1678033, baseEnd_1678033] using wordTrace_append hprefix tailTrace_1678033
  have hstable : (prefixWord ++ tailWord_1678033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678033).length < 2 ^ (prefixWord ++ tailWord_1678033).sum := by decide
  have hdescent : baseEnd_1678033 < baseStart_1678033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678049 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 1, 5, 3]
def baseStart_1678049 : Nat := 118140960795 + 1678049 * 2 ^ 59
def prefixEnd_1678049 : Nat := 4983230072969 + 3 ^ 40 * 1678049 * 2
def baseEnd_1678049 : Nat := 861645698796610359270299

theorem tailTrace_1678049 : CollatzResearch.WordTrace tailWord_1678049 prefixEnd_1678049 861645698796610359270299 := by
  unfold tailWord_1678049
  simp only [CollatzResearch.WordTrace]
  refine ⟨61203475097722535797877201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40802316731815023865251467 61203475097722535797877201)
  ·
    refine ⟨45902606323291901848407901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61203475097722535797877201 45902606323291901848407901)
    ·
      refine ⟨17213477371234463193152963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45902606323291901848407901 17213477371234463193152963)
      ·
        refine ⟨25820216056851694789729445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17213477371234463193152963 25820216056851694789729445)
        ·
          refine ⟨4841290510659692773074271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25820216056851694789729445 4841290510659692773074271)
          ·
            refine ⟨7261935765989539159611407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4841290510659692773074271 7261935765989539159611407)
            ·
              refine ⟨10892903648984308739417111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7261935765989539159611407 10892903648984308739417111)
              ·
                refine ⟨16339355473476463109125667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10892903648984308739417111 16339355473476463109125667)
                ·
                  refine ⟨24509033210214694663688501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16339355473476463109125667 24509033210214694663688501)
                  ·
                    refine ⟨2297721863457627624720797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24509033210214694663688501 2297721863457627624720797)
                    ·
                      refine ⟨861645698796610359270299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2297721863457627624720797 861645698796610359270299)
                      ·
                        rfl

theorem cell23_1678049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_1678049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678049 prefixEnd_1678049 := by exact prefixLift 1678049
  have htrace : WordTrace (prefixWord ++ tailWord_1678049) baseStart_1678049 baseEnd_1678049 := by
    simpa [prefixWord, tailWord_1678049, baseEnd_1678049] using wordTrace_append hprefix tailTrace_1678049
  have hstable : (prefixWord ++ tailWord_1678049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678049).length < 2 ^ (prefixWord ++ tailWord_1678049).sum := by decide
  have hdescent : baseEnd_1678049 < baseStart_1678049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678059 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 4, 5, 2]
def baseStart_1678059 : Nat := 118140960795 + 1678059 * 2 ^ 59
def prefixEnd_1678059 : Nat := 4983230072969 + 3 ^ 40 * 1678059 * 2
def baseEnd_1678059 : Nat := 861650833603155320145253

theorem tailTrace_1678059 : CollatzResearch.WordTrace tailWord_1678059 prefixEnd_1678059 861650833603155320145253 := by
  unfold tailWord_1678059
  simp only [CollatzResearch.WordTrace]
  refine ⟨61203839827686307505741231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40802559885124205003827487 61203839827686307505741231)
  ·
    refine ⟨91805759741529461258611847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61203839827686307505741231 91805759741529461258611847)
    ·
      refine ⟨137708639612294191887917771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91805759741529461258611847 137708639612294191887917771)
      ·
        refine ⟨206562959418441287831876657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137708639612294191887917771 206562959418441287831876657)
        ·
          refine ⟨154922219563830965873907493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206562959418441287831876657 154922219563830965873907493)
          ·
            refine ⟨29047916168218306101357655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154922219563830965873907493 29047916168218306101357655)
            ·
              refine ⟨43571874252327459152036483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29047916168218306101357655 43571874252327459152036483)
              ·
                refine ⟨65357811378491188728054725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43571874252327459152036483 65357811378491188728054725)
                ·
                  refine ⟨12254589633467097886510261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65357811378491188728054725 12254589633467097886510261)
                  ·
                    refine ⟨1148867778137540426860337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12254589633467097886510261 1148867778137540426860337)
                    ·
                      refine ⟨861650833603155320145253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1148867778137540426860337 861650833603155320145253)
                      ·
                        rfl

theorem cell23_1678059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 5, 2].length) (baseStart_1678059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678059 prefixEnd_1678059 := by exact prefixLift 1678059
  have htrace : WordTrace (prefixWord ++ tailWord_1678059) baseStart_1678059 baseEnd_1678059 := by
    simpa [prefixWord, tailWord_1678059, baseEnd_1678059] using wordTrace_append hprefix tailTrace_1678059
  have hstable : (prefixWord ++ tailWord_1678059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678059).length < 2 ^ (prefixWord ++ tailWord_1678059).sum := by decide
  have hdescent : baseEnd_1678059 < baseStart_1678059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678089 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 2, 1, 4]
def baseStart_1678089 : Nat := 118140960795 + 1678089 * 2 ^ 59
def prefixEnd_1678089 : Nat := 4983230072969 + 3 ^ 40 * 1678089 * 2
def baseEnd_1678089 : Nat := 861666238022790202770115

theorem tailTrace_1678089 : CollatzResearch.WordTrace tailWord_1678089 prefixEnd_1678089 861666238022790202770115 := by
  unfold tailWord_1678089
  simp only [CollatzResearch.WordTrace]
  refine ⟨61204934017577622629333321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40803289345051748419555547 61204934017577622629333321)
  ·
    refine ⟨45903700513183216971999991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61204934017577622629333321 45903700513183216971999991)
    ·
      refine ⟨68855550769774825457999987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45903700513183216971999991 68855550769774825457999987)
      ·
        refine ⟨103283326154662238186999981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68855550769774825457999987 103283326154662238186999981)
        ·
          refine ⟨38731247307998339320124993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103283326154662238186999981 38731247307998339320124993)
          ·
            refine ⟨29048435480998754490093745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38731247307998339320124993 29048435480998754490093745)
            ·
              refine ⟨21786326610749065867570309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29048435480998754490093745 21786326610749065867570309)
              ·
                refine ⟨4084936239515449850169433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21786326610749065867570309 4084936239515449850169433)
                ·
                  refine ⟨3063702179636587387627075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4084936239515449850169433 3063702179636587387627075)
                  ·
                    refine ⟨4595553269454881081440613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3063702179636587387627075 4595553269454881081440613)
                    ·
                      refine ⟨861666238022790202770115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4595553269454881081440613 861666238022790202770115)
                      ·
                        rfl

theorem cell23_1678089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 1, 4].length) (baseStart_1678089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678089 prefixEnd_1678089 := by exact prefixLift 1678089
  have htrace : WordTrace (prefixWord ++ tailWord_1678089) baseStart_1678089 baseEnd_1678089 := by
    simpa [prefixWord, tailWord_1678089, baseEnd_1678089] using wordTrace_append hprefix tailTrace_1678089
  have hstable : (prefixWord ++ tailWord_1678089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678089).length < 2 ^ (prefixWord ++ tailWord_1678089).sum := by decide
  have hdescent : baseEnd_1678089 < baseStart_1678089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678106 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2]
def baseStart_1678106 : Nat := 118140960795 + 1678106 * 2 ^ 59
def prefixEnd_1678106 : Nat := 4983230072969 + 3 ^ 40 * 1678106 * 2
def baseEnd_1678106 : Nat := 861674967193916636257537

theorem tailTrace_1678106 : CollatzResearch.WordTrace tailWord_1678106 prefixEnd_1678106 861674967193916636257537 := by
  unfold tailWord_1678106
  simp only [CollatzResearch.WordTrace]
  refine ⟨15301388514629008633175543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40803702705677356355134781 15301388514629008633175543)
  ·
    refine ⟨22952082771943512949763315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15301388514629008633175543 22952082771943512949763315)
    ·
      refine ⟨34428124157915269424644973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22952082771943512949763315 34428124157915269424644973)
      ·
        refine ⟨12910546559218226034241865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34428124157915269424644973 12910546559218226034241865)
        ·
          refine ⟨9682909919413669525681399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12910546559218226034241865 9682909919413669525681399)
          ·
            refine ⟨14524364879120504288522099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9682909919413669525681399 14524364879120504288522099)
            ·
              refine ⟨21786547318680756432783149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14524364879120504288522099 21786547318680756432783149)
              ·
                refine ⟨8169955244505283662293681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21786547318680756432783149 8169955244505283662293681)
                ·
                  refine ⟨6127466433378962746720261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8169955244505283662293681 6127466433378962746720261)
                  ·
                    refine ⟨1148899956258555515010049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6127466433378962746720261 1148899956258555515010049)
                    ·
                      refine ⟨861674967193916636257537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1148899956258555515010049 861674967193916636257537)
                      ·
                        rfl

theorem cell23_1678106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_1678106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678106 prefixEnd_1678106 := by exact prefixLift 1678106
  have htrace : WordTrace (prefixWord ++ tailWord_1678106) baseStart_1678106 baseEnd_1678106 := by
    simpa [prefixWord, tailWord_1678106, baseEnd_1678106] using wordTrace_append hprefix tailTrace_1678106
  have hstable : (prefixWord ++ tailWord_1678106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678106).length < 2 ^ (prefixWord ++ tailWord_1678106).sum := by decide
  have hdescent : baseEnd_1678106 < baseStart_1678106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678183 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 2, 3, 2]
def baseStart_1678183 : Nat := 118140960795 + 1678183 * 2 ^ 59
def prefixEnd_1678183 : Nat := 4983230072969 + 3 ^ 40 * 1678183 * 2
def baseEnd_1678183 : Nat := 861714505204312834994683

theorem tailTrace_1678183 : CollatzResearch.WordTrace tailWord_1678183 prefixEnd_1678183 861714505204312834994683 := by
  unfold tailWord_1678183
  simp only [CollatzResearch.WordTrace]
  refine ⟨61208362479237076683255203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40805574986158051122170135 61208362479237076683255203)
  ·
    refine ⟨91812543718855615024882805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61208362479237076683255203 91812543718855615024882805)
    ·
      refine ⟨8607425973642713908582763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91812543718855615024882805 8607425973642713908582763)
      ·
        refine ⟨12911138960464070862874145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8607425973642713908582763 12911138960464070862874145)
        ·
          refine ⟨9683354220348053147155609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12911138960464070862874145 9683354220348053147155609)
          ·
            refine ⟨7262515665261039860366707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9683354220348053147155609 7262515665261039860366707)
            ·
              refine ⟨10893773497891559790550061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7262515665261039860366707 10893773497891559790550061)
              ·
                refine ⟨4085165061709334921456273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10893773497891559790550061 4085165061709334921456273)
                ·
                  refine ⟨3063873796282001191092205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4085165061709334921456273 3063873796282001191092205)
                  ·
                    refine ⟨1148952673605750446659577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3063873796282001191092205 1148952673605750446659577)
                    ·
                      refine ⟨861714505204312834994683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1148952673605750446659577 861714505204312834994683)
                      ·
                        rfl

theorem cell23_1678183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_1678183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678183 prefixEnd_1678183 := by exact prefixLift 1678183
  have htrace : WordTrace (prefixWord ++ tailWord_1678183) baseStart_1678183 baseEnd_1678183 := by
    simpa [prefixWord, tailWord_1678183, baseEnd_1678183] using wordTrace_append hprefix tailTrace_1678183
  have hstable : (prefixWord ++ tailWord_1678183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678183).length < 2 ^ (prefixWord ++ tailWord_1678183).sum := by decide
  have hdescent : baseEnd_1678183 < baseStart_1678183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678193 : List Nat := [1, 2, 2, 2, 1, 5, 3, 1, 1, 5]
def baseStart_1678193 : Nat := 118140960795 + 1678193 * 2 ^ 59
def prefixEnd_1678193 : Nat := 4983230072969 + 3 ^ 40 * 1678193 * 2
def baseEnd_1678193 : Nat := 287239880003619265289879

theorem tailTrace_1678193 : CollatzResearch.WordTrace tailWord_1678193 prefixEnd_1678193 287239880003619265289879 := by
  unfold tailWord_1678193
  simp only [CollatzResearch.WordTrace]
  refine ⟨61208727209200848391119233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40805818139467232260746155 61208727209200848391119233)
  ·
    refine ⟨45906545406900636293339425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61208727209200848391119233 45906545406900636293339425)
    ·
      refine ⟨34429909055175477220004569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45906545406900636293339425 34429909055175477220004569)
      ·
        refine ⟨25822431791381607915003427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34429909055175477220004569 25822431791381607915003427)
        ·
          refine ⟨38733647687072411872505141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25822431791381607915003427 38733647687072411872505141)
          ·
            refine ⟨3631279470663038613047357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38733647687072411872505141 3631279470663038613047357)
            ·
              refine ⟨1361729801498639479892759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3631279470663038613047357 1361729801498639479892759)
              ·
                refine ⟨2042594702247959219839139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361729801498639479892759 2042594702247959219839139)
                ·
                  refine ⟨3063892053371938829758709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042594702247959219839139 3063892053371938829758709)
                  ·
                    refine ⟨287239880003619265289879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3063892053371938829758709 287239880003619265289879)
                    ·
                      rfl

theorem cell23_1678193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_1678193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678193 prefixEnd_1678193 := by exact prefixLift 1678193
  have htrace : WordTrace (prefixWord ++ tailWord_1678193) baseStart_1678193 baseEnd_1678193 := by
    simpa [prefixWord, tailWord_1678193, baseEnd_1678193] using wordTrace_append hprefix tailTrace_1678193
  have hstable : (prefixWord ++ tailWord_1678193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678193).length < 2 ^ (prefixWord ++ tailWord_1678193).sum := by decide
  have hdescent : baseEnd_1678193 < baseStart_1678193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678219 : List Nat := [1, 1, 1, 1, 4, 2, 5, 8]
def baseStart_1678219 : Nat := 118140960795 + 1678219 * 2 ^ 59
def prefixEnd_1678219 : Nat := 4983230072969 + 3 ^ 40 * 1678219 * 2
def baseEnd_1678219 : Nat := 31916036685476840523871

theorem tailTrace_1678219 : CollatzResearch.WordTrace tailWord_1678219 prefixEnd_1678219 31916036685476840523871 := by
  unfold tailWord_1678219
  simp only [CollatzResearch.WordTrace]
  refine ⟨61209675507106654831565711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40806450338071103221043807 61209675507106654831565711)
  ·
    refine ⟨91814513260659982247348567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61209675507106654831565711 91814513260659982247348567)
    ·
      refine ⟨137721769890989973371022851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91814513260659982247348567 137721769890989973371022851)
      ·
        refine ⟨206582654836484960056534277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137721769890989973371022851 206582654836484960056534277)
        ·
          refine ⟨38734247781840930010600177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206582654836484960056534277 38734247781840930010600177)
          ·
            refine ⟨29050685836380697507950133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38734247781840930010600177 29050685836380697507950133)
            ·
              refine ⟨2723501797160690391370325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29050685836380697507950133 2723501797160690391370325)
              ·
                refine ⟨31916036685476840523871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2723501797160690391370325 31916036685476840523871)
                ·
                  rfl

theorem cell23_1678219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 8].length) (baseStart_1678219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678219 prefixEnd_1678219 := by exact prefixLift 1678219
  have htrace : WordTrace (prefixWord ++ tailWord_1678219) baseStart_1678219 baseEnd_1678219 := by
    simpa [prefixWord, tailWord_1678219, baseEnd_1678219] using wordTrace_append hprefix tailTrace_1678219
  have hstable : (prefixWord ++ tailWord_1678219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678219).length < 2 ^ (prefixWord ++ tailWord_1678219).sum := by decide
  have hdescent : baseEnd_1678219 < baseStart_1678219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678247 : List Nat := [1, 1, 6, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_1678247 : Nat := 118140960795 + 1678247 * 2 ^ 59
def prefixEnd_1678247 : Nat := 4983230072969 + 3 ^ 40 * 1678247 * 2
def baseEnd_1678247 : Nat := 861747367966200584594389

theorem tailTrace_1678247 : CollatzResearch.WordTrace tailWord_1678247 prefixEnd_1678247 861747367966200584594389 := by
  unfold tailWord_1678247
  simp only [CollatzResearch.WordTrace]
  refine ⟨61210696751005215613584995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40807131167336810409056663 61210696751005215613584995)
  ·
    refine ⟨91816045126507823420377493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61210696751005215613584995 91816045126507823420377493)
    ·
      refine ⟨4303877115305054222830195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91816045126507823420377493 4303877115305054222830195)
      ·
        refine ⟨6455815672957581334245293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4303877115305054222830195 6455815672957581334245293)
        ·
          refine ⟨2420930877359093000341985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6455815672957581334245293 2420930877359093000341985)
          ·
            refine ⟨1815698158019319750256489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2420930877359093000341985 1815698158019319750256489)
            ·
              refine ⟨1361773618514489812692367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1815698158019319750256489 1361773618514489812692367)
              ·
                refine ⟨2042660427771734719038551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361773618514489812692367 2042660427771734719038551)
                ·
                  refine ⟨3063990641657602078557827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042660427771734719038551 3063990641657602078557827)
                  ·
                    refine ⟨4595985962486403117836741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3063990641657602078557827 4595985962486403117836741)
                    ·
                      refine ⟨861747367966200584594389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4595985962486403117836741 861747367966200584594389)
                      ·
                        rfl

theorem cell23_1678247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_1678247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678247 prefixEnd_1678247 := by exact prefixLift 1678247
  have htrace : WordTrace (prefixWord ++ tailWord_1678247) baseStart_1678247 baseEnd_1678247 := by
    simpa [prefixWord, tailWord_1678247, baseEnd_1678247] using wordTrace_append hprefix tailTrace_1678247
  have hstable : (prefixWord ++ tailWord_1678247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678247).length < 2 ^ (prefixWord ++ tailWord_1678247).sum := by decide
  have hdescent : baseEnd_1678247 < baseStart_1678247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678253 : List Nat := [1, 5, 2, 3, 1, 1, 10]
def baseStart_1678253 : Nat := 118140960795 + 1678253 * 2 ^ 59
def prefixEnd_1678253 : Nat := 4983230072969 + 3 ^ 40 * 1678253 * 2
def baseEnd_1678253 : Nat := 10638894430248488408881

theorem tailTrace_1678253 : CollatzResearch.WordTrace tailWord_1678253 prefixEnd_1678253 10638894430248488408881 := by
  unfold tailWord_1678253
  simp only [CollatzResearch.WordTrace]
  refine ⟨61210915588983478638303413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40807277059322319092202275 61210915588983478638303413)
  ·
    refine ⟨5738523336467201122340945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61210915588983478638303413 5738523336467201122340945)
    ·
      refine ⟨4303892502350400841755709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5738523336467201122340945 4303892502350400841755709)
      ·
        refine ⟨1613959688381400315658391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4303892502350400841755709 1613959688381400315658391)
        ·
          refine ⟨2420939532572100473487587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1613959688381400315658391 2420939532572100473487587)
          ·
            refine ⟨3631409298858150710231381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420939532572100473487587 3631409298858150710231381)
            ·
              refine ⟨10638894430248488408881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3631409298858150710231381 10638894430248488408881)
              ·
                rfl

theorem cell23_1678253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 10].length) (baseStart_1678253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678253 prefixEnd_1678253 := by exact prefixLift 1678253
  have htrace : WordTrace (prefixWord ++ tailWord_1678253) baseStart_1678253 baseEnd_1678253 := by
    simpa [prefixWord, tailWord_1678253, baseEnd_1678253] using wordTrace_append hprefix tailTrace_1678253
  have hstable : (prefixWord ++ tailWord_1678253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678253).length < 2 ^ (prefixWord ++ tailWord_1678253).sum := by decide
  have hdescent : baseEnd_1678253 < baseStart_1678253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678257 : List Nat := [1, 2, 2, 4, 4, 1, 1, 2, 2, 4]
def baseStart_1678257 : Nat := 118140960795 + 1678257 * 2 ^ 59
def prefixEnd_1678257 : Nat := 4983230072969 + 3 ^ 40 * 1678257 * 2
def baseEnd_1678257 : Nat := 287250834257581848489781

theorem tailTrace_1678257 : CollatzResearch.WordTrace tailWord_1678257 prefixEnd_1678257 287250834257581848489781 := by
  unfold tailWord_1678257
  simp only [CollatzResearch.WordTrace]
  refine ⟨61211061480968987321449025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40807374320645991547632683 61211061480968987321449025)
  ·
    refine ⟨45908296110726740491086769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61211061480968987321449025 45908296110726740491086769)
    ·
      refine ⟨34431222083045055368315077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45908296110726740491086769 34431222083045055368315077)
      ·
        refine ⟨6455854140570947881559077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34431222083045055368315077 6455854140570947881559077)
        ·
          refine ⟨1210472651357052727792327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6455854140570947881559077 1210472651357052727792327)
          ·
            refine ⟨1815708977035579091688491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210472651357052727792327 1815708977035579091688491)
            ·
              refine ⟨2723563465553368637532737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815708977035579091688491 2723563465553368637532737)
              ·
                refine ⟨2042672599165026478149553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2723563465553368637532737 2042672599165026478149553)
                ·
                  refine ⟨1532004449373769858612165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2042672599165026478149553 1532004449373769858612165)
                  ·
                    refine ⟨287250834257581848489781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1532004449373769858612165 287250834257581848489781)
                    ·
                      rfl

theorem cell23_1678257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_1678257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678257 prefixEnd_1678257 := by exact prefixLift 1678257
  have htrace : WordTrace (prefixWord ++ tailWord_1678257) baseStart_1678257 baseEnd_1678257 := by
    simpa [prefixWord, tailWord_1678257, baseEnd_1678257] using wordTrace_append hprefix tailTrace_1678257
  have hstable : (prefixWord ++ tailWord_1678257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678257).length < 2 ^ (prefixWord ++ tailWord_1678257).sum := by decide
  have hdescent : baseEnd_1678257 < baseStart_1678257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678259 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 5]
def baseStart_1678259 : Nat := 118140960795 + 1678259 * 2 ^ 59
def prefixEnd_1678259 : Nat := 4983230072969 + 3 ^ 40 * 1678259 * 2
def baseEnd_1678259 : Nat := 861753529734054537644333

theorem tailTrace_1678259 : CollatzResearch.WordTrace tailWord_1678259 prefixEnd_1678259 861753529734054537644333 := by
  unfold tailWord_1678259
  simp only [CollatzResearch.WordTrace]
  refine ⟨61211134426961741663021831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40807422951307827775347887 61211134426961741663021831)
  ·
    refine ⟨91816701640442612494532747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61211134426961741663021831 91816701640442612494532747)
    ·
      refine ⟨137725052460663918741799121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91816701640442612494532747 137725052460663918741799121)
      ·
        refine ⟨103293789345497939056349341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137725052460663918741799121 103293789345497939056349341)
        ·
          refine ⟨38735171004561727146131003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103293789345497939056349341 38735171004561727146131003)
          ·
            refine ⟨58102756506842590719196505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38735171004561727146131003 58102756506842590719196505)
            ·
              refine ⟨43577067380131943039397379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58102756506842590719196505 43577067380131943039397379)
              ·
                refine ⟨65365601070197914559096069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43577067380131943039397379 65365601070197914559096069)
                ·
                  refine ⟨12256050200662108979830513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65365601070197914559096069 12256050200662108979830513)
                  ·
                    refine ⟨9192037650496581734872885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12256050200662108979830513 9192037650496581734872885)
                    ·
                      refine ⟨861753529734054537644333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9192037650496581734872885 861753529734054537644333)
                      ·
                        rfl

theorem cell23_1678259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_1678259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678259 prefixEnd_1678259 := by exact prefixLift 1678259
  have htrace : WordTrace (prefixWord ++ tailWord_1678259) baseStart_1678259 baseEnd_1678259 := by
    simpa [prefixWord, tailWord_1678259, baseEnd_1678259] using wordTrace_append hprefix tailTrace_1678259
  have hstable : (prefixWord ++ tailWord_1678259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678259).length < 2 ^ (prefixWord ++ tailWord_1678259).sum := by decide
  have hdescent : baseEnd_1678259 < baseStart_1678259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678280 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 1, 3, 3]
def baseStart_1678280 : Nat := 118140960795 + 1678280 * 2 ^ 59
def prefixEnd_1678280 : Nat := 4983230072969 + 3 ^ 40 * 1678280 * 2
def baseEnd_1678280 : Nat := 861764312827798955481737

theorem tailTrace_1678280 : CollatzResearch.WordTrace tailWord_1678280 prefixEnd_1678280 861764312827798955481737 := by
  unfold tailWord_1678280
  simp only [CollatzResearch.WordTrace]
  refine ⟨30605950179942831124768147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40807933573257108166357529 30605950179942831124768147)
  ·
    refine ⟨45908925269914246687152221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30605950179942831124768147 45908925269914246687152221)
    ·
      refine ⟨17215846976217842507682083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45908925269914246687152221 17215846976217842507682083)
      ·
        refine ⟨25823770464326763761523125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17215846976217842507682083 25823770464326763761523125)
        ·
          refine ⟨2420978481030634102642793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25823770464326763761523125 2420978481030634102642793)
          ·
            refine ⟨1815733860772975576982095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2420978481030634102642793 1815733860772975576982095)
            ·
              refine ⟨2723600791159463365473143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815733860772975576982095 2723600791159463365473143)
              ·
                refine ⟨4085401186739195048209715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2723600791159463365473143 4085401186739195048209715)
                ·
                  refine ⟨6128101780108792572314573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4085401186739195048209715 6128101780108792572314573)
                  ·
                    refine ⟨2298038167540797214617965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6128101780108792572314573 2298038167540797214617965)
                    ·
                      refine ⟨861764312827798955481737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2298038167540797214617965 861764312827798955481737)
                      ·
                        rfl

theorem cell23_1678280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_1678280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678280 prefixEnd_1678280 := by exact prefixLift 1678280
  have htrace : WordTrace (prefixWord ++ tailWord_1678280) baseStart_1678280 baseEnd_1678280 := by
    simpa [prefixWord, tailWord_1678280, baseEnd_1678280] using wordTrace_append hprefix tailTrace_1678280
  have hstable : (prefixWord ++ tailWord_1678280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678280).length < 2 ^ (prefixWord ++ tailWord_1678280).sum := by decide
  have hdescent : baseEnd_1678280 < baseStart_1678280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678320 : List Nat := [2, 1, 1, 1, 3, 2, 1, 6, 2, 2, 2]
def baseStart_1678320 : Nat := 118140960795 + 1678320 * 2 ^ 59
def prefixEnd_1678320 : Nat := 4983230072969 + 3 ^ 40 * 1678320 * 2
def baseEnd_1678320 : Nat := 861784852053978798981553

theorem tailTrace_1678320 : CollatzResearch.WordTrace tailWord_1678320 prefixEnd_1678320 861784852053978798981553 := by
  unfold tailWord_1678320
  simp only [CollatzResearch.WordTrace]
  refine ⟨30606679639870374540496207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40808906186493832720661609 30606679639870374540496207)
  ·
    refine ⟨45910019459805561810744311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30606679639870374540496207 45910019459805561810744311)
    ·
      refine ⟨68865029189708342716116467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45910019459805561810744311 68865029189708342716116467)
      ·
        refine ⟨103297543784562514074174701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68865029189708342716116467 103297543784562514074174701)
        ·
          refine ⟨38736578919210942777815513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103297543784562514074174701 38736578919210942777815513)
          ·
            refine ⟨29052434189408207083361635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38736578919210942777815513 29052434189408207083361635)
            ·
              refine ⟨43578651284112310625042453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29052434189408207083361635 43578651284112310625042453)
              ·
                refine ⟨2042749278942764560548865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43578651284112310625042453 2042749278942764560548865)
                ·
                  refine ⟨1532061959207073420411649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2042749278942764560548865 1532061959207073420411649)
                  ·
                    refine ⟨1149046469405305065308737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1532061959207073420411649 1149046469405305065308737)
                    ·
                      refine ⟨861784852053978798981553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1149046469405305065308737 861784852053978798981553)
                      ·
                        rfl

theorem cell23_1678320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 2, 2, 2].length) (baseStart_1678320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678320 prefixEnd_1678320 := by exact prefixLift 1678320
  have htrace : WordTrace (prefixWord ++ tailWord_1678320) baseStart_1678320 baseEnd_1678320 := by
    simpa [prefixWord, tailWord_1678320, baseEnd_1678320] using wordTrace_append hprefix tailTrace_1678320
  have hstable : (prefixWord ++ tailWord_1678320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678320).length < 2 ^ (prefixWord ++ tailWord_1678320).sum := by decide
  have hdescent : baseEnd_1678320 < baseStart_1678320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678336 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 3]
def baseStart_1678336 : Nat := 118140960795 + 1678336 * 2 ^ 59
def prefixEnd_1678336 : Nat := 4983230072969 + 3 ^ 40 * 1678336 * 2
def baseEnd_1678336 : Nat := 861793067744450736381479

theorem tailTrace_1678336 : CollatzResearch.WordTrace tailWord_1678336 prefixEnd_1678336 861793067744450736381479 := by
  unfold tailWord_1678336
  simp only [CollatzResearch.WordTrace]
  refine ⟨30606971423841391906787431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40809295231788522542383241 30606971423841391906787431)
  ·
    refine ⟨45910457135762087860181147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30606971423841391906787431 45910457135762087860181147)
    ·
      refine ⟨68865685703643131790271721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45910457135762087860181147 68865685703643131790271721)
      ·
        refine ⟨51649264277732348842703791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68865685703643131790271721 51649264277732348842703791)
        ·
          refine ⟨77473896416598523264055687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51649264277732348842703791 77473896416598523264055687)
          ·
            refine ⟨116210844624897784896083531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77473896416598523264055687 116210844624897784896083531)
            ·
              refine ⟨174316266937346677344125297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116210844624897784896083531 174316266937346677344125297)
              ·
                refine ⟨130737200203010008008093973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174316266937346677344125297 130737200203010008008093973)
                ·
                  refine ⟨6128306259516094125379405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130737200203010008008093973 6128306259516094125379405)
                  ·
                    refine ⟨2298114847318535297017277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6128306259516094125379405 2298114847318535297017277)
                    ·
                      refine ⟨861793067744450736381479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2298114847318535297017277 861793067744450736381479)
                      ·
                        rfl

theorem cell23_1678336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_1678336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678336 prefixEnd_1678336 := by exact prefixLift 1678336
  have htrace : WordTrace (prefixWord ++ tailWord_1678336) baseStart_1678336 baseEnd_1678336 := by
    simpa [prefixWord, tailWord_1678336, baseEnd_1678336] using wordTrace_append hprefix tailTrace_1678336
  have hstable : (prefixWord ++ tailWord_1678336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678336).length < 2 ^ (prefixWord ++ tailWord_1678336).sum := by decide
  have hdescent : baseEnd_1678336 < baseStart_1678336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678337 : List Nat := [1, 2, 4, 1, 2, 3, 1, 3, 2, 2, 2]
def baseStart_1678337 : Nat := 118140960795 + 1678337 * 2 ^ 59
def prefixEnd_1678337 : Nat := 4983230072969 + 3 ^ 40 * 1678337 * 2
def baseEnd_1678337 : Nat := 861793581225105232468975

theorem tailTrace_1678337 : CollatzResearch.WordTrace tailWord_1678337 prefixEnd_1678337 861793581225105232468975 := by
  unfold tailWord_1678337
  simp only [CollatzResearch.WordTrace]
  refine ⟨61213979320679160984361265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40809319547119440656240843 61213979320679160984361265)
  ·
    refine ⟨45910484490509370738270949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61213979320679160984361265 45910484490509370738270949)
    ·
      refine ⟨8608215841970507013425803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45910484490509370738270949 8608215841970507013425803)
      ·
        refine ⟨12912323762955760520138705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8608215841970507013425803 12912323762955760520138705)
        ·
          refine ⟨9684242822216820390104029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12912323762955760520138705 9684242822216820390104029)
          ·
            refine ⟨3631591058331307646289011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9684242822216820390104029 3631591058331307646289011)
            ·
              refine ⟨5447386587496961469433517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3631591058331307646289011 5447386587496961469433517)
              ·
                refine ⟨2042769970311360551037569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5447386587496961469433517 2042769970311360551037569)
                ·
                  refine ⟨1532077477733520413278177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2042769970311360551037569 1532077477733520413278177)
                  ·
                    refine ⟨1149058108300140309958633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1532077477733520413278177 1149058108300140309958633)
                    ·
                      refine ⟨861793581225105232468975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1149058108300140309958633 861793581225105232468975)
                      ·
                        rfl

theorem cell23_1678337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_1678337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678337 prefixEnd_1678337 := by exact prefixLift 1678337
  have htrace : WordTrace (prefixWord ++ tailWord_1678337) baseStart_1678337 baseEnd_1678337 := by
    simpa [prefixWord, tailWord_1678337, baseEnd_1678337] using wordTrace_append hprefix tailTrace_1678337
  have hstable : (prefixWord ++ tailWord_1678337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678337).length < 2 ^ (prefixWord ++ tailWord_1678337).sum := by decide
  have hdescent : baseEnd_1678337 < baseStart_1678337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678403 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 3, 4]
def baseStart_1678403 : Nat := 118140960795 + 1678403 * 2 ^ 59
def prefixEnd_1678403 : Nat := 4983230072969 + 3 ^ 40 * 1678403 * 2
def baseEnd_1678403 : Nat := 287275823649433991414557

theorem tailTrace_1678403 : CollatzResearch.WordTrace tailWord_1678403 prefixEnd_1678403 287275823649433991414557 := by
  unfold tailWord_1678403
  simp only [CollatzResearch.WordTrace]
  refine ⟨61216386538440054256263863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40810924358960036170842575 61216386538440054256263863)
  ·
    refine ⟨91824579807660081384395795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61216386538440054256263863 91824579807660081384395795)
    ·
      refine ⟨137736869711490122076593693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91824579807660081384395795 137736869711490122076593693)
      ·
        refine ⟨51651326141808795778722635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137736869711490122076593693 51651326141808795778722635)
        ·
          refine ⟨77476989212713193668083953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51651326141808795778722635 77476989212713193668083953)
          ·
            refine ⟨58107741909534895251062965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77476989212713193668083953 58107741909534895251062965)
            ·
              refine ⟨5447600804018896429787153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58107741909534895251062965 5447600804018896429787153)
              ·
                refine ⟨4085700603014172322340365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5447600804018896429787153 4085700603014172322340365)
                ·
                  refine ⟨1532137726130314620877637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4085700603014172322340365 1532137726130314620877637)
                  ·
                    refine ⟨287275823649433991414557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1532137726130314620877637 287275823649433991414557)
                    ·
                      rfl

theorem cell23_1678403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 4].length) (baseStart_1678403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678403 prefixEnd_1678403 := by exact prefixLift 1678403
  have htrace : WordTrace (prefixWord ++ tailWord_1678403) baseStart_1678403 baseEnd_1678403 := by
    simpa [prefixWord, tailWord_1678403, baseEnd_1678403] using wordTrace_append hprefix tailTrace_1678403
  have hstable : (prefixWord ++ tailWord_1678403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678403).length < 2 ^ (prefixWord ++ tailWord_1678403).sum := by decide
  have hdescent : baseEnd_1678403 < baseStart_1678403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678433 : List Nat := [1, 2, 3, 1, 1, 2, 5, 2, 6]
def baseStart_1678433 : Nat := 118140960795 + 1678433 * 2 ^ 59
def prefixEnd_1678433 : Nat := 4983230072969 + 3 ^ 40 * 1678433 * 2
def baseEnd_1678433 : Nat := 95760319485326317429837

theorem tailTrace_1678433 : CollatzResearch.WordTrace tailWord_1678433 prefixEnd_1678433 95760319485326317429837 := by
  unfold tailWord_1678433
  simp only [CollatzResearch.WordTrace]
  refine ⟨61217480728331369379855953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40811653818887579586570635 61217480728331369379855953)
  ·
    refine ⟨45913110546248527034891965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61217480728331369379855953 45913110546248527034891965)
    ·
      refine ⟨17217416454843197638084487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45913110546248527034891965 17217416454843197638084487)
      ·
        refine ⟨25826124682264796457126731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17217416454843197638084487 25826124682264796457126731)
        ·
          refine ⟨38739187023397194685690097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25826124682264796457126731 38739187023397194685690097)
          ·
            refine ⟨29054390267547896014267573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38739187023397194685690097 29054390267547896014267573)
            ·
              refine ⟨2723849087582615251337585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29054390267547896014267573 2723849087582615251337585)
              ·
                refine ⟨2042886815686961438503189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2723849087582615251337585 2042886815686961438503189)
                ·
                  refine ⟨95760319485326317429837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2042886815686961438503189 95760319485326317429837)
                  ·
                    rfl

theorem cell23_1678433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 6].length) (baseStart_1678433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678433 prefixEnd_1678433 := by exact prefixLift 1678433
  have htrace : WordTrace (prefixWord ++ tailWord_1678433) baseStart_1678433 baseEnd_1678433 := by
    simpa [prefixWord, tailWord_1678433, baseEnd_1678433] using wordTrace_append hprefix tailTrace_1678433
  have hstable : (prefixWord ++ tailWord_1678433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678433).length < 2 ^ (prefixWord ++ tailWord_1678433).sum := by decide
  have hdescent : baseEnd_1678433 < baseStart_1678433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678450 : List Nat := [3, 2, 1, 2, 2, 1, 5, 1, 6]
def baseStart_1678450 : Nat := 118140960795 + 1678450 * 2 ^ 59
def prefixEnd_1678450 : Nat := 4983230072969 + 3 ^ 40 * 1678450 * 2
def baseEnd_1678450 : Nat := 95761289393229254483995

theorem tailTrace_1678450 : CollatzResearch.WordTrace tailWord_1678450 prefixEnd_1678450 95761289393229254483995 := by
  unfold tailWord_1678450
  simp only [CollatzResearch.WordTrace]
  refine ⟨15304525192317445320806201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40812067179513187522149869 15304525192317445320806201)
  ·
    refine ⟨11478393894238083990604651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15304525192317445320806201 11478393894238083990604651)
    ·
      refine ⟨17217590841357125985906977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11478393894238083990604651 17217590841357125985906977)
      ·
        refine ⟨12913193131017844489430233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17217590841357125985906977 12913193131017844489430233)
        ·
          refine ⟨9684894848263383367072675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12913193131017844489430233 9684894848263383367072675)
          ·
            refine ⟨14527342272395075050609013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9684894848263383367072675 14527342272395075050609013)
            ·
              refine ⟨1361938338037038285994595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14527342272395075050609013 1361938338037038285994595)
              ·
                refine ⟨2042907507055557428991893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361938338037038285994595 2042907507055557428991893)
                ·
                  refine ⟨95761289393229254483995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2042907507055557428991893 95761289393229254483995)
                  ·
                    rfl

theorem cell23_1678450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_1678450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678450 prefixEnd_1678450 := by exact prefixLift 1678450
  have htrace : WordTrace (prefixWord ++ tailWord_1678450) baseStart_1678450 baseEnd_1678450 := by
    simpa [prefixWord, tailWord_1678450, baseEnd_1678450] using wordTrace_append hprefix tailTrace_1678450
  have hstable : (prefixWord ++ tailWord_1678450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678450).length < 2 ^ (prefixWord ++ tailWord_1678450).sum := by decide
  have hdescent : baseEnd_1678450 < baseStart_1678450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678456 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 2, 1, 7]
def baseStart_1678456 : Nat := 118140960795 + 1678456 * 2 ^ 59
def prefixEnd_1678456 : Nat := 4983230072969 + 3 ^ 40 * 1678456 * 2
def baseEnd_1678456 : Nat := 861854685422990266880927

theorem tailTrace_1678456 : CollatzResearch.WordTrace tailWord_1678456 prefixEnd_1678456 861854685422990266880927 := by
  unfold tailWord_1678456
  simp only [CollatzResearch.WordTrace]
  refine ⟨30609159803624022153971611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40812213071498696205295481 30609159803624022153971611)
  ·
    refine ⟨45913739705436033230957417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30609159803624022153971611 45913739705436033230957417)
    ·
      refine ⟨34435304779077024923218063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45913739705436033230957417 34435304779077024923218063)
      ·
        refine ⟨51652957168615537384827095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34435304779077024923218063 51652957168615537384827095)
        ·
          refine ⟨77479435752923306077240643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51652957168615537384827095 77479435752923306077240643)
          ·
            refine ⟨116219153629384959115860965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77479435752923306077240643 116219153629384959115860965)
            ·
              refine ⟨21791091305509679834223931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116219153629384959115860965 21791091305509679834223931)
              ·
                refine ⟨32686636958264519751335897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21791091305509679834223931 32686636958264519751335897)
                ·
                  refine ⟨24514977718698389813501923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32686636958264519751335897 24514977718698389813501923)
                  ·
                    refine ⟨36772466578047584720252885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24514977718698389813501923 36772466578047584720252885)
                    ·
                      refine ⟨861854685422990266880927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36772466578047584720252885 861854685422990266880927)
                      ·
                        rfl

theorem cell23_1678456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_1678456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678456 prefixEnd_1678456 := by exact prefixLift 1678456
  have htrace : WordTrace (prefixWord ++ tailWord_1678456) baseStart_1678456 baseEnd_1678456 := by
    simpa [prefixWord, tailWord_1678456, baseEnd_1678456] using wordTrace_append hprefix tailTrace_1678456
  have hstable : (prefixWord ++ tailWord_1678456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678456).length < 2 ^ (prefixWord ++ tailWord_1678456).sum := by decide
  have hdescent : baseEnd_1678456 < baseStart_1678456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678460 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 3, 1, 3]
def baseStart_1678460 : Nat := 118140960795 + 1678460 * 2 ^ 59
def prefixEnd_1678460 : Nat := 4983230072969 + 3 ^ 40 * 1678460 * 2
def baseEnd_1678460 : Nat := 861856739345608251230909

theorem tailTrace_1678460 : CollatzResearch.WordTrace tailWord_1678460 prefixEnd_1678460 861856739345608251230909 := by
  unfold tailWord_1678460
  simp only [CollatzResearch.WordTrace]
  refine ⟨30609232749616776495544417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40812310332822368660725889 30609232749616776495544417)
  ·
    refine ⟨22956924562212582371658313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30609232749616776495544417 22956924562212582371658313)
    ·
      refine ⟨17217693421659436778743735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22956924562212582371658313 17217693421659436778743735)
      ·
        refine ⟨25826540132489155168115603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17217693421659436778743735 25826540132489155168115603)
        ·
          refine ⟨38739810198733732752173405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25826540132489155168115603 38739810198733732752173405)
          ·
            refine ⟨14527428824525149782065027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38739810198733732752173405 14527428824525149782065027)
            ·
              refine ⟨21791143236787724673097541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14527428824525149782065027 21791143236787724673097541)
              ·
                refine ⟨4085839356897698376205789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21791143236787724673097541 4085839356897698376205789)
                ·
                  refine ⟨1532189758836636891077171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4085839356897698376205789 1532189758836636891077171)
                  ·
                    refine ⟨2298284638254955336615757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1532189758836636891077171 2298284638254955336615757)
                    ·
                      refine ⟨861856739345608251230909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2298284638254955336615757 861856739345608251230909)
                      ·
                        rfl

theorem cell23_1678460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_1678460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678460 prefixEnd_1678460 := by exact prefixLift 1678460
  have htrace : WordTrace (prefixWord ++ tailWord_1678460) baseStart_1678460 baseEnd_1678460 := by
    simpa [prefixWord, tailWord_1678460, baseEnd_1678460] using wordTrace_append hprefix tailTrace_1678460
  have hstable : (prefixWord ++ tailWord_1678460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678460).length < 2 ^ (prefixWord ++ tailWord_1678460).sum := by decide
  have hdescent : baseEnd_1678460 < baseStart_1678460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678487 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 2, 3, 2]
def baseStart_1678487 : Nat := 118140960795 + 1678487 * 2 ^ 59
def prefixEnd_1678487 : Nat := 4983230072969 + 3 ^ 40 * 1678487 * 2
def baseEnd_1678487 : Nat := 861870603323279645593285

theorem tailTrace_1678487 : CollatzResearch.WordTrace tailWord_1678487 prefixEnd_1678487 861870603323279645593285 := by
  unfold tailWord_1678487
  simp only [CollatzResearch.WordTrace]
  refine ⟨61219450270135736602321715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40812966846757157734881143 61219450270135736602321715)
  ·
    refine ⟨91829175405203604903482573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61219450270135736602321715 91829175405203604903482573)
    ·
      refine ⟨34435940776951351838805965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91829175405203604903482573 34435940776951351838805965)
      ·
        refine ⟨12913477791356756939552237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34435940776951351838805965 12913477791356756939552237)
        ·
          refine ⟨4842554171758783852332089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12913477791356756939552237 4842554171758783852332089)
          ·
            refine ⟨3631915628819087889249067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4842554171758783852332089 3631915628819087889249067)
            ·
              refine ⟨5447873443228631833873601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3631915628819087889249067 5447873443228631833873601)
              ·
                refine ⟨4085905082421473875405201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5447873443228631833873601 4085905082421473875405201)
                ·
                  refine ⟨3064428811816105406553901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4085905082421473875405201 3064428811816105406553901)
                  ·
                    refine ⟨1149160804431039527457713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3064428811816105406553901 1149160804431039527457713)
                    ·
                      refine ⟨861870603323279645593285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1149160804431039527457713 861870603323279645593285)
                      ·
                        rfl

theorem cell23_1678487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_1678487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678487 prefixEnd_1678487 := by exact prefixLift 1678487
  have htrace : WordTrace (prefixWord ++ tailWord_1678487) baseStart_1678487 baseEnd_1678487 := by
    simpa [prefixWord, tailWord_1678487, baseEnd_1678487] using wordTrace_append hprefix tailTrace_1678487
  have hstable : (prefixWord ++ tailWord_1678487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678487).length < 2 ^ (prefixWord ++ tailWord_1678487).sum := by decide
  have hdescent : baseEnd_1678487 < baseStart_1678487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678494 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_1678494 : Nat := 118140960795 + 1678494 * 2 ^ 59
def prefixEnd_1678494 : Nat := 4983230072969 + 3 ^ 40 * 1678494 * 2
def baseEnd_1678494 : Nat := 861874197687861118205753

theorem tailTrace_1678494 : CollatzResearch.WordTrace tailWord_1678494 prefixEnd_1678494 861874197687861118205753 := by
  unfold tailWord_1678494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7652463197638797099728317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40813137054073584531884357 7652463197638797099728317)
  ·
    refine ⟨2869673699114548912398119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7652463197638797099728317 2869673699114548912398119)
    ·
      refine ⟨4304510548671823368597179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2869673699114548912398119 4304510548671823368597179)
      ·
        refine ⟨6456765823007735052895769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4304510548671823368597179 6456765823007735052895769)
        ·
          refine ⟨4842574367255801289671827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6456765823007735052895769 4842574367255801289671827)
          ·
            refine ⟨7263861550883701934507741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4842574367255801289671827 7263861550883701934507741)
            ·
              refine ⟨2723948081581388225440403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7263861550883701934507741 2723948081581388225440403)
              ·
                refine ⟨4085922122372082338160605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2723948081581388225440403 4085922122372082338160605)
                ·
                  refine ⟨1532220795889530876810227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4085922122372082338160605 1532220795889530876810227)
                  ·
                    refine ⟨2298331193834296315215341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1532220795889530876810227 2298331193834296315215341)
                    ·
                      refine ⟨861874197687861118205753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2298331193834296315215341 861874197687861118205753)
                      ·
                        rfl

theorem cell23_1678494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_1678494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678494 prefixEnd_1678494 := by exact prefixLift 1678494
  have htrace : WordTrace (prefixWord ++ tailWord_1678494) baseStart_1678494 baseEnd_1678494 := by
    simpa [prefixWord, tailWord_1678494, baseEnd_1678494] using wordTrace_append hprefix tailTrace_1678494
  have hstable : (prefixWord ++ tailWord_1678494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678494).length < 2 ^ (prefixWord ++ tailWord_1678494).sum := by decide
  have hdescent : baseEnd_1678494 < baseStart_1678494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678520 : List Nat := [2, 1, 2, 1, 2, 1, 2, 6, 1, 2, 3]
def baseStart_1678520 : Nat := 118140960795 + 1678520 * 2 ^ 59
def prefixEnd_1678520 : Nat := 4983230072969 + 3 ^ 40 * 1678520 * 2
def baseEnd_1678520 : Nat := 861887548184878016480633

theorem tailTrace_1678520 : CollatzResearch.WordTrace tailWord_1678520 prefixEnd_1678520 861887548184878016480633 := by
  unfold tailWord_1678520
  simp only [CollatzResearch.WordTrace]
  refine ⟨30610326939508091619136507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40813769252677455492182009 30610326939508091619136507)
  ·
    refine ⟨45915490409262137428704761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30610326939508091619136507 45915490409262137428704761)
    ·
      refine ⟨34436617806946603071528571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45915490409262137428704761 34436617806946603071528571)
      ·
        refine ⟨51654926710419904607292857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34436617806946603071528571 51654926710419904607292857)
        ·
          refine ⟨38741195032814928455469643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51654926710419904607292857 38741195032814928455469643)
          ·
            refine ⟨58111792549222392683204465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38741195032814928455469643 58111792549222392683204465)
            ·
              refine ⟨43583844411916794512403349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58111792549222392683204465 43583844411916794512403349)
              ·
                refine ⟨2042992706808599742768907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43583844411916794512403349 2042992706808599742768907)
                ·
                  refine ⟨3064489060212899614153361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042992706808599742768907 3064489060212899614153361)
                  ·
                    refine ⟨2298366795159674710615021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3064489060212899614153361 2298366795159674710615021)
                    ·
                      refine ⟨861887548184878016480633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2298366795159674710615021 861887548184878016480633)
                      ·
                        rfl

theorem cell23_1678520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_1678520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678520 prefixEnd_1678520 := by exact prefixLift 1678520
  have htrace : WordTrace (prefixWord ++ tailWord_1678520) baseStart_1678520 baseEnd_1678520 := by
    simpa [prefixWord, tailWord_1678520, baseEnd_1678520] using wordTrace_append hprefix tailTrace_1678520
  have hstable : (prefixWord ++ tailWord_1678520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678520).length < 2 ^ (prefixWord ++ tailWord_1678520).sum := by decide
  have hdescent : baseEnd_1678520 < baseStart_1678520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678551 : List Nat := [1, 1, 3, 2, 1, 2, 6, 2, 1, 2, 2]
def baseStart_1678551 : Nat := 118140960795 + 1678551 * 2 ^ 59
def prefixEnd_1678551 : Nat := 4983230072969 + 3 ^ 40 * 1678551 * 2
def baseEnd_1678551 : Nat := 861903466085167395192991

theorem tailTrace_1678551 : CollatzResearch.WordTrace tailWord_1678551 prefixEnd_1678551 861903466085167395192991 := by
  unfold tailWord_1678551
  simp only [CollatzResearch.WordTrace]
  refine ⟨61221784541903875532651507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40814523027935917021767671 61221784541903875532651507)
  ·
    refine ⟨91832676812855813298977261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61221784541903875532651507 91832676812855813298977261)
    ·
      refine ⟨34437253804820929987116473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91832676812855813298977261 34437253804820929987116473)
      ·
        refine ⟨25827940353615697490337355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34437253804820929987116473 25827940353615697490337355)
        ·
          refine ⟨38741910530423546235506033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25827940353615697490337355 38741910530423546235506033)
          ·
            refine ⟨29056432897817659676629525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38741910530423546235506033 29056432897817659676629525)
            ·
              refine ⟨1362020292085202797342009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29056432897817659676629525 1362020292085202797342009)
              ·
                refine ⟨1021515219063902098006507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362020292085202797342009 1021515219063902098006507)
                ·
                  refine ⟨1532272828595853147009761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1021515219063902098006507 1532272828595853147009761)
                  ·
                    refine ⟨1149204621446889860257321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1532272828595853147009761 1149204621446889860257321)
                    ·
                      refine ⟨861903466085167395192991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1149204621446889860257321 861903466085167395192991)
                      ·
                        rfl

theorem cell23_1678551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_1678551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678551 prefixEnd_1678551 := by exact prefixLift 1678551
  have htrace : WordTrace (prefixWord ++ tailWord_1678551) baseStart_1678551 baseEnd_1678551 := by
    simpa [prefixWord, tailWord_1678551, baseEnd_1678551] using wordTrace_append hprefix tailTrace_1678551
  have hstable : (prefixWord ++ tailWord_1678551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678551).length < 2 ^ (prefixWord ++ tailWord_1678551).sum := by decide
  have hdescent : baseEnd_1678551 < baseStart_1678551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678557 : List Nat := [1, 4, 3, 2, 2, 2, 1, 8]
def baseStart_1678557 : Nat := 118140960795 + 1678557 * 2 ^ 59
def prefixEnd_1678557 : Nat := 4983230072969 + 3 ^ 40 * 1678557 * 2
def baseEnd_1678557 : Nat := 31922464702559050804369

theorem tailTrace_1678557 : CollatzResearch.WordTrace tailWord_1678557 prefixEnd_1678557 31922464702559050804369 := by
  unfold tailWord_1678557
  simp only [CollatzResearch.WordTrace]
  refine ⟨61222003379882138557369925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40814668919921425704913283 61222003379882138557369925)
  ·
    refine ⟨11479125633727900979506861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61222003379882138557369925 11479125633727900979506861)
    ·
      refine ⟨4304672112647962867315073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11479125633727900979506861 4304672112647962867315073)
      ·
        refine ⟨3228504084485972150486305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4304672112647962867315073 3228504084485972150486305)
        ·
          refine ⟨2421378063364479112864729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3228504084485972150486305 2421378063364479112864729)
          ·
            refine ⟨1816033547523359334648547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2421378063364479112864729 1816033547523359334648547)
            ·
              refine ⟨2724050321285039001972821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1816033547523359334648547 2724050321285039001972821)
              ·
                refine ⟨31922464702559050804369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2724050321285039001972821 31922464702559050804369)
                ·
                  rfl

theorem cell23_1678557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 8].length) (baseStart_1678557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678557 prefixEnd_1678557 := by exact prefixLift 1678557
  have htrace : WordTrace (prefixWord ++ tailWord_1678557) baseStart_1678557 baseEnd_1678557 := by
    simpa [prefixWord, tailWord_1678557, baseEnd_1678557] using wordTrace_append hprefix tailTrace_1678557
  have hstable : (prefixWord ++ tailWord_1678557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678557).length < 2 ^ (prefixWord ++ tailWord_1678557).sum := by decide
  have hdescent : baseEnd_1678557 < baseStart_1678557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678577 : List Nat := [1, 2, 2, 2, 2, 1, 1, 6, 1, 3, 2]
def baseStart_1678577 : Nat := 118140960795 + 1678577 * 2 ^ 59
def prefixEnd_1678577 : Nat := 4983230072969 + 3 ^ 40 * 1678577 * 2
def baseEnd_1678577 : Nat := 861916816582184293467871

theorem tailTrace_1678577 : CollatzResearch.WordTrace tailWord_1678577 prefixEnd_1678577 861916816582184293467871 := by
  unfold tailWord_1678577
  simp only [CollatzResearch.WordTrace]
  refine ⟨61222732839809681973097985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40815155226539787982065323 61222732839809681973097985)
  ·
    refine ⟨45917049629857261479823489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61222732839809681973097985 45917049629857261479823489)
    ·
      refine ⟨34437787222392946109867617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45917049629857261479823489 34437787222392946109867617)
      ·
        refine ⟨25828340416794709582400713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34437787222392946109867617 25828340416794709582400713)
        ·
          refine ⟨19371255312596032186800535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25828340416794709582400713 19371255312596032186800535)
          ·
            refine ⟨29056882968894048280200803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19371255312596032186800535 29056882968894048280200803)
            ·
              refine ⟨43585324453341072420301205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29056882968894048280200803 43585324453341072420301205)
              ·
                refine ⟨2043062083750362769701619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43585324453341072420301205 2043062083750362769701619)
                ·
                  refine ⟨3064593125625544154552429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043062083750362769701619 3064593125625544154552429)
                  ·
                    refine ⟨1149222422109579057957161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3064593125625544154552429 1149222422109579057957161)
                    ·
                      refine ⟨861916816582184293467871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1149222422109579057957161 861916816582184293467871)
                      ·
                        rfl

theorem cell23_1678577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_1678577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678577 prefixEnd_1678577 := by exact prefixLift 1678577
  have htrace : WordTrace (prefixWord ++ tailWord_1678577) baseStart_1678577 baseEnd_1678577 := by
    simpa [prefixWord, tailWord_1678577, baseEnd_1678577] using wordTrace_append hprefix tailTrace_1678577
  have hstable : (prefixWord ++ tailWord_1678577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678577).length < 2 ^ (prefixWord ++ tailWord_1678577).sum := by decide
  have hdescent : baseEnd_1678577 < baseStart_1678577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678620 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_1678620 : Nat := 118140960795 + 1678620 * 2 ^ 59
def prefixEnd_1678620 : Nat := 4983230072969 + 3 ^ 40 * 1678620 * 2
def baseEnd_1678620 : Nat := 861938896250327625230173

theorem tailTrace_1678620 : CollatzResearch.WordTrace tailWord_1678620 prefixEnd_1678620 861938896250327625230173 := by
  unfold tailWord_1678620
  simp only [CollatzResearch.WordTrace]
  refine ⟨30612150589326950158456657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40816200785769266877942209 30612150589326950158456657)
  ·
    refine ⟨22959112941995212618842493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30612150589326950158456657 22959112941995212618842493)
    ·
      refine ⟨8609667353248204732065935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22959112941995212618842493 8609667353248204732065935)
      ·
        refine ⟨12914501029872307098098903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8609667353248204732065935 12914501029872307098098903)
        ·
          refine ⟨19371751544808460647148355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12914501029872307098098903 19371751544808460647148355)
          ·
            refine ⟨29057627317212690970722533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19371751544808460647148355 29057627317212690970722533)
            ·
              refine ⟨5448305121977379557010475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29057627317212690970722533 5448305121977379557010475)
              ·
                refine ⟨8172457682966069335515713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5448305121977379557010475 8172457682966069335515713)
                ·
                  refine ⟨6129343262224552001636785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8172457682966069335515713 6129343262224552001636785)
                  ·
                    refine ⟨4597007446668414001227589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6129343262224552001636785 4597007446668414001227589)
                    ·
                      refine ⟨861938896250327625230173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4597007446668414001227589 861938896250327625230173)
                      ·
                        rfl

theorem cell23_1678620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_1678620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678620 prefixEnd_1678620 := by exact prefixLift 1678620
  have htrace : WordTrace (prefixWord ++ tailWord_1678620) baseStart_1678620 baseEnd_1678620 := by
    simpa [prefixWord, tailWord_1678620, baseEnd_1678620] using wordTrace_append hprefix tailTrace_1678620
  have hstable : (prefixWord ++ tailWord_1678620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678620).length < 2 ^ (prefixWord ++ tailWord_1678620).sum := by decide
  have hdescent : baseEnd_1678620 < baseStart_1678620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678670 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_1678670 : Nat := 118140960795 + 1678670 * 2 ^ 59
def prefixEnd_1678670 : Nat := 4983230072969 + 3 ^ 40 * 1678670 * 2
def baseEnd_1678670 : Nat := 861964570283052429604943

theorem tailTrace_1678670 : CollatzResearch.WordTrace tailWord_1678670 prefixEnd_1678670 861964570283052429604943 := by
  unfold tailWord_1678670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7653265603559094857029183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40817416552315172570822309 7653265603559094857029183)
  ·
    refine ⟨11479898405338642285543775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7653265603559094857029183 11479898405338642285543775)
    ·
      refine ⟨17219847608007963428315663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11479898405338642285543775 17219847608007963428315663)
      ·
        refine ⟨25829771412011945142473495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17219847608007963428315663 25829771412011945142473495)
        ·
          refine ⟨38744657118017917713710243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25829771412011945142473495 38744657118017917713710243)
          ·
            refine ⟨58116985677026876570565365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38744657118017917713710243 58116985677026876570565365)
            ·
              refine ⟨5448467407221269678490503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58116985677026876570565365 5448467407221269678490503)
              ·
                refine ⟨8172701110831904517735755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5448467407221269678490503 8172701110831904517735755)
                ·
                  refine ⟨12259051666247856776603633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8172701110831904517735755 12259051666247856776603633)
                  ·
                    refine ⟨9194288749685892582452725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12259051666247856776603633 9194288749685892582452725)
                    ·
                      refine ⟨861964570283052429604943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9194288749685892582452725 861964570283052429604943)
                      ·
                        rfl

theorem cell23_1678670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_1678670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678670 prefixEnd_1678670 := by exact prefixLift 1678670
  have htrace : WordTrace (prefixWord ++ tailWord_1678670) baseStart_1678670 baseEnd_1678670 := by
    simpa [prefixWord, tailWord_1678670, baseEnd_1678670] using wordTrace_append hprefix tailTrace_1678670
  have hstable : (prefixWord ++ tailWord_1678670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678670).length < 2 ^ (prefixWord ++ tailWord_1678670).sum := by decide
  have hdescent : baseEnd_1678670 < baseStart_1678670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678680 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 4, 1, 4]
def baseStart_1678680 : Nat := 118140960795 + 1678680 * 2 ^ 59
def prefixEnd_1678680 : Nat := 4983230072969 + 3 ^ 40 * 1678680 * 2
def baseEnd_1678680 : Nat := 861969705089597390479897

theorem tailTrace_1678680 : CollatzResearch.WordTrace tailWord_1678680 prefixEnd_1678680 861969705089597390479897 := by
  unfold tailWord_1678680
  simp only [CollatzResearch.WordTrace]
  refine ⟨30613244779218265282048747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40817659705624353709398329 30613244779218265282048747)
  ·
    refine ⟨45919867168827397923073121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30613244779218265282048747 45919867168827397923073121)
    ·
      refine ⟨34439900376620548442304841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45919867168827397923073121 34439900376620548442304841)
      ·
        refine ⟨25829925282465411331728631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34439900376620548442304841 25829925282465411331728631)
        ·
          refine ⟨38744887923698116997592947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25829925282465411331728631 38744887923698116997592947)
          ·
            refine ⟨58117331885547175496389421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38744887923698116997592947 58117331885547175496389421)
            ·
              refine ⟨21793999457080190811146033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58117331885547175496389421 21793999457080190811146033)
              ·
                refine ⟨16345499592810143108359525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21793999457080190811146033 16345499592810143108359525)
                ·
                  refine ⟨3064781173651901832817411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16345499592810143108359525 3064781173651901832817411)
                  ·
                    refine ⟨4597171760477852749226117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3064781173651901832817411 4597171760477852749226117)
                    ·
                      refine ⟨861969705089597390479897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4597171760477852749226117 861969705089597390479897)
                      ·
                        rfl

theorem cell23_1678680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_1678680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678680 prefixEnd_1678680 := by exact prefixLift 1678680
  have htrace : WordTrace (prefixWord ++ tailWord_1678680) baseStart_1678680 baseEnd_1678680 := by
    simpa [prefixWord, tailWord_1678680, baseEnd_1678680] using wordTrace_append hprefix tailTrace_1678680
  have hstable : (prefixWord ++ tailWord_1678680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678680).length < 2 ^ (prefixWord ++ tailWord_1678680).sum := by decide
  have hdescent : baseEnd_1678680 < baseStart_1678680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678717 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 2, 2, 3]
def baseStart_1678717 : Nat := 118140960795 + 1678717 * 2 ^ 59
def prefixEnd_1678717 : Nat := 4983230072969 + 3 ^ 40 * 1678717 * 2
def baseEnd_1678717 : Nat := 861988703873813745717227

theorem tailTrace_1678717 : CollatzResearch.WordTrace tailWord_1678717 prefixEnd_1678717 861988703873813745717227 := by
  unfold tailWord_1678717
  simp only [CollatzResearch.WordTrace]
  refine ⟨61227839059302485883194405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40818559372868323922129603 61227839059302485883194405)
  ·
    refine ⟨11480219823619216103098951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61227839059302485883194405 11480219823619216103098951)
    ·
      refine ⟨17220329735428824154648427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11480219823619216103098951 17220329735428824154648427)
      ·
        refine ⟨25830494603143236231972641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17220329735428824154648427 25830494603143236231972641)
        ·
          refine ⟨19372870952357427173979481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25830494603143236231972641 19372870952357427173979481)
          ·
            refine ⟨14529653214268070380484611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19372870952357427173979481 14529653214268070380484611)
            ·
              refine ⟨21794479821402105570726917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14529653214268070380484611 21794479821402105570726917)
              ·
                refine ⟨4086464966512894794511297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21794479821402105570726917 4086464966512894794511297)
                ·
                  refine ⟨3064848724884671095883473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4086464966512894794511297 3064848724884671095883473)
                  ·
                    refine ⟨2298636543663503321912605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3064848724884671095883473 2298636543663503321912605)
                    ·
                      refine ⟨861988703873813745717227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2298636543663503321912605 861988703873813745717227)
                      ·
                        rfl

theorem cell23_1678717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_1678717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678717 prefixEnd_1678717 := by exact prefixLift 1678717
  have htrace : WordTrace (prefixWord ++ tailWord_1678717) baseStart_1678717 baseEnd_1678717 := by
    simpa [prefixWord, tailWord_1678717, baseEnd_1678717] using wordTrace_append hprefix tailTrace_1678717
  have hstable : (prefixWord ++ tailWord_1678717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678717).length < 2 ^ (prefixWord ++ tailWord_1678717).sum := by decide
  have hdescent : baseEnd_1678717 < baseStart_1678717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678748 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 2, 1, 4]
def baseStart_1678748 : Nat := 118140960795 + 1678748 * 2 ^ 59
def prefixEnd_1678748 : Nat := 4983230072969 + 3 ^ 40 * 1678748 * 2
def baseEnd_1678748 : Nat := 862004621774103124429585

theorem tailTrace_1678748 : CollatzResearch.WordTrace tailWord_1678748 prefixEnd_1678748 862004621774103124429585 := by
  unfold tailWord_1678748
  simp only [CollatzResearch.WordTrace]
  refine ⟨30614484861095089088786449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40819313148126785451715265 30614484861095089088786449)
  ·
    refine ⟨22960863645821316816589837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30614484861095089088786449 22960863645821316816589837)
    ·
      refine ⟨8610323867182993806221189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22960863645821316816589837 8610323867182993806221189)
      ·
        refine ⟨1614435725096811338666473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8610323867182993806221189 1614435725096811338666473)
        ·
          refine ⟨1210826793822608503999855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1614435725096811338666473 1210826793822608503999855)
          ·
            refine ⟨1816240190733912755999783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210826793822608503999855 1816240190733912755999783)
            ·
              refine ⟨2724360286100869133999675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1816240190733912755999783 2724360286100869133999675)
              ·
                refine ⟨4086540429151303700999513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2724360286100869133999675 4086540429151303700999513)
                ·
                  refine ⟨3064905321863477775749635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4086540429151303700999513 3064905321863477775749635)
                  ·
                    refine ⟨4597357982795216663624453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3064905321863477775749635 4597357982795216663624453)
                    ·
                      refine ⟨862004621774103124429585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4597357982795216663624453 862004621774103124429585)
                      ·
                        rfl

theorem cell23_1678748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_1678748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678748 prefixEnd_1678748 := by exact prefixLift 1678748
  have htrace : WordTrace (prefixWord ++ tailWord_1678748) baseStart_1678748 baseEnd_1678748 := by
    simpa [prefixWord, tailWord_1678748, baseEnd_1678748] using wordTrace_append hprefix tailTrace_1678748
  have hstable : (prefixWord ++ tailWord_1678748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678748).length < 2 ^ (prefixWord ++ tailWord_1678748).sum := by decide
  have hdescent : baseEnd_1678748 < baseStart_1678748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678781 : List Nat := [1, 4, 1, 2, 2, 1, 1, 6, 1, 1, 3]
def baseStart_1678781 : Nat := 118140960795 + 1678781 * 2 ^ 59
def prefixEnd_1678781 : Nat := 4983230072969 + 3 ^ 40 * 1678781 * 2
def baseEnd_1678781 : Nat := 862021566635701495316933

theorem tailTrace_1678781 : CollatzResearch.WordTrace tailWord_1678781 prefixEnd_1678781 862021566635701495316933 := by
  unfold tailWord_1678781
  simp only [CollatzResearch.WordTrace]
  refine ⟨61230173331070624813524197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40820115554047083209016131 61230173331070624813524197)
  ·
    refine ⟨11480657499575742152535787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61230173331070624813524197 11480657499575742152535787)
    ·
      refine ⟨17220986249363613228803681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11480657499575742152535787 17220986249363613228803681)
      ·
        refine ⟨12915739687022709921602761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17220986249363613228803681 12915739687022709921602761)
        ·
          refine ⟨9686804765267032441202071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12915739687022709921602761 9686804765267032441202071)
          ·
            refine ⟨14530207147900548661803107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9686804765267032441202071 14530207147900548661803107)
            ·
              refine ⟨21795310721850822992704661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14530207147900548661803107 21795310721850822992704661)
              ·
                refine ⟨1021655190086757327783031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21795310721850822992704661 1021655190086757327783031)
                ·
                  refine ⟨1532482785130135991674547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1021655190086757327783031 1532482785130135991674547)
                  ·
                    refine ⟨2298724177695203987511821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1532482785130135991674547 2298724177695203987511821)
                    ·
                      refine ⟨862021566635701495316933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2298724177695203987511821 862021566635701495316933)
                      ·
                        rfl

theorem cell23_1678781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_1678781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678781 prefixEnd_1678781 := by exact prefixLift 1678781
  have htrace : WordTrace (prefixWord ++ tailWord_1678781) baseStart_1678781 baseEnd_1678781 := by
    simpa [prefixWord, tailWord_1678781, baseEnd_1678781] using wordTrace_append hprefix tailTrace_1678781
  have hstable : (prefixWord ++ tailWord_1678781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678781).length < 2 ^ (prefixWord ++ tailWord_1678781).sum := by decide
  have hdescent : baseEnd_1678781 < baseStart_1678781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678800 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 6]
def baseStart_1678800 : Nat := 118140960795 + 1678800 * 2 ^ 59
def prefixEnd_1678800 : Nat := 4983230072969 + 3 ^ 40 * 1678800 * 2
def baseEnd_1678800 : Nat := 862031322768136920979345

theorem tailTrace_1678800 : CollatzResearch.WordTrace tailWord_1678800 prefixEnd_1678800 862031322768136920979345 := by
  unfold tailWord_1678800
  simp only [CollatzResearch.WordTrace]
  refine ⟨30615433159000895529232927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40820577545334527372310569 30615433159000895529232927)
  ·
    refine ⟨45923149738501343293849391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30615433159000895529232927 45923149738501343293849391)
    ·
      refine ⟨68884724607752014940774087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45923149738501343293849391 68884724607752014940774087)
      ·
        refine ⟨103327086911628022411161131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68884724607752014940774087 103327086911628022411161131)
        ·
          refine ⟨154990630367442033616741697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103327086911628022411161131 154990630367442033616741697)
          ·
            refine ⟨116242972775581525212556273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154990630367442033616741697 116242972775581525212556273)
            ·
              refine ⟨87182229581686143909417205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116242972775581525212556273 87182229581686143909417205)
              ·
                refine ⟨8173334023283075991507863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87182229581686143909417205 8173334023283075991507863)
                ·
                  refine ⟨12260001034924613987261795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8173334023283075991507863 12260001034924613987261795)
                  ·
                    refine ⟨18390001552386920980892693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12260001034924613987261795 18390001552386920980892693)
                    ·
                      refine ⟨862031322768136920979345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18390001552386920980892693 862031322768136920979345)
                      ·
                        rfl

theorem cell23_1678800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_1678800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678800 prefixEnd_1678800 := by exact prefixLift 1678800
  have htrace : WordTrace (prefixWord ++ tailWord_1678800) baseStart_1678800 baseEnd_1678800 := by
    simpa [prefixWord, tailWord_1678800, baseEnd_1678800] using wordTrace_append hprefix tailTrace_1678800
  have hstable : (prefixWord ++ tailWord_1678800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678800).length < 2 ^ (prefixWord ++ tailWord_1678800).sum := by decide
  have hdescent : baseEnd_1678800 < baseStart_1678800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678807 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 3]
def baseStart_1678807 : Nat := 118140960795 + 1678807 * 2 ^ 59
def prefixEnd_1678807 : Nat := 4983230072969 + 3 ^ 40 * 1678807 * 2
def baseEnd_1678807 : Nat := 862034917132718393591813

theorem tailTrace_1678807 : CollatzResearch.WordTrace tailWord_1678807 prefixEnd_1678807 862034917132718393591813 := by
  unfold tailWord_1678807
  simp only [CollatzResearch.WordTrace]
  refine ⟨61231121628976431253970675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40820747752650954169313783 61231121628976431253970675)
  ·
    refine ⟨91846682443464646880956013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61231121628976431253970675 91846682443464646880956013)
    ·
      refine ⟨34442505916299242580358505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91846682443464646880956013 34442505916299242580358505)
      ·
        refine ⟨25831879437224431935268879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34442505916299242580358505 25831879437224431935268879)
        ·
          refine ⟨38747819155836647902903319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25831879437224431935268879 38747819155836647902903319)
          ·
            refine ⟨58121728733754971854354979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38747819155836647902903319 58121728733754971854354979)
            ·
              refine ⟨87182593100632457781532469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58121728733754971854354979 87182593100632457781532469)
              ·
                refine ⟨8173368103184292917018669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87182593100632457781532469 8173368103184292917018669)
                ·
                  refine ⟨3065013038694109843882001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8173368103184292917018669 3065013038694109843882001)
                  ·
                    refine ⟨2298759779020582382911501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3065013038694109843882001 2298759779020582382911501)
                    ·
                      refine ⟨862034917132718393591813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2298759779020582382911501 862034917132718393591813)
                      ·
                        rfl

theorem cell23_1678807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_1678807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678807 prefixEnd_1678807 := by exact prefixLift 1678807
  have htrace : WordTrace (prefixWord ++ tailWord_1678807) baseStart_1678807 baseEnd_1678807 := by
    simpa [prefixWord, tailWord_1678807, baseEnd_1678807] using wordTrace_append hprefix tailTrace_1678807
  have hstable : (prefixWord ++ tailWord_1678807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678807).length < 2 ^ (prefixWord ++ tailWord_1678807).sum := by decide
  have hdescent : baseEnd_1678807 < baseStart_1678807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678824 : List Nat := [2, 1, 4, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_1678824 : Nat := 118140960795 + 1678824 * 2 ^ 59
def prefixEnd_1678824 : Nat := 4983230072969 + 3 ^ 40 * 1678824 * 2
def baseEnd_1678824 : Nat := 862043646303844827079235

theorem tailTrace_1678824 : CollatzResearch.WordTrace tailWord_1678824 prefixEnd_1678824 862043646303844827079235 := by
  unfold tailWord_1678824
  simp only [CollatzResearch.WordTrace]
  refine ⟨30615870834957421578669763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40821161113276562104893017 30615870834957421578669763)
  ·
    refine ⟨45923806252436132368004645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30615870834957421578669763 45923806252436132368004645)
    ·
      refine ⟨8610713672331774819000871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45923806252436132368004645 8610713672331774819000871)
      ·
        refine ⟨12916070508497662228501307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8610713672331774819000871 12916070508497662228501307)
        ·
          refine ⟨19374105762746493342751961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12916070508497662228501307 19374105762746493342751961)
          ·
            refine ⟨14530579322059870007063971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19374105762746493342751961 14530579322059870007063971)
            ·
              refine ⟨21795868983089805010595957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14530579322059870007063971 21795868983089805010595957)
              ·
                refine ⟨2043362717164669219743371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21795868983089805010595957 2043362717164669219743371)
                ·
                  refine ⟨3065044075747003829615057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043362717164669219743371 3065044075747003829615057)
                  ·
                    refine ⟨2298783056810252872211293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3065044075747003829615057 2298783056810252872211293)
                    ·
                      refine ⟨862043646303844827079235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2298783056810252872211293 862043646303844827079235)
                      ·
                        rfl

theorem cell23_1678824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_1678824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678824 prefixEnd_1678824 := by exact prefixLift 1678824
  have htrace : WordTrace (prefixWord ++ tailWord_1678824) baseStart_1678824 baseEnd_1678824 := by
    simpa [prefixWord, tailWord_1678824, baseEnd_1678824] using wordTrace_append hprefix tailTrace_1678824
  have hstable : (prefixWord ++ tailWord_1678824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678824).length < 2 ^ (prefixWord ++ tailWord_1678824).sum := by decide
  have hdescent : baseEnd_1678824 < baseStart_1678824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678838 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2]
def baseStart_1678838 : Nat := 118140960795 + 1678838 * 2 ^ 59
def prefixEnd_1678838 : Nat := 4983230072969 + 3 ^ 40 * 1678838 * 2
def baseEnd_1678838 : Nat := 862050835033007772304171

theorem tailTrace_1678838 : CollatzResearch.WordTrace tailWord_1678838 prefixEnd_1678838 862050835033007772304171 := by
  unfold tailWord_1678838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3827015768241507721771823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40821501527909415698899445 3827015768241507721771823)
  ·
    refine ⟨5740523652362261582657735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3827015768241507721771823 5740523652362261582657735)
    ·
      refine ⟨8610785478543392373986603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5740523652362261582657735 8610785478543392373986603)
      ·
        refine ⟨12916178217815088560979905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8610785478543392373986603 12916178217815088560979905)
        ·
          refine ⟨9687133663361316420734929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12916178217815088560979905 9687133663361316420734929)
          ·
            refine ⟨7265350247520987315551197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9687133663361316420734929 7265350247520987315551197)
            ·
              refine ⟨2724506342820370243331699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7265350247520987315551197 2724506342820370243331699)
              ·
                refine ⟨4086759514230555364997549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2724506342820370243331699 4086759514230555364997549)
                ·
                  refine ⟨1532534817836458261874081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4086759514230555364997549 1532534817836458261874081)
                  ·
                    refine ⟨1149401113377343696405561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1532534817836458261874081 1149401113377343696405561)
                    ·
                      refine ⟨862050835033007772304171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1149401113377343696405561 862050835033007772304171)
                      ·
                        rfl

theorem cell23_1678838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_1678838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678838 prefixEnd_1678838 := by exact prefixLift 1678838
  have htrace : WordTrace (prefixWord ++ tailWord_1678838) baseStart_1678838 baseEnd_1678838 := by
    simpa [prefixWord, tailWord_1678838, baseEnd_1678838] using wordTrace_append hprefix tailTrace_1678838
  have hstable : (prefixWord ++ tailWord_1678838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678838).length < 2 ^ (prefixWord ++ tailWord_1678838).sum := by decide
  have hdescent : baseEnd_1678838 < baseStart_1678838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678878 : List Nat := [4, 3, 3, 1, 2, 10]
def baseStart_1678878 : Nat := 118140960795 + 1678878 * 2 ^ 59
def prefixEnd_1678878 : Nat := 4983230072969 + 3 ^ 40 * 1678878 * 2
def baseEnd_1678878 : Nat := 3547618824111883192609

theorem tailTrace_1678878 : CollatzResearch.WordTrace tailWord_1678878 prefixEnd_1678878 3547618824111883192609 := by
  unfold tailWord_1678878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7654213901464901297475661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40822474141146140253203525 7654213901464901297475661)
  ·
    refine ⟨2870330213049337986553373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7654213901464901297475661 2870330213049337986553373)
    ·
      refine ⟨1076373829893501744957515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2870330213049337986553373 1076373829893501744957515)
      ·
        refine ⟨1614560744840252617436273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076373829893501744957515 1614560744840252617436273)
        ·
          refine ⟨1210920558630189463077205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1614560744840252617436273 1210920558630189463077205)
          ·
            refine ⟨3547618824111883192609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1210920558630189463077205 3547618824111883192609)
            ·
              rfl

theorem cell23_1678878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 10].length) (baseStart_1678878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678878 prefixEnd_1678878 := by exact prefixLift 1678878
  have htrace : WordTrace (prefixWord ++ tailWord_1678878) baseStart_1678878 baseEnd_1678878 := by
    simpa [prefixWord, tailWord_1678878, baseEnd_1678878] using wordTrace_append hprefix tailTrace_1678878
  have hstable : (prefixWord ++ tailWord_1678878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678878).length < 2 ^ (prefixWord ++ tailWord_1678878).sum := by decide
  have hdescent : baseEnd_1678878 < baseStart_1678878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678894 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1678894 : Nat := 118140960795 + 1678894 * 2 ^ 59
def prefixEnd_1678894 : Nat := 4983230072969 + 3 ^ 40 * 1678894 * 2
def baseEnd_1678894 : Nat := 862079589949659553203913

theorem tailTrace_1678894 : CollatzResearch.WordTrace tailWord_1678894 prefixEnd_1678894 862079589949659553203913 := by
  unfold tailWord_1678894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7654286847457655639048467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40822863186440830074925157 7654286847457655639048467)
  ·
    refine ⟨11481430271186483458572701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7654286847457655639048467 11481430271186483458572701)
    ·
      refine ⟨4305536351694931296964763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11481430271186483458572701 4305536351694931296964763)
      ·
        refine ⟨6458304527542396945447145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4305536351694931296964763 6458304527542396945447145)
        ·
          refine ⟨4843728395656797709085359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6458304527542396945447145 4843728395656797709085359)
          ·
            refine ⟨7265592593485196563628039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4843728395656797709085359 7265592593485196563628039)
            ·
              refine ⟨10898388890227794845442059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7265592593485196563628039 10898388890227794845442059)
              ·
                refine ⟨16347583335341692268163089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10898388890227794845442059 16347583335341692268163089)
                ·
                  refine ⟨12260687501506269201122317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16347583335341692268163089 12260687501506269201122317)
                  ·
                    refine ⟨4597757813064850950420869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12260687501506269201122317 4597757813064850950420869)
                    ·
                      refine ⟨862079589949659553203913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4597757813064850950420869 862079589949659553203913)
                      ·
                        rfl

theorem cell23_1678894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1678894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678894 prefixEnd_1678894 := by exact prefixLift 1678894
  have htrace : WordTrace (prefixWord ++ tailWord_1678894) baseStart_1678894 baseEnd_1678894 := by
    simpa [prefixWord, tailWord_1678894, baseEnd_1678894] using wordTrace_append hprefix tailTrace_1678894
  have hstable : (prefixWord ++ tailWord_1678894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678894).length < 2 ^ (prefixWord ++ tailWord_1678894).sum := by decide
  have hdescent : baseEnd_1678894 < baseStart_1678894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678911 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 1, 4, 2]
def baseStart_1678911 : Nat := 118140960795 + 1678911 * 2 ^ 59
def prefixEnd_1678911 : Nat := 4983230072969 + 3 ^ 40 * 1678911 * 2
def baseEnd_1678911 : Nat := 862088319120785986691335

theorem tailTrace_1678911 : CollatzResearch.WordTrace tailWord_1678911 prefixEnd_1678911 862088319120785986691335 := by
  unfold tailWord_1678911
  simp only [CollatzResearch.WordTrace]
  refine ⟨61234914820599657015756587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40823276547066438010504391 61234914820599657015756587)
  ·
    refine ⟨91852372230899485523634881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61234914820599657015756587 91852372230899485523634881)
    ·
      refine ⟨68889279173174614142726161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91852372230899485523634881 68889279173174614142726161)
      ·
        refine ⟨51666959379880960607044621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68889279173174614142726161 51666959379880960607044621)
        ·
          refine ⟨19375109767455360227641733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51666959379880960607044621 19375109767455360227641733)
          ·
            refine ⟨3632833081397880042682825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19375109767455360227641733 3632833081397880042682825)
            ·
              refine ⟨2724624811048410032012119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3632833081397880042682825 2724624811048410032012119)
              ·
                refine ⟨4086937216572615048018179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2724624811048410032012119 4086937216572615048018179)
                ·
                  refine ⟨6130405824858922572027269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4086937216572615048018179 6130405824858922572027269)
                  ·
                    refine ⟨1149451092161047982255113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6130405824858922572027269 1149451092161047982255113)
                    ·
                      refine ⟨862088319120785986691335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1149451092161047982255113 862088319120785986691335)
                      ·
                        rfl

theorem cell23_1678911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 4, 2].length) (baseStart_1678911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678911 prefixEnd_1678911 := by exact prefixLift 1678911
  have htrace : WordTrace (prefixWord ++ tailWord_1678911) baseStart_1678911 baseEnd_1678911 := by
    simpa [prefixWord, tailWord_1678911, baseEnd_1678911] using wordTrace_append hprefix tailTrace_1678911
  have hstable : (prefixWord ++ tailWord_1678911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678911).length < 2 ^ (prefixWord ++ tailWord_1678911).sum := by decide
  have hdescent : baseEnd_1678911 < baseStart_1678911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678917 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 7]
def baseStart_1678917 : Nat := 118140960795 + 1678917 * 2 ^ 59
def prefixEnd_1678917 : Nat := 4983230072969 + 3 ^ 40 * 1678917 * 2
def baseEnd_1678917 : Nat := 95787933333856995912923

theorem tailTrace_1678917 : CollatzResearch.WordTrace tailWord_1678917 prefixEnd_1678917 95787933333856995912923 := by
  unfold tailWord_1678917
  simp only [CollatzResearch.WordTrace]
  refine ⟨61235133658577920040475005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40823422439051946693650003 61235133658577920040475005)
  ·
    refine ⟨22963175121966720015178127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61235133658577920040475005 22963175121966720015178127)
    ·
      refine ⟨34444762682950080022767191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22963175121966720015178127 34444762682950080022767191)
      ·
        refine ⟨51667144024425120034150787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34444762682950080022767191 51667144024425120034150787)
        ·
          refine ⟨77500716036637680051226181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51667144024425120034150787 77500716036637680051226181)
          ·
            refine ⟨14531384256869565009604909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77500716036637680051226181 14531384256869565009604909)
            ·
              refine ⟨5449269096326086878601841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14531384256869565009604909 5449269096326086878601841)
              ·
                refine ⟨4086951822244565158951381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5449269096326086878601841 4086951822244565158951381)
                ·
                  refine ⟨95787933333856995912923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4086951822244565158951381 95787933333856995912923)
                  ·
                    rfl

theorem cell23_1678917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 7].length) (baseStart_1678917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1678917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1678917 prefixEnd_1678917 := by exact prefixLift 1678917
  have htrace : WordTrace (prefixWord ++ tailWord_1678917) baseStart_1678917 baseEnd_1678917 := by
    simpa [prefixWord, tailWord_1678917, baseEnd_1678917] using wordTrace_append hprefix tailTrace_1678917
  have hstable : (prefixWord ++ tailWord_1678917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678917).length < 2 ^ (prefixWord ++ tailWord_1678917).sum := by decide
  have hdescent : baseEnd_1678917 < baseStart_1678917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
