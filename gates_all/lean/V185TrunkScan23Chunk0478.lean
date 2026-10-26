import V185TrunkScan23Chunk0477

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2826908 : List Nat := [2, 2, 3, 2, 2, 1, 4, 2, 5]
def baseStart_2826908 : Nat := 118140960795 + 2826908 * 2 ^ 59
def prefixEnd_2826908 : Nat := 4983230072969 + 3 ^ 40 * 2826908 * 2
def baseEnd_2826908 : Nat := 161284730004481215905477

theorem tailTrace_2826908 : CollatzResearch.WordTrace tailWord_2826908 prefixEnd_2826908 161284730004481215905477 := by
  unfold tailWord_2826908
  simp only [CollatzResearch.WordTrace]
  refine ⟨51552902621301294147020689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68737203495068392196027585 51552902621301294147020689)
  ·
    refine ⟨38664676965975970610265517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51552902621301294147020689 38664676965975970610265517)
    ·
      refine ⟨14499253862240988978849569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38664676965975970610265517 14499253862240988978849569)
      ·
        refine ⟨10874440396680741734137177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14499253862240988978849569 10874440396680741734137177)
        ·
          refine ⟨8155830297510556300602883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10874440396680741734137177 8155830297510556300602883)
          ·
            refine ⟨12233745446265834450904325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8155830297510556300602883 12233745446265834450904325)
            ·
              refine ⟨2293827271174843959544561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12233745446265834450904325 2293827271174843959544561)
              ·
                refine ⟨1720370453381132969658421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2293827271174843959544561 1720370453381132969658421)
                ·
                  refine ⟨161284730004481215905477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1720370453381132969658421 161284730004481215905477)
                  ·
                    rfl

theorem cell23_2826908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 5].length) (baseStart_2826908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826908 prefixEnd_2826908 := by exact prefixLift 2826908
  have htrace : WordTrace (prefixWord ++ tailWord_2826908) baseStart_2826908 baseEnd_2826908 := by
    simpa [prefixWord, tailWord_2826908, baseEnd_2826908] using wordTrace_append hprefix tailTrace_2826908
  have hstable : (prefixWord ++ tailWord_2826908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826908).length < 2 ^ (prefixWord ++ tailWord_2826908).sum := by decide
  have hdescent : baseEnd_2826908 < baseStart_2826908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826917 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 2, 8]
def baseStart_2826917 : Nat := 118140960795 + 2826917 * 2 ^ 59
def prefixEnd_2826917 : Nat := 4983230072969 + 3 ^ 40 * 2826917 * 2
def baseEnd_2826917 : Nat := 483855730455407135978917

theorem tailTrace_2826917 : CollatzResearch.WordTrace tailWord_2826917 prefixEnd_2826917 483855730455407135978917 := by
  unfold tailWord_2826917
  simp only [CollatzResearch.WordTrace]
  refine ⟨103106133499569982831119005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68737422333046655220746003 103106133499569982831119005)
  ·
    refine ⟨38664800062338743561669627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103106133499569982831119005 38664800062338743561669627)
    ·
      refine ⟨57997200093508115342504441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38664800062338743561669627 57997200093508115342504441)
      ·
        refine ⟨43497900070131086506878331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57997200093508115342504441 43497900070131086506878331)
        ·
          refine ⟨65246850105196629760317497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43497900070131086506878331 65246850105196629760317497)
          ·
            refine ⟨48935137578897472320238123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65246850105196629760317497 48935137578897472320238123)
            ·
              refine ⟨73402706368346208480357185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48935137578897472320238123 73402706368346208480357185)
              ·
                refine ⟨55052029776259656360267889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73402706368346208480357185 55052029776259656360267889)
                ·
                  refine ⟨41289022332194742270200917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55052029776259656360267889 41289022332194742270200917)
                  ·
                    refine ⟨483855730455407135978917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41289022332194742270200917 483855730455407135978917)
                    ·
                      rfl

theorem cell23_2826917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_2826917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826917 prefixEnd_2826917 := by exact prefixLift 2826917
  have htrace : WordTrace (prefixWord ++ tailWord_2826917) baseStart_2826917 baseEnd_2826917 := by
    simpa [prefixWord, tailWord_2826917, baseEnd_2826917] using wordTrace_append hprefix tailTrace_2826917
  have hstable : (prefixWord ++ tailWord_2826917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826917).length < 2 ^ (prefixWord ++ tailWord_2826917).sum := by decide
  have hdescent : baseEnd_2826917 < baseStart_2826917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826941 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 2, 1, 4]
def baseStart_2826941 : Nat := 118140960795 + 2826941 * 2 ^ 59
def prefixEnd_2826941 : Nat := 4983230072969 + 3 ^ 40 * 2826941 * 2
def baseEnd_2826941 : Nat := 1451579514901929314036641

theorem tailTrace_2826941 : CollatzResearch.WordTrace tailWord_2826941 prefixEnd_2826941 1451579514901929314036641 := by
  unfold tailWord_2826941
  simp only [CollatzResearch.WordTrace]
  refine ⟨103107008851483034929992677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68738005900988689953328451 103107008851483034929992677)
  ·
    refine ⟨19332564159653069049373627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103107008851483034929992677 19332564159653069049373627)
    ·
      refine ⟨28998846239479603574060441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19332564159653069049373627 28998846239479603574060441)
      ·
        refine ⟨21749134679609702680545331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28998846239479603574060441 21749134679609702680545331)
        ·
          refine ⟨32623702019414554020817997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21749134679609702680545331 32623702019414554020817997)
          ·
            refine ⟨12233888257280457757806749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32623702019414554020817997 12233888257280457757806749)
            ·
              refine ⟨4587708096480171659177531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12233888257280457757806749 4587708096480171659177531)
              ·
                refine ⟨6881562144720257488766297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4587708096480171659177531 6881562144720257488766297)
                ·
                  refine ⟨5161171608540193116574723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6881562144720257488766297 5161171608540193116574723)
                  ·
                    refine ⟨7741757412810289674862085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5161171608540193116574723 7741757412810289674862085)
                    ·
                      refine ⟨1451579514901929314036641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7741757412810289674862085 1451579514901929314036641)
                      ·
                        rfl

theorem cell23_2826941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_2826941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826941 prefixEnd_2826941 := by exact prefixLift 2826941
  have htrace : WordTrace (prefixWord ++ tailWord_2826941) baseStart_2826941 baseEnd_2826941 := by
    simpa [prefixWord, tailWord_2826941, baseEnd_2826941] using wordTrace_append hprefix tailTrace_2826941
  have hstable : (prefixWord ++ tailWord_2826941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826941).length < 2 ^ (prefixWord ++ tailWord_2826941).sum := by decide
  have hdescent : baseEnd_2826941 < baseStart_2826941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826954 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_2826954 : Nat := 118140960795 + 2826954 * 2 ^ 59
def prefixEnd_2826954 : Nat := 4983230072969 + 3 ^ 40 * 2826954 * 2
def baseEnd_2826954 : Nat := 1451586190150437763174081

theorem tailTrace_2826954 : CollatzResearch.WordTrace tailWord_2826954 prefixEnd_2826954 1451586190150437763174081 := by
  unfold tailWord_2826954
  simp only [CollatzResearch.WordTrace]
  refine ⟨25776870750108984537553979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68738322000290625433477277 25776870750108984537553979)
  ·
    refine ⟨38665306125163476806330969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25776870750108984537553979 38665306125163476806330969)
    ·
      refine ⟨28998979593872607604748227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38665306125163476806330969 28998979593872607604748227)
      ·
        refine ⟨43498469390808911407122341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28998979593872607604748227 43498469390808911407122341)
        ·
          refine ⟨8155963010776670888835439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43498469390808911407122341 8155963010776670888835439)
          ·
            refine ⟨12233944516165006333253159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8155963010776670888835439 12233944516165006333253159)
            ·
              refine ⟨18350916774247509499879739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12233944516165006333253159 18350916774247509499879739)
              ·
                refine ⟨27526375161371264249819609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18350916774247509499879739 27526375161371264249819609)
                ·
                  refine ⟨20644781371028448187364707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27526375161371264249819609 20644781371028448187364707)
                  ·
                    refine ⟨30967172056542672281047061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20644781371028448187364707 30967172056542672281047061)
                    ·
                      refine ⟨1451586190150437763174081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30967172056542672281047061 1451586190150437763174081)
                      ·
                        rfl

theorem cell23_2826954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_2826954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826954 prefixEnd_2826954 := by exact prefixLift 2826954
  have htrace : WordTrace (prefixWord ++ tailWord_2826954) baseStart_2826954 baseEnd_2826954 := by
    simpa [prefixWord, tailWord_2826954, baseEnd_2826954] using wordTrace_append hprefix tailTrace_2826954
  have hstable : (prefixWord ++ tailWord_2826954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826954).length < 2 ^ (prefixWord ++ tailWord_2826954).sum := by decide
  have hdescent : baseEnd_2826954 < baseStart_2826954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826968 : List Nat := [2, 1, 2, 2, 3, 2, 2, 4, 1, 4]
def baseStart_2826968 : Nat := 118140960795 + 2826968 * 2 ^ 59
def prefixEnd_2826968 : Nat := 4983230072969 + 3 ^ 40 * 2826968 * 2
def baseEnd_2826968 : Nat := 483864459626533569466339

theorem tailTrace_2826968 : CollatzResearch.WordTrace tailWord_2826968 prefixEnd_2826968 483864459626533569466339 := by
  unfold tailWord_2826968
  simp only [CollatzResearch.WordTrace]
  refine ⟨51553996811192609270612779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68738662414923479027483705 51553996811192609270612779)
  ·
    refine ⟨77330995216788913905919169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51553996811192609270612779 77330995216788913905919169)
    ·
      refine ⟨57998246412591685429439377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77330995216788913905919169 57998246412591685429439377)
      ·
        refine ⟨43498684809443764072079533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57998246412591685429439377 43498684809443764072079533)
        ·
          refine ⟨16312006803541411527029825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43498684809443764072079533 16312006803541411527029825)
          ·
            refine ⟨12234005102656058645272369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16312006803541411527029825 12234005102656058645272369)
            ·
              refine ⟨9175503826992043983954277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12234005102656058645272369 9175503826992043983954277)
              ·
                refine ⟨1720406967561008246991427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9175503826992043983954277 1720406967561008246991427)
                ·
                  refine ⟨2580610451341512370487141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720406967561008246991427 2580610451341512370487141)
                  ·
                    refine ⟨483864459626533569466339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2580610451341512370487141 483864459626533569466339)
                    ·
                      rfl

theorem cell23_2826968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 1, 4].length) (baseStart_2826968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826968 prefixEnd_2826968 := by exact prefixLift 2826968
  have htrace : WordTrace (prefixWord ++ tailWord_2826968) baseStart_2826968 baseEnd_2826968 := by
    simpa [prefixWord, tailWord_2826968, baseEnd_2826968] using wordTrace_append hprefix tailTrace_2826968
  have hstable : (prefixWord ++ tailWord_2826968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826968).length < 2 ^ (prefixWord ++ tailWord_2826968).sum := by decide
  have hdescent : baseEnd_2826968 < baseStart_2826968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827001 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 6, 3, 2]
def baseStart_2827001 : Nat := 118140960795 + 2827001 * 2 ^ 59
def prefixEnd_2827001 : Nat := 4983230072969 + 3 ^ 40 * 2827001 * 2
def baseEnd_2827001 : Nat := 1451610323741199079286365

theorem tailTrace_2827001 : CollatzResearch.WordTrace tailWord_2827001 prefixEnd_2827001 1451610323741199079286365 := by
  unfold tailWord_2827001
  simp only [CollatzResearch.WordTrace]
  refine ⟨103109197231265665177176857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68739464820843776784784571 103109197231265665177176857)
  ·
    refine ⟨77331897923449248882882643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103109197231265665177176857 77331897923449248882882643)
    ·
      refine ⟨115997846885173873324323965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77331897923449248882882643 115997846885173873324323965)
      ·
        refine ⟨43499192581940202496621487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115997846885173873324323965 43499192581940202496621487)
        ·
          refine ⟨65248788872910303744932231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43499192581940202496621487 65248788872910303744932231)
          ·
            refine ⟨97873183309365455617398347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65248788872910303744932231 97873183309365455617398347)
            ·
              refine ⟨146809774964048183426097521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97873183309365455617398347 146809774964048183426097521)
              ·
                refine ⟨110107331223036137569573141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146809774964048183426097521 110107331223036137569573141)
                ·
                  refine ⟨5161281151079818948573741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110107331223036137569573141 5161281151079818948573741)
                  ·
                    refine ⟨1935480431654932105715153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5161281151079818948573741 1935480431654932105715153)
                    ·
                      refine ⟨1451610323741199079286365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935480431654932105715153 1451610323741199079286365)
                      ·
                        rfl

theorem cell23_2827001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_2827001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827001 prefixEnd_2827001 := by exact prefixLift 2827001
  have htrace : WordTrace (prefixWord ++ tailWord_2827001) baseStart_2827001 baseEnd_2827001 := by
    simpa [prefixWord, tailWord_2827001, baseEnd_2827001] using wordTrace_append hprefix tailTrace_2827001
  have hstable : (prefixWord ++ tailWord_2827001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827001).length < 2 ^ (prefixWord ++ tailWord_2827001).sum := by decide
  have hdescent : baseEnd_2827001 < baseStart_2827001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827018 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 2, 3, 2]
def baseStart_2827018 : Nat := 118140960795 + 2827018 * 2 ^ 59
def prefixEnd_2827018 : Nat := 4983230072969 + 3 ^ 40 * 2827018 * 2
def baseEnd_2827018 : Nat := 1451619052912325512773787

theorem tailTrace_2827018 : CollatzResearch.WordTrace tailWord_2827018 prefixEnd_2827018 1451619052912325512773787 := by
  unfold tailWord_2827018
  simp only [CollatzResearch.WordTrace]
  refine ⟨25777454318051019270136427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68739878181469384720363805 25777454318051019270136427)
  ·
    refine ⟨38666181477076528905204641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25777454318051019270136427 38666181477076528905204641)
    ·
      refine ⟨28999636107807396678903481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38666181477076528905204641 28999636107807396678903481)
      ·
        refine ⟨21749727080855547509177611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28999636107807396678903481 21749727080855547509177611)
        ·
          refine ⟨32624590621283321263766417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21749727080855547509177611 32624590621283321263766417)
          ·
            refine ⟨24468442965962490947824813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32624590621283321263766417 24468442965962490947824813)
            ·
              refine ⟨9175666112235934105434305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24468442965962490947824813 9175666112235934105434305)
              ·
                refine ⟨6881749584176950579075729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9175666112235934105434305 6881749584176950579075729)
                ·
                  refine ⟨5161312188132712934306797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6881749584176950579075729 5161312188132712934306797)
                  ·
                    refine ⟨1935492070549767350365049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5161312188132712934306797 1935492070549767350365049)
                    ·
                      refine ⟨1451619052912325512773787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935492070549767350365049 1451619052912325512773787)
                      ·
                        rfl

theorem cell23_2827018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_2827018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827018 prefixEnd_2827018 := by exact prefixLift 2827018
  have htrace : WordTrace (prefixWord ++ tailWord_2827018) baseStart_2827018 baseEnd_2827018 := by
    simpa [prefixWord, tailWord_2827018, baseEnd_2827018] using wordTrace_append hprefix tailTrace_2827018
  have hstable : (prefixWord ++ tailWord_2827018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827018).length < 2 ^ (prefixWord ++ tailWord_2827018).sum := by decide
  have hdescent : baseEnd_2827018 < baseStart_2827018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827061 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_2827061 : Nat := 118140960795 + 2827061 * 2 ^ 59
def prefixEnd_2827061 : Nat := 4983230072969 + 3 ^ 40 * 2827061 * 2
def baseEnd_2827061 : Nat := 1451641132580468844536089

theorem tailTrace_2827061 : CollatzResearch.WordTrace tailWord_2827061 prefixEnd_2827061 1451641132580468844536089 := by
  unfold tailWord_2827061
  simp only [CollatzResearch.WordTrace]
  refine ⟨103111385611048295424361037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68740923740698863616240691 103111385611048295424361037)
  ·
    refine ⟨38666769604143110784135389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103111385611048295424361037 38666769604143110784135389)
    ·
      refine ⟨14500038601553666544050771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38666769604143110784135389 14500038601553666544050771)
      ·
        refine ⟨21750057902330499816076157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14500038601553666544050771 21750057902330499816076157)
        ·
          refine ⟨8156271713373937431028559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21750057902330499816076157 8156271713373937431028559)
          ·
            refine ⟨12234407570060906146542839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8156271713373937431028559 12234407570060906146542839)
            ·
              refine ⟨18351611355091359219814259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12234407570060906146542839 18351611355091359219814259)
              ·
                refine ⟨27527417032637038829721389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18351611355091359219814259 27527417032637038829721389)
                ·
                  refine ⟨10322781387238889561145521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27527417032637038829721389 10322781387238889561145521)
                  ·
                    refine ⟨7742086040429167170859141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10322781387238889561145521 7742086040429167170859141)
                    ·
                      refine ⟨1451641132580468844536089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7742086040429167170859141 1451641132580468844536089)
                      ·
                        rfl

theorem cell23_2827061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_2827061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827061 prefixEnd_2827061 := by exact prefixLift 2827061
  have htrace : WordTrace (prefixWord ++ tailWord_2827061) baseStart_2827061 baseEnd_2827061 := by
    simpa [prefixWord, tailWord_2827061, baseEnd_2827061] using wordTrace_append hprefix tailTrace_2827061
  have hstable : (prefixWord ++ tailWord_2827061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827061).length < 2 ^ (prefixWord ++ tailWord_2827061).sum := by decide
  have hdescent : baseEnd_2827061 < baseStart_2827061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827062 : List Nat := [5, 1, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_2827062 : Nat := 118140960795 + 2827062 * 2 ^ 59
def prefixEnd_2827062 : Nat := 4983230072969 + 3 ^ 40 * 2827062 * 2
def baseEnd_2827062 : Nat := 483880548687041113541195

theorem tailTrace_2827062 : CollatzResearch.WordTrace tailWord_2827062 prefixEnd_2827062 483880548687041113541195 := by
  unfold tailWord_2827062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6444463880252792037196715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68740948056029781730098293 6444463880252792037196715)
  ·
    refine ⟨9666695820379188055795073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6444463880252792037196715 9666695820379188055795073)
    ·
      refine ⟨7250021865284391041846305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9666695820379188055795073 7250021865284391041846305)
      ·
        refine ⟨5437516398963293281384729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7250021865284391041846305 5437516398963293281384729)
        ·
          refine ⟨4078137299222469961038547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5437516398963293281384729 4078137299222469961038547)
          ·
            refine ⟨6117205948833704941557821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4078137299222469961038547 6117205948833704941557821)
            ·
              refine ⟨2293952230812639353084183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6117205948833704941557821 2293952230812639353084183)
              ·
                refine ⟨3440928346218959029626275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293952230812639353084183 3440928346218959029626275)
                ·
                  refine ⟨5161392519328438544439413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3440928346218959029626275 5161392519328438544439413)
                  ·
                    refine ⟨483880548687041113541195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5161392519328438544439413 483880548687041113541195)
                    ·
                      rfl

theorem cell23_2827062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_2827062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827062 prefixEnd_2827062 := by exact prefixLift 2827062
  have htrace : WordTrace (prefixWord ++ tailWord_2827062) baseStart_2827062 baseEnd_2827062 := by
    simpa [prefixWord, tailWord_2827062, baseEnd_2827062] using wordTrace_append hprefix tailTrace_2827062
  have hstable : (prefixWord ++ tailWord_2827062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827062).length < 2 ^ (prefixWord ++ tailWord_2827062).sum := by decide
  have hdescent : baseEnd_2827062 < baseStart_2827062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827098 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3]
def baseStart_2827098 : Nat := 118140960795 + 2827098 * 2 ^ 59
def prefixEnd_2827098 : Nat := 4983230072969 + 3 ^ 40 * 2827098 * 2
def baseEnd_2827098 : Nat := 1451660131364685199773419

theorem tailTrace_2827098 : CollatzResearch.WordTrace tailWord_2827098 prefixEnd_2827098 1451660131364685199773419 := by
  unfold tailWord_2827098
  simp only [CollatzResearch.WordTrace]
  refine ⟨25778183777978562685864487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68741823407942833828971965 25778183777978562685864487)
  ·
    refine ⟨38667275666967844028796731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25778183777978562685864487 38667275666967844028796731)
    ·
      refine ⟨58000913500451766043195097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38667275666967844028796731 58000913500451766043195097)
      ·
        refine ⟨43500685125338824532396323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58000913500451766043195097 43500685125338824532396323)
        ·
          refine ⟨65251027688008236798594485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43500685125338824532396323 65251027688008236798594485)
          ·
            refine ⟨6117283845750772199868233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65251027688008236798594485 6117283845750772199868233)
            ·
              refine ⟨4587962884313079149901175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6117283845750772199868233 4587962884313079149901175)
              ·
                refine ⟨6881944326469618724851763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4587962884313079149901175 6881944326469618724851763)
                ·
                  refine ⟨10322916489704428087277645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6881944326469618724851763 10322916489704428087277645)
                  ·
                    refine ⟨3871093683639160532729117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10322916489704428087277645 3871093683639160532729117)
                    ·
                      refine ⟨1451660131364685199773419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3871093683639160532729117 1451660131364685199773419)
                      ·
                        rfl

theorem cell23_2827098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_2827098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827098 prefixEnd_2827098 := by exact prefixLift 2827098
  have htrace : WordTrace (prefixWord ++ tailWord_2827098) baseStart_2827098 baseEnd_2827098 := by
    simpa [prefixWord, tailWord_2827098, baseEnd_2827098] using wordTrace_append hprefix tailTrace_2827098
  have hstable : (prefixWord ++ tailWord_2827098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827098).length < 2 ^ (prefixWord ++ tailWord_2827098).sum := by decide
  have hdescent : baseEnd_2827098 < baseStart_2827098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827171 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 3]
def baseStart_2827171 : Nat := 118140960795 + 2827171 * 2 ^ 59
def prefixEnd_2827171 : Nat := 4983230072969 + 3 ^ 40 * 2827171 * 2
def baseEnd_2827171 : Nat := 1451697615452463414160583

theorem tailTrace_2827171 : CollatzResearch.WordTrace tailWord_2827171 prefixEnd_2827171 1451697615452463414160583 := by
  unfold tailWord_2827171
  simp only [CollatzResearch.WordTrace]
  refine ⟨103115397640649784210865367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68743598427099856140576911 103115397640649784210865367)
  ·
    refine ⟨154673096460974676316298051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103115397640649784210865367 154673096460974676316298051)
    ·
      refine ⟨232009644691462014474447077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154673096460974676316298051 232009644691462014474447077)
      ·
        refine ⟨43501808379649127713958827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232009644691462014474447077 43501808379649127713958827)
        ·
          refine ⟨65252712569473691570938241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43501808379649127713958827 65252712569473691570938241)
          ·
            refine ⟨48939534427105268678203681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65252712569473691570938241 48939534427105268678203681)
            ·
              refine ⟨36704650820328951508652761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48939534427105268678203681 36704650820328951508652761)
              ·
                refine ⟨27528488115246713631489571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36704650820328951508652761 27528488115246713631489571)
                ·
                  refine ⟨41292732172870070447234357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27528488115246713631489571 41292732172870070447234357)
                  ·
                    refine ⟨3871193641206569104428221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41292732172870070447234357 3871193641206569104428221)
                    ·
                      refine ⟨1451697615452463414160583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3871193641206569104428221 1451697615452463414160583)
                      ·
                        rfl

theorem cell23_2827171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_2827171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827171 prefixEnd_2827171 := by exact prefixLift 2827171
  have htrace : WordTrace (prefixWord ++ tailWord_2827171) baseStart_2827171 baseEnd_2827171 := by
    simpa [prefixWord, tailWord_2827171, baseEnd_2827171] using wordTrace_append hprefix tailTrace_2827171
  have hstable : (prefixWord ++ tailWord_2827171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827171).length < 2 ^ (prefixWord ++ tailWord_2827171).sum := by decide
  have hdescent : baseEnd_2827171 < baseStart_2827171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827191 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 4, 5]
def baseStart_2827191 : Nat := 118140960795 + 2827191 * 2 ^ 59
def prefixEnd_2827191 : Nat := 4983230072969 + 3 ^ 40 * 2827191 * 2
def baseEnd_2827191 : Nat := 483902628355184445303497

theorem tailTrace_2827191 : CollatzResearch.WordTrace tailWord_2827191 prefixEnd_2827191 483902628355184445303497 := by
  unfold tailWord_2827191
  simp only [CollatzResearch.WordTrace]
  refine ⟨103116127100577327626593427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68744084733718218417728951 103116127100577327626593427)
  ·
    refine ⟨154674190650865991439890141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103116127100577327626593427 154674190650865991439890141)
    ·
      refine ⟨58002821494074746789958803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154674190650865991439890141 58002821494074746789958803)
      ·
        refine ⟨87004232241112120184938205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58002821494074746789958803 87004232241112120184938205)
        ·
          refine ⟨32626587090417045069351827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87004232241112120184938205 32626587090417045069351827)
          ·
            refine ⟨48939880635625567604027741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32626587090417045069351827 48939880635625567604027741)
            ·
              refine ⟨18352455238359587851510403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48939880635625567604027741 18352455238359587851510403)
              ·
                refine ⟨27528682857539381777265605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18352455238359587851510403 27528682857539381777265605)
                ·
                  refine ⟨5161628035788634083237301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27528682857539381777265605 5161628035788634083237301)
                  ·
                    refine ⟨483902628355184445303497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5161628035788634083237301 483902628355184445303497)
                    ·
                      rfl

theorem cell23_2827191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_2827191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827191 prefixEnd_2827191 := by exact prefixLift 2827191
  have htrace : WordTrace (prefixWord ++ tailWord_2827191) baseStart_2827191 baseEnd_2827191 := by
    simpa [prefixWord, tailWord_2827191, baseEnd_2827191] using wordTrace_append hprefix tailTrace_2827191
  have hstable : (prefixWord ++ tailWord_2827191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827191).length < 2 ^ (prefixWord ++ tailWord_2827191).sum := by decide
  have hdescent : baseEnd_2827191 < baseStart_2827191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827312 : List Nat := [2, 1, 1, 1, 2, 4, 1, 6, 1, 1, 3]
def baseStart_2827312 : Nat := 118140960795 + 2827312 * 2 ^ 59
def prefixEnd_2827312 : Nat := 4983230072969 + 3 ^ 40 * 2827312 * 2
def baseEnd_2827312 : Nat := 1451770016224747362497435

theorem tailTrace_2827312 : CollatzResearch.WordTrace tailWord_2827312 prefixEnd_2827312 1451770016224747362497435 := by
  unfold tailWord_2827312
  simp only [CollatzResearch.WordTrace]
  refine ⟨51560270166569482645874095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68747026888759310194498793 51560270166569482645874095)
  ·
    refine ⟨77340405249854223968811143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51560270166569482645874095 77340405249854223968811143)
    ·
      refine ⟨116010607874781335953216715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77340405249854223968811143 116010607874781335953216715)
      ·
        refine ⟨174015911812172003929825073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116010607874781335953216715 174015911812172003929825073)
        ·
          refine ⟨130511933859129002947368805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174015911812172003929825073 130511933859129002947368805)
          ·
            refine ⟨24470987598586688052631651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130511933859129002947368805 24470987598586688052631651)
            ·
              refine ⟨36706481397880032078947477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24470987598586688052631651 36706481397880032078947477)
              ·
                refine ⟨1720616315525626503700663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36706481397880032078947477 1720616315525626503700663)
                ·
                  refine ⟨2580924473288439755550995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720616315525626503700663 2580924473288439755550995)
                  ·
                    refine ⟨3871386709932659633326493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2580924473288439755550995 3871386709932659633326493)
                    ·
                      refine ⟨1451770016224747362497435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3871386709932659633326493 1451770016224747362497435)
                      ·
                        rfl

theorem cell23_2827312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6, 1, 1, 3].length) (baseStart_2827312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827312 prefixEnd_2827312 := by exact prefixLift 2827312
  have htrace : WordTrace (prefixWord ++ tailWord_2827312) baseStart_2827312 baseEnd_2827312 := by
    simpa [prefixWord, tailWord_2827312, baseEnd_2827312] using wordTrace_append hprefix tailTrace_2827312
  have hstable : (prefixWord ++ tailWord_2827312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827312).length < 2 ^ (prefixWord ++ tailWord_2827312).sum := by decide
  have hdescent : baseEnd_2827312 < baseStart_2827312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827335 : List Nat := [1, 1, 4, 1, 3, 2, 1, 4, 1, 1, 4]
def baseStart_2827335 : Nat := 118140960795 + 2827335 * 2 ^ 59
def prefixEnd_2827335 : Nat := 4983230072969 + 3 ^ 40 * 2827335 * 2
def baseEnd_2827335 : Nat := 1451781826279800772509829

theorem tailTrace_2827335 : CollatzResearch.WordTrace tailWord_2827335 prefixEnd_2827335 1451781826279800772509829 := by
  unfold tailWord_2827335
  simp only [CollatzResearch.WordTrace]
  refine ⟨103121379212055640219835459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68747586141370426813223639 103121379212055640219835459)
  ·
    refine ⟨154682068818083460329753189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103121379212055640219835459 154682068818083460329753189)
    ·
      refine ⟨29002887903390648811828723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154682068818083460329753189 29002887903390648811828723)
      ·
        refine ⟨43504331855085973217743085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29002887903390648811828723 43504331855085973217743085)
        ·
          refine ⟨16314124445657239956653657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43504331855085973217743085 16314124445657239956653657)
          ·
            refine ⟨12235593334242929967490243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16314124445657239956653657 12235593334242929967490243)
            ·
              refine ⟨18353390001364394951235365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12235593334242929967490243 18353390001364394951235365)
              ·
                refine ⟨3441260625255824053356631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18353390001364394951235365 3441260625255824053356631)
                ·
                  refine ⟨5161890937883736080034947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3441260625255824053356631 5161890937883736080034947)
                  ·
                    refine ⟨7742836406825604120052421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5161890937883736080034947 7742836406825604120052421)
                    ·
                      refine ⟨1451781826279800772509829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7742836406825604120052421 1451781826279800772509829)
                      ·
                        rfl

theorem cell23_2827335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_2827335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827335 prefixEnd_2827335 := by exact prefixLift 2827335
  have htrace : WordTrace (prefixWord ++ tailWord_2827335) baseStart_2827335 baseEnd_2827335 := by
    simpa [prefixWord, tailWord_2827335, baseEnd_2827335] using wordTrace_append hprefix tailTrace_2827335
  have hstable : (prefixWord ++ tailWord_2827335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827335).length < 2 ^ (prefixWord ++ tailWord_2827335).sum := by decide
  have hdescent : baseEnd_2827335 < baseStart_2827335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827346 : List Nat := [3, 2, 2, 1, 3, 3, 1, 3, 1, 1, 3]
def baseStart_2827346 : Nat := 118140960795 + 2827346 * 2 ^ 59
def prefixEnd_2827346 : Nat := 4983230072969 + 3 ^ 40 * 2827346 * 2
def baseEnd_2827346 : Nat := 1451787474567000229472279

theorem tailTrace_2827346 : CollatzResearch.WordTrace tailWord_2827346 prefixEnd_2827346 1451787474567000229472279 := by
  unfold tailWord_2827346
  simp only [CollatzResearch.WordTrace]
  refine ⟨25780445103753947274621473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68747853610010526065657261 25780445103753947274621473)
  ·
    refine ⟨19335333827815460455966105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25780445103753947274621473 19335333827815460455966105)
    ·
      refine ⟨14501500370861595341974579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19335333827815460455966105 14501500370861595341974579)
      ·
        refine ⟨21752250556292393012961869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14501500370861595341974579 21752250556292393012961869)
        ·
          refine ⟨8157093958609647379860701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21752250556292393012961869 8157093958609647379860701)
          ·
            refine ⟨3058910234478617767447763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8157093958609647379860701 3058910234478617767447763)
            ·
              refine ⟨4588365351717926651171645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3058910234478617767447763 4588365351717926651171645)
              ·
                refine ⟨1720637006894222494189367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4588365351717926651171645 1720637006894222494189367)
                ·
                  refine ⟨2580955510341333741284051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720637006894222494189367 2580955510341333741284051)
                  ·
                    refine ⟨3871433265512000611926077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2580955510341333741284051 3871433265512000611926077)
                    ·
                      refine ⟨1451787474567000229472279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3871433265512000611926077 1451787474567000229472279)
                      ·
                        rfl

theorem cell23_2827346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_2827346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827346 prefixEnd_2827346 := by exact prefixLift 2827346
  have htrace : WordTrace (prefixWord ++ tailWord_2827346) baseStart_2827346 baseEnd_2827346 := by
    simpa [prefixWord, tailWord_2827346, baseEnd_2827346] using wordTrace_append hprefix tailTrace_2827346
  have hstable : (prefixWord ++ tailWord_2827346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827346).length < 2 ^ (prefixWord ++ tailWord_2827346).sum := by decide
  have hdescent : baseEnd_2827346 < baseStart_2827346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827362 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_2827362 : Nat := 118140960795 + 2827362 * 2 ^ 59
def prefixEnd_2827362 : Nat := 4983230072969 + 3 ^ 40 * 2827362 * 2
def baseEnd_2827362 : Nat := 483931896752490722290735

theorem tailTrace_2827362 : CollatzResearch.WordTrace tailWord_2827362 prefixEnd_2827362 483931896752490722290735 := by
  unfold tailWord_2827362
  simp only [CollatzResearch.WordTrace]
  refine ⟨25780590995739455957767085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68748242655305215887378893 25780590995739455957767085)
  ·
    refine ⟨9667721623402295984162657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25780590995739455957767085 9667721623402295984162657)
    ·
      refine ⟨7250791217551721988121993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9667721623402295984162657 7250791217551721988121993)
      ·
        refine ⟨5438093413163791491091495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7250791217551721988121993 5438093413163791491091495)
        ·
          refine ⟨8157140119745687236637243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5438093413163791491091495 8157140119745687236637243)
          ·
            refine ⟨12235710179618530854955865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8157140119745687236637243 12235710179618530854955865)
            ·
              refine ⟨9176782634713898141216899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12235710179618530854955865 9176782634713898141216899)
              ·
                refine ⟨13765173952070847211825349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9176782634713898141216899 13765173952070847211825349)
                ·
                  refine ⟨2580970116013283852217253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13765173952070847211825349 2580970116013283852217253)
                  ·
                    refine ⟨483931896752490722290735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2580970116013283852217253 483931896752490722290735)
                    ·
                      rfl

theorem cell23_2827362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_2827362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827362 prefixEnd_2827362 := by exact prefixLift 2827362
  have htrace : WordTrace (prefixWord ++ tailWord_2827362) baseStart_2827362 baseEnd_2827362 := by
    simpa [prefixWord, tailWord_2827362, baseEnd_2827362] using wordTrace_append hprefix tailTrace_2827362
  have hstable : (prefixWord ++ tailWord_2827362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827362).length < 2 ^ (prefixWord ++ tailWord_2827362).sum := by decide
  have hdescent : baseEnd_2827362 < baseStart_2827362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827369 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 3, 2, 2]
def baseStart_2827369 : Nat := 118140960795 + 2827369 * 2 ^ 59
def prefixEnd_2827369 : Nat := 4983230072969 + 3 ^ 40 * 2827369 * 2
def baseEnd_2827369 : Nat := 1451799284622053639484673

theorem tailTrace_2827369 : CollatzResearch.WordTrace tailWord_2827369 prefixEnd_2827369 1451799284622053639484673 := by
  unfold tailWord_2827369
  simp only [CollatzResearch.WordTrace]
  refine ⟨103122619293932464026573161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68748412862621642684382107 103122619293932464026573161)
  ·
    refine ⟨77341964470449348019929871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103122619293932464026573161 77341964470449348019929871)
    ·
      refine ⟨116012946705674022029894807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77341964470449348019929871 116012946705674022029894807)
      ·
        refine ⟨174019420058511033044842211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116012946705674022029894807 174019420058511033044842211)
        ·
          refine ⟨261029130087766549567263317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174019420058511033044842211 261029130087766549567263317)
          ·
            refine ⟨3058935118216014252741367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 261029130087766549567263317 3058935118216014252741367)
            ·
              refine ⟨4588402677324021379112051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3058935118216014252741367 4588402677324021379112051)
              ·
                refine ⟨6882604015986032068668077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4588402677324021379112051 6882604015986032068668077)
                ·
                  refine ⟨2580976505994762025750529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6882604015986032068668077 2580976505994762025750529)
                  ·
                    refine ⟨1935732379496071519312897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2580976505994762025750529 1935732379496071519312897)
                    ·
                      refine ⟨1451799284622053639484673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935732379496071519312897 1451799284622053639484673)
                      ·
                        rfl

theorem cell23_2827369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 2, 2].length) (baseStart_2827369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827369 prefixEnd_2827369 := by exact prefixLift 2827369
  have htrace : WordTrace (prefixWord ++ tailWord_2827369) baseStart_2827369 baseEnd_2827369 := by
    simpa [prefixWord, tailWord_2827369, baseEnd_2827369] using wordTrace_append hprefix tailTrace_2827369
  have hstable : (prefixWord ++ tailWord_2827369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827369).length < 2 ^ (prefixWord ++ tailWord_2827369).sum := by decide
  have hdescent : baseEnd_2827369 < baseStart_2827369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827378 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_2827378 : Nat := 118140960795 + 2827378 * 2 ^ 59
def prefixEnd_2827378 : Nat := 4983230072969 + 3 ^ 40 * 2827378 * 2
def baseEnd_2827378 : Nat := 1451803905947944104272131

theorem tailTrace_2827378 : CollatzResearch.WordTrace tailWord_2827378 prefixEnd_2827378 1451803905947944104272131 := by
  unfold tailWord_2827378
  simp only [CollatzResearch.WordTrace]
  refine ⟨25780736887724964640912697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68748631700599905709100525 25780736887724964640912697)
  ·
    refine ⟨19335552665793723480684523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25780736887724964640912697 19335552665793723480684523)
    ·
      refine ⟨29003328998690585221026785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19335552665793723480684523 29003328998690585221026785)
      ·
        refine ⟨21752496749017938915770089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29003328998690585221026785 21752496749017938915770089)
        ·
          refine ⟨16314372561763454186827567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21752496749017938915770089 16314372561763454186827567)
          ·
            refine ⟨24471558842645181280241351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16314372561763454186827567 24471558842645181280241351)
            ·
              refine ⟨36707338263967771920362027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24471558842645181280241351 36707338263967771920362027)
              ·
                refine ⟨55061007395951657880543041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36707338263967771920362027 55061007395951657880543041)
                ·
                  refine ⟨41295755546963743410407281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55061007395951657880543041 41295755546963743410407281)
                  ·
                    refine ⟨30971816660222807557805461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41295755546963743410407281 30971816660222807557805461)
                    ·
                      refine ⟨1451803905947944104272131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30971816660222807557805461 1451803905947944104272131)
                      ·
                        rfl

theorem cell23_2827378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_2827378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827378 prefixEnd_2827378 := by exact prefixLift 2827378
  have htrace : WordTrace (prefixWord ++ tailWord_2827378) baseStart_2827378 baseEnd_2827378 := by
    simpa [prefixWord, tailWord_2827378, baseEnd_2827378] using wordTrace_append hprefix tailTrace_2827378
  have hstable : (prefixWord ++ tailWord_2827378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827378).length < 2 ^ (prefixWord ++ tailWord_2827378).sum := by decide
  have hdescent : baseEnd_2827378 < baseStart_2827378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827442 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2]
def baseStart_2827442 : Nat := 118140960795 + 2827442 * 2 ^ 59
def prefixEnd_2827442 : Nat := 4983230072969 + 3 ^ 40 * 2827442 * 2
def baseEnd_2827442 : Nat := 1451836768709831853871837

theorem tailTrace_2827442 : CollatzResearch.WordTrace tailWord_2827442 prefixEnd_2827442 1451836768709831853871837 := by
  unfold tailWord_2827442
  simp only [CollatzResearch.WordTrace]
  refine ⟨25781320455666999373495145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68750187881778664995987053 25781320455666999373495145)
  ·
    refine ⟨19335990341750249530121359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25781320455666999373495145 19335990341750249530121359)
    ·
      refine ⟨29003985512625374295182039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19335990341750249530121359 29003985512625374295182039)
      ·
        refine ⟨43505978268938061442773059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29003985512625374295182039 43505978268938061442773059)
        ·
          refine ⟨65258967403407092164159589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43505978268938061442773059 65258967403407092164159589)
          ·
            refine ⟨12236056388138829780779923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65258967403407092164159589 12236056388138829780779923)
            ·
              refine ⟨18354084582208244671169885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12236056388138829780779923 18354084582208244671169885)
              ·
                refine ⟨6882781718328091751688707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18354084582208244671169885 6882781718328091751688707)
                ·
                  refine ⟨10324172577492137627533061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6882781718328091751688707 10324172577492137627533061)
                  ·
                    refine ⟨1935782358279775805162449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10324172577492137627533061 1935782358279775805162449)
                    ·
                      refine ⟨1451836768709831853871837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935782358279775805162449 1451836768709831853871837)
                      ·
                        rfl

theorem cell23_2827442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_2827442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827442 prefixEnd_2827442 := by exact prefixLift 2827442
  have htrace : WordTrace (prefixWord ++ tailWord_2827442) baseStart_2827442 baseEnd_2827442 := by
    simpa [prefixWord, tailWord_2827442, baseEnd_2827442] using wordTrace_append hprefix tailTrace_2827442
  have hstable : (prefixWord ++ tailWord_2827442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827442).length < 2 ^ (prefixWord ++ tailWord_2827442).sum := by decide
  have hdescent : baseEnd_2827442 < baseStart_2827442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827493 : List Nat := [1, 3, 1, 4, 3, 1, 3, 1, 2, 2, 2]
def baseStart_2827493 : Nat := 118140960795 + 2827493 * 2 ^ 59
def prefixEnd_2827493 : Nat := 4983230072969 + 3 ^ 40 * 2827493 * 2
def baseEnd_2827493 : Nat := 1451862956223211154334103

theorem tailTrace_2827493 : CollatzResearch.WordTrace tailWord_2827493 prefixEnd_2827493 1451862956223211154334103 := by
  unfold tailWord_2827493
  simp only [CollatzResearch.WordTrace]
  refine ⟨103127141945483233204087133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68751427963655488802724755 103127141945483233204087133)
  ·
    refine ⟨38672678229556212451532675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103127141945483233204087133 38672678229556212451532675)
    ·
      refine ⟨58009017344334318677299013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38672678229556212451532675 58009017344334318677299013)
      ·
        refine ⟨10876690752062684751993565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58009017344334318677299013 10876690752062684751993565)
        ·
          refine ⟨4078759032023506781997587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10876690752062684751993565 4078759032023506781997587)
          ·
            refine ⟨6118138548035260172996381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4078759032023506781997587 6118138548035260172996381)
            ·
              refine ⟨2294301955513222564873643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6118138548035260172996381 2294301955513222564873643)
              ·
                refine ⟨3441452933269833847310465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2294301955513222564873643 3441452933269833847310465)
                ·
                  refine ⟨2581089699952375385482849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3441452933269833847310465 2581089699952375385482849)
                  ·
                    refine ⟨1935817274964281539112137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2581089699952375385482849 1935817274964281539112137)
                    ·
                      refine ⟨1451862956223211154334103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935817274964281539112137 1451862956223211154334103)
                      ·
                        rfl

theorem cell23_2827493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_2827493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827493 prefixEnd_2827493 := by exact prefixLift 2827493
  have htrace : WordTrace (prefixWord ++ tailWord_2827493) baseStart_2827493 baseEnd_2827493 := by
    simpa [prefixWord, tailWord_2827493, baseEnd_2827493] using wordTrace_append hprefix tailTrace_2827493
  have hstable : (prefixWord ++ tailWord_2827493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827493).length < 2 ^ (prefixWord ++ tailWord_2827493).sum := by decide
  have hdescent : baseEnd_2827493 < baseStart_2827493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827502 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 2, 5, 2]
def baseStart_2827502 : Nat := 118140960795 + 2827502 * 2 ^ 59
def prefixEnd_2827502 : Nat := 4983230072969 + 3 ^ 40 * 2827502 * 2
def baseEnd_2827502 : Nat := 1451867577549101619121561

theorem tailTrace_2827502 : CollatzResearch.WordTrace tailWord_2827502 prefixEnd_2827502 1451867577549101619121561 := by
  unfold tailWord_2827502
  simp only [CollatzResearch.WordTrace]
  refine ⟨12890933775306328467645595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68751646801633751827443173 12890933775306328467645595)
  ·
    refine ⟨19336400662959492701468393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12890933775306328467645595 19336400662959492701468393)
    ·
      refine ⟨14502300497219619526101295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19336400662959492701468393 14502300497219619526101295)
      ·
        refine ⟨21753450745829429289151943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14502300497219619526101295 21753450745829429289151943)
        ·
          refine ⟨32630176118744143933727915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21753450745829429289151943 32630176118744143933727915)
          ·
            refine ⟨48945264178116215900591873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32630176118744143933727915 48945264178116215900591873)
            ·
              refine ⟨36708948133587161925443905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48945264178116215900591873 36708948133587161925443905)
              ·
                refine ⟨27531711100190371444082929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36708948133587161925443905 27531711100190371444082929)
                ·
                  refine ⟨20648783325142778583062197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27531711100190371444082929 20648783325142778583062197)
                  ·
                    refine ⟨1935823436732135492162081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20648783325142778583062197 1935823436732135492162081)
                    ·
                      refine ⟨1451867577549101619121561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935823436732135492162081 1451867577549101619121561)
                      ·
                        rfl

theorem cell23_2827502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_2827502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827502 prefixEnd_2827502 := by exact prefixLift 2827502
  have htrace : WordTrace (prefixWord ++ tailWord_2827502) baseStart_2827502 baseEnd_2827502 := by
    simpa [prefixWord, tailWord_2827502, baseEnd_2827502] using wordTrace_append hprefix tailTrace_2827502
  have hstable : (prefixWord ++ tailWord_2827502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827502).length < 2 ^ (prefixWord ++ tailWord_2827502).sum := by decide
  have hdescent : baseEnd_2827502 < baseStart_2827502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827516 : List Nat := [2, 2, 2, 1, 6, 1, 1, 3, 5]
def baseStart_2827516 : Nat := 118140960795 + 2827516 * 2 ^ 59
def prefixEnd_2827516 : Nat := 4983230072969 + 3 ^ 40 * 2827516 * 2
def baseEnd_2827516 : Nat := 161319418475362729371833

theorem tailTrace_2827516 : CollatzResearch.WordTrace tailWord_2827516 prefixEnd_2827516 161319418475362729371833 := by
  unfold tailWord_2827516
  simp only [CollatzResearch.WordTrace]
  refine ⟨51563990412199954066087201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68751987216266605421449601 51563990412199954066087201)
  ·
    refine ⟨38672992809149965549565401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51563990412199954066087201 38672992809149965549565401)
    ·
      refine ⟨29004744606862474162174051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38672992809149965549565401 29004744606862474162174051)
      ·
        refine ⟨43507116910293711243261077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29004744606862474162174051 43507116910293711243261077)
        ·
          refine ⟨2039396105170017714527863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43507116910293711243261077 2039396105170017714527863)
          ·
            refine ⟨3059094157755026571791795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2039396105170017714527863 3059094157755026571791795)
            ·
              refine ⟨4588641236632539857687693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3059094157755026571791795 4588641236632539857687693)
              ·
                refine ⟨1720740463737202446632885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4588641236632539857687693 1720740463737202446632885)
                ·
                  refine ⟨161319418475362729371833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1720740463737202446632885 161319418475362729371833)
                  ·
                    rfl

theorem cell23_2827516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 5].length) (baseStart_2827516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827516 prefixEnd_2827516 := by exact prefixLift 2827516
  have htrace : WordTrace (prefixWord ++ tailWord_2827516) baseStart_2827516 baseEnd_2827516 := by
    simpa [prefixWord, tailWord_2827516, baseEnd_2827516] using wordTrace_append hprefix tailTrace_2827516
  have hstable : (prefixWord ++ tailWord_2827516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827516).length < 2 ^ (prefixWord ++ tailWord_2827516).sum := by decide
  have hdescent : baseEnd_2827516 < baseStart_2827516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827532 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 2, 1, 4]
def baseStart_2827532 : Nat := 118140960795 + 2827532 * 2 ^ 59
def prefixEnd_2827532 : Nat := 4983230072969 + 3 ^ 40 * 2827532 * 2
def baseEnd_2827532 : Nat := 1451882981968736501746423

theorem tailTrace_2827532 : CollatzResearch.WordTrace tailWord_2827532 prefixEnd_2827532 1451882981968736501746423 := by
  unfold tailWord_2827532
  simp only [CollatzResearch.WordTrace]
  refine ⟨51564282196170971432378425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68752376261561295243171233 51564282196170971432378425)
  ·
    refine ⟨38673211647128228574283819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51564282196170971432378425 38673211647128228574283819)
    ·
      refine ⟨58009817470692342861425729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38673211647128228574283819 58009817470692342861425729)
      ·
        refine ⟨43507363103019257146069297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58009817470692342861425729 43507363103019257146069297)
        ·
          refine ⟨32630522327264442859551973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43507363103019257146069297 32630522327264442859551973)
          ·
            refine ⟨6118222936362083036165995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32630522327264442859551973 6118222936362083036165995)
            ·
              refine ⟨9177334404543124554248993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6118222936362083036165995 9177334404543124554248993)
              ·
                refine ⟨6883000803407343415686745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9177334404543124554248993 6883000803407343415686745)
                ·
                  refine ⟨5162250602555507561765059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6883000803407343415686745 5162250602555507561765059)
                  ·
                    refine ⟨7743375903833261342647589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5162250602555507561765059 7743375903833261342647589)
                    ·
                      refine ⟨1451882981968736501746423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7743375903833261342647589 1451882981968736501746423)
                      ·
                        rfl

theorem cell23_2827532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_2827532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827532 prefixEnd_2827532 := by exact prefixLift 2827532
  have htrace : WordTrace (prefixWord ++ tailWord_2827532) baseStart_2827532 baseEnd_2827532 := by
    simpa [prefixWord, tailWord_2827532, baseEnd_2827532] using wordTrace_append hprefix tailTrace_2827532
  have hstable : (prefixWord ++ tailWord_2827532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827532).length < 2 ^ (prefixWord ++ tailWord_2827532).sum := by decide
  have hdescent : baseEnd_2827532 < baseStart_2827532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827569 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 2, 2, 3]
def baseStart_2827569 : Nat := 118140960795 + 2827569 * 2 ^ 59
def prefixEnd_2827569 : Nat := 4983230072969 + 3 ^ 40 * 2827569 * 2
def baseEnd_2827569 : Nat := 1451901980752952856983753

theorem tailTrace_2827569 : CollatzResearch.WordTrace tailWord_2827569 prefixEnd_2827569 1451901980752952856983753 := by
  unfold tailWord_2827569
  simp only [CollatzResearch.WordTrace]
  refine ⟨103129913893207898183853761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68753275928805265455902507 103129913893207898183853761)
  ·
    refine ⟨77347435419905923637890321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103129913893207898183853761 77347435419905923637890321)
    ·
      refine ⟨58010576564929442728417741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77347435419905923637890321 58010576564929442728417741)
      ·
        refine ⟨21753966211848541023156653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58010576564929442728417741 21753966211848541023156653)
        ·
          refine ⟨8157737329443202883683745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21753966211848541023156653 8157737329443202883683745)
          ·
            refine ⟨6118302997082402162762809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8157737329443202883683745 6118302997082402162762809)
            ·
              refine ⟨4588727247811801622072107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6118302997082402162762809 4588727247811801622072107)
              ·
                refine ⟨6883090871717702433108161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4588727247811801622072107 6883090871717702433108161)
                ·
                  refine ⟨5162318153788276824831121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6883090871717702433108161 5162318153788276824831121)
                  ·
                    refine ⟨3871738615341207618623341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5162318153788276824831121 3871738615341207618623341)
                    ·
                      refine ⟨1451901980752952856983753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3871738615341207618623341 1451901980752952856983753)
                      ·
                        rfl

theorem cell23_2827569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_2827569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827569 prefixEnd_2827569 := by exact prefixLift 2827569
  have htrace : WordTrace (prefixWord ++ tailWord_2827569) baseStart_2827569 baseEnd_2827569 := by
    simpa [prefixWord, tailWord_2827569, baseEnd_2827569] using wordTrace_append hprefix tailTrace_2827569
  have hstable : (prefixWord ++ tailWord_2827569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827569).length < 2 ^ (prefixWord ++ tailWord_2827569).sum := by decide
  have hdescent : baseEnd_2827569 < baseStart_2827569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827592 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 3, 5, 2]
def baseStart_2827592 : Nat := 118140960795 + 2827592 * 2 ^ 59
def prefixEnd_2827592 : Nat := 4983230072969 + 3 ^ 40 * 2827592 * 2
def baseEnd_2827592 : Nat := 1451913790808006266996147

theorem tailTrace_2827592 : CollatzResearch.WordTrace tailWord_2827592 prefixEnd_2827592 1451913790808006266996147 := by
  unfold tailWord_2827592
  simp only [CollatzResearch.WordTrace]
  refine ⟨51565376386062286555970515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68753835181416382074627353 51565376386062286555970515)
  ·
    refine ⟨77348064579093429833955773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51565376386062286555970515 77348064579093429833955773)
    ·
      refine ⟨29005524217160036187733415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77348064579093429833955773 29005524217160036187733415)
      ·
        refine ⟨43508286325740054281600123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29005524217160036187733415 43508286325740054281600123)
        ·
          refine ⟨65262429488610081422400185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43508286325740054281600123 65262429488610081422400185)
          ·
            refine ⟨48946822116457561066800139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65262429488610081422400185 48946822116457561066800139)
            ·
              refine ⟨73420233174686341600200209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48946822116457561066800139 73420233174686341600200209)
              ·
                refine ⟨55065174881014756200150157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73420233174686341600200209 55065174881014756200150157)
                ·
                  refine ⟨20649440580380533575056309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55065174881014756200150157 20649440580380533575056309)
                  ·
                    refine ⟨1935885054410675022661529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20649440580380533575056309 1935885054410675022661529)
                    ·
                      refine ⟨1451913790808006266996147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935885054410675022661529 1451913790808006266996147)
                      ·
                        rfl

theorem cell23_2827592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_2827592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827592 prefixEnd_2827592 := by exact prefixLift 2827592
  have htrace : WordTrace (prefixWord ++ tailWord_2827592) baseStart_2827592 baseEnd_2827592 := by
    simpa [prefixWord, tailWord_2827592, baseEnd_2827592] using wordTrace_append hprefix tailTrace_2827592
  have hstable : (prefixWord ++ tailWord_2827592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827592).length < 2 ^ (prefixWord ++ tailWord_2827592).sum := by decide
  have hdescent : baseEnd_2827592 < baseStart_2827592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827625 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 5, 1, 5]
def baseStart_2827625 : Nat := 118140960795 + 2827625 * 2 ^ 59
def prefixEnd_2827625 : Nat := 4983230072969 + 3 ^ 40 * 2827625 * 2
def baseEnd_2827625 : Nat := 1451930735669604637883495

theorem tailTrace_2827625 : CollatzResearch.WordTrace tailWord_2827625 prefixEnd_2827625 1451930735669604637883495 := by
  unfold tailWord_2827625
  simp only [CollatzResearch.WordTrace]
  refine ⟨103131956381005019747892329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68754637587336679831928219 103131956381005019747892329)
  ·
    refine ⟨77348967285753764810919247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103131956381005019747892329 77348967285753764810919247)
    ·
      refine ⟨116023450928630647216378871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77348967285753764810919247 116023450928630647216378871)
      ·
        refine ⟨174035176392945970824568307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116023450928630647216378871 174035176392945970824568307)
        ·
          refine ⟨261052764589418956236852461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174035176392945970824568307 261052764589418956236852461)
          ·
            refine ⟨97894786721032108588819673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261052764589418956236852461 97894786721032108588819673)
            ·
              refine ⟨73421090040774081441614755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97894786721032108588819673 73421090040774081441614755)
              ·
                refine ⟨110131635061161122162422133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73421090040774081441614755 110131635061161122162422133)
                ·
                  refine ⟨10324840786983855202727075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110131635061161122162422133 10324840786983855202727075)
                  ·
                    refine ⟨15487261180475782804090613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10324840786983855202727075 15487261180475782804090613)
                    ·
                      refine ⟨1451930735669604637883495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15487261180475782804090613 1451930735669604637883495)
                      ·
                        rfl

theorem cell23_2827625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_2827625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827625 prefixEnd_2827625 := by exact prefixLift 2827625
  have htrace : WordTrace (prefixWord ++ tailWord_2827625) baseStart_2827625 baseEnd_2827625 := by
    simpa [prefixWord, tailWord_2827625, baseEnd_2827625] using wordTrace_append hprefix tailTrace_2827625
  have hstable : (prefixWord ++ tailWord_2827625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827625).length < 2 ^ (prefixWord ++ tailWord_2827625).sum := by decide
  have hdescent : baseEnd_2827625 < baseStart_2827625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827626 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 1, 5, 2]
def baseStart_2827626 : Nat := 118140960795 + 2827626 * 2 ^ 59
def prefixEnd_2827626 : Nat := 4983230072969 + 3 ^ 40 * 2827626 * 2
def baseEnd_2827626 : Nat := 1451931249150259133970991

theorem tailTrace_2827626 : CollatzResearch.WordTrace tailWord_2827626 prefixEnd_2827626 1451931249150259133970991 := by
  unfold tailWord_2827626
  simp only [CollatzResearch.WordTrace]
  refine ⟨25782998213500349229669683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68754661902667597945785821 25782998213500349229669683)
  ·
    refine ⟨38674497320250523844504525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25782998213500349229669683 38674497320250523844504525)
    ·
      refine ⟨14502936495093946441689197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38674497320250523844504525 14502936495093946441689197)
      ·
        refine ⟨5438601185660229915633449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14502936495093946441689197 5438601185660229915633449)
        ·
          refine ⟨4078950889245172436725087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5438601185660229915633449 4078950889245172436725087)
          ·
            refine ⟨6118426333867758655087631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4078950889245172436725087 6118426333867758655087631)
            ·
              refine ⟨9177639500801637982631447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6118426333867758655087631 9177639500801637982631447)
              ·
                refine ⟨13766459251202456973947171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9177639500801637982631447 13766459251202456973947171)
                ·
                  refine ⟨20649688876803685460920757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13766459251202456973947171 20649688876803685460920757)
                  ·
                    refine ⟨1935908332200345511961321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20649688876803685460920757 1935908332200345511961321)
                    ·
                      refine ⟨1451931249150259133970991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935908332200345511961321 1451931249150259133970991)
                      ·
                        rfl

theorem cell23_2827626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_2827626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827626 prefixEnd_2827626 := by exact prefixLift 2827626
  have htrace : WordTrace (prefixWord ++ tailWord_2827626) baseStart_2827626 baseEnd_2827626 := by
    simpa [prefixWord, tailWord_2827626, baseEnd_2827626] using wordTrace_append hprefix tailTrace_2827626
  have hstable : (prefixWord ++ tailWord_2827626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827626).length < 2 ^ (prefixWord ++ tailWord_2827626).sum := by decide
  have hdescent : baseEnd_2827626 < baseStart_2827626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827632 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 4, 4]
def baseStart_2827632 : Nat := 118140960795 + 2827632 * 2 ^ 59
def prefixEnd_2827632 : Nat := 4983230072969 + 3 ^ 40 * 2827632 * 2
def baseEnd_2827632 : Nat := 483978110011395370165321

theorem tailTrace_2827632 : CollatzResearch.WordTrace tailWord_2827632 prefixEnd_2827632 483978110011395370165321 := by
  unfold tailWord_2827632
  simp only [CollatzResearch.WordTrace]
  refine ⟨51566105845989829971698575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68754807794653106628931433 51566105845989829971698575)
  ·
    refine ⟨77349158768984744957547863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51566105845989829971698575 77349158768984744957547863)
    ·
      refine ⟨116023738153477117436321795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77349158768984744957547863 116023738153477117436321795)
      ·
        refine ⟨174035607230215676154482693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116023738153477117436321795 174035607230215676154482693)
        ·
          refine ⟨32631676355665439278965505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174035607230215676154482693 32631676355665439278965505)
          ·
            refine ⟨24473757266749079459224129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32631676355665439278965505 24473757266749079459224129)
            ·
              refine ⟨18355317950061809594418097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24473757266749079459224129 18355317950061809594418097)
              ·
                refine ⟨13766488462546357195813573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18355317950061809594418097 13766488462546357195813573)
                ·
                  refine ⟨2581216586727441974215045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13766488462546357195813573 2581216586727441974215045)
                  ·
                    refine ⟨483978110011395370165321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2581216586727441974215045 483978110011395370165321)
                    ·
                      rfl

theorem cell23_2827632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 4, 4].length) (baseStart_2827632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827632 prefixEnd_2827632 := by exact prefixLift 2827632
  have htrace : WordTrace (prefixWord ++ tailWord_2827632) baseStart_2827632 baseEnd_2827632 := by
    simpa [prefixWord, tailWord_2827632, baseEnd_2827632] using wordTrace_append hprefix tailTrace_2827632
  have hstable : (prefixWord ++ tailWord_2827632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827632).length < 2 ^ (prefixWord ++ tailWord_2827632).sum := by decide
  have hdescent : baseEnd_2827632 < baseStart_2827632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827639 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 5, 2, 2]
def baseStart_2827639 : Nat := 118140960795 + 2827639 * 2 ^ 59
def prefixEnd_2827639 : Nat := 4983230072969 + 3 ^ 40 * 2827639 * 2
def baseEnd_2827639 : Nat := 1451937924398767583108431

theorem tailTrace_2827639 : CollatzResearch.WordTrace tailWord_2827639 prefixEnd_2827639 1451937924398767583108431 := by
  unfold tailWord_2827639
  simp only [CollatzResearch.WordTrace]
  refine ⟨103132467002954300138901971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68754978001969533425934647 103132467002954300138901971)
  ·
    refine ⟨154698700504431450208352957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103132467002954300138901971 154698700504431450208352957)
    ·
      refine ⟨58012012689161793828132359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154698700504431450208352957 58012012689161793828132359)
      ·
        refine ⟨87018019033742690742198539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58012012689161793828132359 87018019033742690742198539)
        ·
          refine ⟨130527028550614036113297809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87018019033742690742198539 130527028550614036113297809)
          ·
            refine ⟨97895271412960527084973357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130527028550614036113297809 97895271412960527084973357)
            ·
              refine ⟨36710726779860197656865009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97895271412960527084973357 36710726779860197656865009)
              ·
                refine ⟨27533045084895148242648757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36710726779860197656865009 27533045084895148242648757)
                ·
                  refine ⟨2581222976708920147748321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27533045084895148242648757 2581222976708920147748321)
                  ·
                    refine ⟨1935917232531690110811241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2581222976708920147748321 1935917232531690110811241)
                    ·
                      refine ⟨1451937924398767583108431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935917232531690110811241 1451937924398767583108431)
                      ·
                        rfl

theorem cell23_2827639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 2, 2].length) (baseStart_2827639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827639 prefixEnd_2827639 := by exact prefixLift 2827639
  have htrace : WordTrace (prefixWord ++ tailWord_2827639) baseStart_2827639 baseEnd_2827639 := by
    simpa [prefixWord, tailWord_2827639, baseEnd_2827639] using wordTrace_append hprefix tailTrace_2827639
  have hstable : (prefixWord ++ tailWord_2827639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827639).length < 2 ^ (prefixWord ++ tailWord_2827639).sum := by decide
  have hdescent : baseEnd_2827639 < baseStart_2827639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827645 : List Nat := [1, 4, 1, 1, 2, 2, 12]
def baseStart_2827645 : Nat := 118140960795 + 2827645 * 2 ^ 59
def prefixEnd_2827645 : Nat := 4983230072969 + 3 ^ 40 * 2827645 * 2
def baseEnd_2827645 : Nat := 17925197596082648884363

theorem tailTrace_2827645 : CollatzResearch.WordTrace tailWord_2827645 prefixEnd_2827645 17925197596082648884363 := by
  unfold tailWord_2827645
  simp only [CollatzResearch.WordTrace]
  refine ⟨103132685840932563163620389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68755123893955042109080259 103132685840932563163620389)
  ·
    refine ⟨19337378595174855593178823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103132685840932563163620389 19337378595174855593178823)
    ·
      refine ⟨29006067892762283389768235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19337378595174855593178823 29006067892762283389768235)
      ·
        refine ⟨43509101839143425084652353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29006067892762283389768235 43509101839143425084652353)
        ·
          refine ⟨32631826379357568813489265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43509101839143425084652353 32631826379357568813489265)
          ·
            refine ⟨24473869784518176610116949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32631826379357568813489265 24473869784518176610116949)
            ·
              refine ⟨17925197596082648884363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 24473869784518176610116949 17925197596082648884363)
              ·
                rfl

theorem cell23_2827645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 12].length) (baseStart_2827645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827645 prefixEnd_2827645 := by exact prefixLift 2827645
  have htrace : WordTrace (prefixWord ++ tailWord_2827645) baseStart_2827645 baseEnd_2827645 := by
    simpa [prefixWord, tailWord_2827645, baseEnd_2827645] using wordTrace_append hprefix tailTrace_2827645
  have hstable : (prefixWord ++ tailWord_2827645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827645).length < 2 ^ (prefixWord ++ tailWord_2827645).sum := by decide
  have hdescent : baseEnd_2827645 < baseStart_2827645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827650 : List Nat := [3, 4, 2, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_2827650 : Nat := 118140960795 + 2827650 * 2 ^ 59
def prefixEnd_2827650 : Nat := 4983230072969 + 3 ^ 40 * 2827650 * 2
def baseEnd_2827650 : Nat := 1451943572685967040070881

theorem tailTrace_2827650 : CollatzResearch.WordTrace tailWord_2827650 prefixEnd_2827650 1451943572685967040070881 := by
  unfold tailWord_2827650
  simp only [CollatzResearch.WordTrace]
  refine ⟨25783217051478612254388101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68755245470609632678368269 25783217051478612254388101)
  ·
    refine ⟨4834353197152239797697769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25783217051478612254388101 4834353197152239797697769)
    ·
      refine ⟨3625764897864179848273327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4834353197152239797697769 3625764897864179848273327)
      ·
        refine ⟨5438647346796269772409991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3625764897864179848273327 5438647346796269772409991)
        ·
          refine ⟨8157971020194404658614987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5438647346796269772409991 8157971020194404658614987)
          ·
            refine ⟨12236956530291606987922481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8157971020194404658614987 12236956530291606987922481)
            ·
              refine ⟨9177717397718705240941861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12236956530291606987922481 9177717397718705240941861)
              ·
                refine ⟨1720822012072257232676599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9177717397718705240941861 1720822012072257232676599)
                ·
                  refine ⟨2581233018108385849014899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720822012072257232676599 2581233018108385849014899)
                  ·
                    refine ⟨3871849527162578773522349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2581233018108385849014899 3871849527162578773522349)
                    ·
                      refine ⟨1451943572685967040070881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3871849527162578773522349 1451943572685967040070881)
                      ·
                        rfl

theorem cell23_2827650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_2827650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827650 prefixEnd_2827650 := by exact prefixLift 2827650
  have htrace : WordTrace (prefixWord ++ tailWord_2827650) baseStart_2827650 baseEnd_2827650 := by
    simpa [prefixWord, tailWord_2827650, baseEnd_2827650] using wordTrace_append hprefix tailTrace_2827650
  have hstable : (prefixWord ++ tailWord_2827650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827650).length < 2 ^ (prefixWord ++ tailWord_2827650).sum := by decide
  have hdescent : baseEnd_2827650 < baseStart_2827650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827656 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 3, 2, 2]
def baseStart_2827656 : Nat := 118140960795 + 2827656 * 2 ^ 59
def prefixEnd_2827656 : Nat := 4983230072969 + 3 ^ 40 * 2827656 * 2
def baseEnd_2827656 : Nat := 1451946653569894016595853

theorem tailTrace_2827656 : CollatzResearch.WordTrace tailWord_2827656 prefixEnd_2827656 1451946653569894016595853 := by
  unfold tailWord_2827656
  simp only [CollatzResearch.WordTrace]
  refine ⟨51566543521946356021135411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68755391362595141361513881 51566543521946356021135411)
  ·
    refine ⟨77349815282919534031703117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51566543521946356021135411 77349815282919534031703117)
    ·
      refine ⟨29006180731094825261888669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77349815282919534031703117 29006180731094825261888669)
      ·
        refine ⟨10877317774160559473208251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29006180731094825261888669 10877317774160559473208251)
        ·
          refine ⟨16315976661240839209812377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10877317774160559473208251 16315976661240839209812377)
          ·
            refine ⟨12236982495930629407359283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16315976661240839209812377 12236982495930629407359283)
            ·
              refine ⟨18355473743895944111038925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12236982495930629407359283 18355473743895944111038925)
              ·
                refine ⟨6883302653960979041639597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18355473743895944111038925 6883302653960979041639597)
                ·
                  refine ⟨2581238495235367140614849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6883302653960979041639597 2581238495235367140614849)
                  ·
                    refine ⟨1935928871426525355461137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2581238495235367140614849 1935928871426525355461137)
                    ·
                      refine ⟨1451946653569894016595853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935928871426525355461137 1451946653569894016595853)
                      ·
                        rfl

theorem cell23_2827656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_2827656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827656 prefixEnd_2827656 := by exact prefixLift 2827656
  have htrace : WordTrace (prefixWord ++ tailWord_2827656) baseStart_2827656 baseEnd_2827656 := by
    simpa [prefixWord, tailWord_2827656, baseEnd_2827656] using wordTrace_append hprefix tailTrace_2827656
  have hstable : (prefixWord ++ tailWord_2827656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827656).length < 2 ^ (prefixWord ++ tailWord_2827656).sum := by decide
  have hdescent : baseEnd_2827656 < baseStart_2827656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827665 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 6]
def baseStart_2827665 : Nat := 118140960795 + 2827665 * 2 ^ 59
def prefixEnd_2827665 : Nat := 4983230072969 + 3 ^ 40 * 2827665 * 2
def baseEnd_2827665 : Nat := 1451951274895784481383311

theorem tailTrace_2827665 : CollatzResearch.WordTrace tailWord_2827665 prefixEnd_2827665 1451951274895784481383311 := by
  unfold tailWord_2827665
  simp only [CollatzResearch.WordTrace]
  refine ⟨103133415300860106579348449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68755610200573404386232299 103133415300860106579348449)
  ·
    refine ⟨77350061475645079934511337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103133415300860106579348449 77350061475645079934511337)
    ·
      refine ⟨58012546106733809950883503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77350061475645079934511337 58012546106733809950883503)
      ·
        refine ⟨87018819160100714926325255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58012546106733809950883503 87018819160100714926325255)
        ·
          refine ⟨130528228740151072389487883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87018819160100714926325255 130528228740151072389487883)
          ·
            refine ⟨195792343110226608584231825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130528228740151072389487883 195792343110226608584231825)
            ·
              refine ⟨146844257332669956438173869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195792343110226608584231825 146844257332669956438173869)
              ·
                refine ⟨55066596499751233664315201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146844257332669956438173869 55066596499751233664315201)
                ·
                  refine ⟨41299947374813425248236401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55066596499751233664315201 41299947374813425248236401)
                  ·
                    refine ⟨30974960531110068936177301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41299947374813425248236401 30974960531110068936177301)
                    ·
                      refine ⟨1451951274895784481383311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30974960531110068936177301 1451951274895784481383311)
                      ·
                        rfl

theorem cell23_2827665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_2827665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827665 prefixEnd_2827665 := by exact prefixLift 2827665
  have htrace : WordTrace (prefixWord ++ tailWord_2827665) baseStart_2827665 baseEnd_2827665 := by
    simpa [prefixWord, tailWord_2827665, baseEnd_2827665] using wordTrace_append hprefix tailTrace_2827665
  have hstable : (prefixWord ++ tailWord_2827665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827665).length < 2 ^ (prefixWord ++ tailWord_2827665).sum := by decide
  have hdescent : baseEnd_2827665 < baseStart_2827665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827679 : List Nat := [1, 1, 2, 5, 1, 4, 2, 7]
def baseStart_2827679 : Nat := 118140960795 + 2827679 * 2 ^ 59
def prefixEnd_2827679 : Nat := 4983230072969 + 3 ^ 40 * 2827679 * 2
def baseEnd_2827679 : Nat := 53776239393516571355861

theorem tailTrace_2827679 : CollatzResearch.WordTrace tailWord_2827679 prefixEnd_2827679 53776239393516571355861 := by
  unfold tailWord_2827679
  simp only [CollatzResearch.WordTrace]
  refine ⟨103133925922809386970358091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68755950615206257980238727 103133925922809386970358091)
  ·
    refine ⟨154700888884214080455537137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103133925922809386970358091 154700888884214080455537137)
    ·
      refine ⟨116025666663160560341652853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154700888884214080455537137 116025666663160560341652853)
      ·
        refine ⟨10877406249671302532029955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116025666663160560341652853 10877406249671302532029955)
        ·
          refine ⟨16316109374506953798044933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10877406249671302532029955 16316109374506953798044933)
          ·
            refine ⟨3059270507720053837133425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16316109374506953798044933 3059270507720053837133425)
            ·
              refine ⟨2294452880790040377850069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3059270507720053837133425 2294452880790040377850069)
              ·
                refine ⟨53776239393516571355861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2294452880790040377850069 53776239393516571355861)
                ·
                  rfl

theorem cell23_2827679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 7].length) (baseStart_2827679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827679 prefixEnd_2827679 := by exact prefixLift 2827679
  have htrace : WordTrace (prefixWord ++ tailWord_2827679) baseStart_2827679 baseEnd_2827679 := by
    simpa [prefixWord, tailWord_2827679, baseEnd_2827679] using wordTrace_append hprefix tailTrace_2827679
  have hstable : (prefixWord ++ tailWord_2827679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827679).length < 2 ^ (prefixWord ++ tailWord_2827679).sum := by decide
  have hdescent : baseEnd_2827679 < baseStart_2827679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827695 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 8]
def baseStart_2827695 : Nat := 118140960795 + 2827695 * 2 ^ 59
def prefixEnd_2827695 : Nat := 4983230072969 + 3 ^ 40 * 2827695 * 2
def baseEnd_2827695 : Nat := 1451966679315419364008173

theorem tailTrace_2827695 : CollatzResearch.WordTrace tailWord_2827695 prefixEnd_2827695 1451966679315419364008173 := by
  unfold tailWord_2827695
  simp only [CollatzResearch.WordTrace]
  refine ⟨103134509490751421702940539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68756339660500947801960359 103134509490751421702940539)
  ·
    refine ⟨154701764236127132554410809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103134509490751421702940539 154701764236127132554410809)
    ·
      refine ⟨116026323177095349415808107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154701764236127132554410809 116026323177095349415808107)
      ·
        refine ⟨174039484765643024123712161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116026323177095349415808107 174039484765643024123712161)
        ·
          refine ⟨130529613574232268092784121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174039484765643024123712161 130529613574232268092784121)
          ·
            refine ⟨97897210180674201069588091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130529613574232268092784121 97897210180674201069588091)
            ·
              refine ⟨146845815271011301604382137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97897210180674201069588091 146845815271011301604382137)
              ·
                refine ⟨110134361453258476203286603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146845815271011301604382137 110134361453258476203286603)
                ·
                  refine ⟨165201542179887714304929905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110134361453258476203286603 165201542179887714304929905)
                  ·
                    refine ⟨123901156634915785728697429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 165201542179887714304929905 123901156634915785728697429)
                    ·
                      refine ⟨1451966679315419364008173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 123901156634915785728697429 1451966679315419364008173)
                      ·
                        rfl

theorem cell23_2827695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_2827695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827695 prefixEnd_2827695 := by exact prefixLift 2827695
  have htrace : WordTrace (prefixWord ++ tailWord_2827695) baseStart_2827695 baseEnd_2827695 := by
    simpa [prefixWord, tailWord_2827695, baseEnd_2827695] using wordTrace_append hprefix tailTrace_2827695
  have hstable : (prefixWord ++ tailWord_2827695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827695).length < 2 ^ (prefixWord ++ tailWord_2827695).sum := by decide
  have hdescent : baseEnd_2827695 < baseStart_2827695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827749 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2827749 : Nat := 118140960795 + 2827749 * 2 ^ 59
def prefixEnd_2827749 : Nat := 4983230072969 + 3 ^ 40 * 2827749 * 2
def baseEnd_2827749 : Nat := 1451994407270762152732925

theorem tailTrace_2827749 : CollatzResearch.WordTrace tailWord_2827749 prefixEnd_2827749 1451994407270762152732925 := by
  unfold tailWord_2827749
  simp only [CollatzResearch.WordTrace]
  refine ⟨103136479032555788925406301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68757652688370525950270867 103136479032555788925406301)
  ·
    refine ⟨38676179637208420847027363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103136479032555788925406301 38676179637208420847027363)
    ·
      refine ⟨58014269455812631270541045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38676179637208420847027363 58014269455812631270541045)
      ·
        refine ⟨5438837761482434181613223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58014269455812631270541045 5438837761482434181613223)
        ·
          refine ⟨8158256642223651272419835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5438837761482434181613223 8158256642223651272419835)
          ·
            refine ⟨12237384963335476908629753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8158256642223651272419835 12237384963335476908629753)
            ·
              refine ⟨9178038722501607681472315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12237384963335476908629753 9178038722501607681472315)
              ·
                refine ⟨13767058083752411522208473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9178038722501607681472315 13767058083752411522208473)
                ·
                  refine ⟨10325293562814308641656355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13767058083752411522208473 10325293562814308641656355)
                  ·
                    refine ⟨15487940344221462962484533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10325293562814308641656355 15487940344221462962484533)
                    ·
                      refine ⟨1451994407270762152732925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15487940344221462962484533 1451994407270762152732925)
                      ·
                        rfl

theorem cell23_2827749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2827749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827749 prefixEnd_2827749 := by exact prefixLift 2827749
  have htrace : WordTrace (prefixWord ++ tailWord_2827749) baseStart_2827749 baseEnd_2827749 := by
    simpa [prefixWord, tailWord_2827749, baseEnd_2827749] using wordTrace_append hprefix tailTrace_2827749
  have hstable : (prefixWord ++ tailWord_2827749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827749).length < 2 ^ (prefixWord ++ tailWord_2827749).sum := by decide
  have hdescent : baseEnd_2827749 < baseStart_2827749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827839 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 3]
def baseStart_2827839 : Nat := 118140960795 + 2827839 * 2 ^ 59
def prefixEnd_2827839 : Nat := 4983230072969 + 3 ^ 40 * 2827839 * 2
def baseEnd_2827839 : Nat := 1452040620529666800607511

theorem tailTrace_2827839 : CollatzResearch.WordTrace tailWord_2827839 prefixEnd_2827839 1452040620529666800607511 := by
  unfold tailWord_2827839
  simp only [CollatzResearch.WordTrace]
  refine ⟨103139761602229734296182571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68759841068153156197455047 103139761602229734296182571)
  ·
    refine ⟨154709642403344601444273857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103139761602229734296182571 154709642403344601444273857)
    ·
      refine ⟨116032231802508451083205393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154709642403344601444273857 116032231802508451083205393)
      ·
        refine ⟨87024173851881338312404045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116032231802508451083205393 87024173851881338312404045)
        ·
          refine ⟨32634065194455501867151517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87024173851881338312404045 32634065194455501867151517)
          ·
            refine ⟨12237774447920813200181819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32634065194455501867151517 12237774447920813200181819)
            ·
              refine ⟨18356661671881219800272729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12237774447920813200181819 18356661671881219800272729)
              ·
                refine ⟨13767496253910914850204547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18356661671881219800272729 13767496253910914850204547)
                ·
                  refine ⟨20651244380866372275306821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13767496253910914850204547 20651244380866372275306821)
                  ·
                    refine ⟨3872108321412444801620029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20651244380866372275306821 3872108321412444801620029)
                    ·
                      refine ⟨1452040620529666800607511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3872108321412444801620029 1452040620529666800607511)
                      ·
                        rfl

theorem cell23_2827839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_2827839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827839 prefixEnd_2827839 := by exact prefixLift 2827839
  have htrace : WordTrace (prefixWord ++ tailWord_2827839) baseStart_2827839 baseEnd_2827839 := by
    simpa [prefixWord, tailWord_2827839, baseEnd_2827839] using wordTrace_append hprefix tailTrace_2827839
  have hstable : (prefixWord ++ tailWord_2827839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827839).length < 2 ^ (prefixWord ++ tailWord_2827839).sum := by decide
  have hdescent : baseEnd_2827839 < baseStart_2827839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827863 : List Nat := [1, 1, 3, 2, 2, 3, 3, 3, 1, 4]
def baseStart_2827863 : Nat := 118140960795 + 2827863 * 2 ^ 59
def prefixEnd_2827863 : Nat := 4983230072969 + 3 ^ 40 * 2827863 * 2
def baseEnd_2827863 : Nat := 484017648021791568902467

theorem tailTrace_2827863 : CollatzResearch.WordTrace tailWord_2827863 prefixEnd_2827863 484017648021791568902467 := by
  unfold tailWord_2827863
  simp only [CollatzResearch.WordTrace]
  refine ⟨103140636954142786395056243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68760424636095190930037495 103140636954142786395056243)
  ·
    refine ⟨154710955431214179592584365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103140636954142786395056243 154710955431214179592584365)
    ·
      refine ⟨58016608286705317347219137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154710955431214179592584365 58016608286705317347219137)
      ·
        refine ⟨43512456215028988010414353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58016608286705317347219137 43512456215028988010414353)
        ·
          refine ⟨32634342161271741007810765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43512456215028988010414353 32634342161271741007810765)
          ·
            refine ⟨12237878310476902877929037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32634342161271741007810765 12237878310476902877929037)
            ·
              refine ⟨4589204366428838579223389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12237878310476902877929037 4589204366428838579223389)
              ·
                refine ⟨1720951637410814467208771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4589204366428838579223389 1720951637410814467208771)
                ·
                  refine ⟨2581427456116221700813157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720951637410814467208771 2581427456116221700813157)
                  ·
                    refine ⟨484017648021791568902467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2581427456116221700813157 484017648021791568902467)
                    ·
                      rfl

theorem cell23_2827863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 1, 4].length) (baseStart_2827863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827863 prefixEnd_2827863 := by exact prefixLift 2827863
  have htrace : WordTrace (prefixWord ++ tailWord_2827863) baseStart_2827863 baseEnd_2827863 := by
    simpa [prefixWord, tailWord_2827863, baseEnd_2827863] using wordTrace_append hprefix tailTrace_2827863
  have hstable : (prefixWord ++ tailWord_2827863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827863).length < 2 ^ (prefixWord ++ tailWord_2827863).sum := by decide
  have hdescent : baseEnd_2827863 < baseStart_2827863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827893 : List Nat := [1, 3, 4, 2, 1, 1, 4, 1, 6]
def baseStart_2827893 : Nat := 118140960795 + 2827893 * 2 ^ 59
def prefixEnd_2827893 : Nat := 4983230072969 + 3 ^ 40 * 2827893 * 2
def baseEnd_2827893 : Nat := 161340927609445509925807

theorem tailTrace_2827893 : CollatzResearch.WordTrace tailWord_2827893 prefixEnd_2827893 161340927609445509925807 := by
  unfold tailWord_2827893
  simp only [CollatzResearch.WordTrace]
  refine ⟨103141731144034101518648333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68761154096022734345765555 103141731144034101518648333)
  ·
    refine ⟨38678149179012788069493125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103141731144034101518648333 38678149179012788069493125)
    ·
      refine ⟨7252152971064897763029961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38678149179012788069493125 7252152971064897763029961)
      ·
        refine ⟨5439114728298673322272471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7252152971064897763029961 5439114728298673322272471)
        ·
          refine ⟨8158672092448009983408707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5439114728298673322272471 8158672092448009983408707)
          ·
            refine ⟨12238008138672014975113061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8158672092448009983408707 12238008138672014975113061)
            ·
              refine ⟨2294626526001002807833699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12238008138672014975113061 2294626526001002807833699)
              ·
                refine ⟨3441939789001504211750549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2294626526001002807833699 3441939789001504211750549)
                ·
                  refine ⟨161340927609445509925807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3441939789001504211750549 161340927609445509925807)
                  ·
                    rfl

theorem cell23_2827893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 6].length) (baseStart_2827893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827893 prefixEnd_2827893 := by exact prefixLift 2827893
  have htrace : WordTrace (prefixWord ++ tailWord_2827893) baseStart_2827893 baseEnd_2827893 := by
    simpa [prefixWord, tailWord_2827893, baseEnd_2827893] using wordTrace_append hprefix tailTrace_2827893
  have hstable : (prefixWord ++ tailWord_2827893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827893).length < 2 ^ (prefixWord ++ tailWord_2827893).sum := by decide
  have hdescent : baseEnd_2827893 < baseStart_2827893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827929 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 1, 1, 5]
def baseStart_2827929 : Nat := 118140960795 + 2827929 * 2 ^ 59
def prefixEnd_2827929 : Nat := 4983230072969 + 3 ^ 40 * 2827929 * 2
def baseEnd_2827929 : Nat := 1452086833788571448482097

theorem tailTrace_2827929 : CollatzResearch.WordTrace tailWord_2827929 prefixEnd_2827929 1452086833788571448482097 := by
  unfold tailWord_2827929
  simp only [CollatzResearch.WordTrace]
  refine ⟨103143044171903679666958841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68762029447935786444639227 103143044171903679666958841)
  ·
    refine ⟨77357283128927759750219131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103143044171903679666958841 77357283128927759750219131)
    ·
      refine ⟨116035924693391639625328697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77357283128927759750219131 116035924693391639625328697)
      ·
        refine ⟨87026943520043729718996523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116035924693391639625328697 87026943520043729718996523)
        ·
          refine ⟨130540415280065594578494785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87026943520043729718996523 130540415280065594578494785)
          ·
            refine ⟨97905311460049195933871089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130540415280065594578494785 97905311460049195933871089)
            ·
              refine ⟨73428983595036896950403317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97905311460049195933871089 73428983595036896950403317)
              ·
                refine ⟨6883967212034709089100311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73428983595036896950403317 6883967212034709089100311)
                ·
                  refine ⟨10325950818052063633650467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6883967212034709089100311 10325950818052063633650467)
                  ·
                    refine ⟨15488926227078095450475701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10325950818052063633650467 15488926227078095450475701)
                    ·
                      refine ⟨1452086833788571448482097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15488926227078095450475701 1452086833788571448482097)
                      ·
                        rfl

theorem cell23_2827929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_2827929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827929 prefixEnd_2827929 := by exact prefixLift 2827929
  have htrace : WordTrace (prefixWord ++ tailWord_2827929) baseStart_2827929 baseEnd_2827929 := by
    simpa [prefixWord, tailWord_2827929, baseEnd_2827929] using wordTrace_append hprefix tailTrace_2827929
  have hstable : (prefixWord ++ tailWord_2827929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827929).length < 2 ^ (prefixWord ++ tailWord_2827929).sum := by decide
  have hdescent : baseEnd_2827929 < baseStart_2827929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827937 : List Nat := [1, 2, 3, 3, 2, 1, 4, 2, 1, 1, 3]
def baseStart_2827937 : Nat := 118140960795 + 2827937 * 2 ^ 59
def prefixEnd_2827937 : Nat := 4983230072969 + 3 ^ 40 * 2827937 * 2
def baseEnd_2827937 : Nat := 1452090941633807417182061

theorem tailTrace_2827937 : CollatzResearch.WordTrace tailWord_2827937 prefixEnd_2827937 1452090941633807417182061 := by
  unfold tailWord_2827937
  simp only [CollatzResearch.WordTrace]
  refine ⟨103143335955874697033250065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68762223970583131355500043 103143335955874697033250065)
  ·
    refine ⟨77357501966906022774937549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103143335955874697033250065 77357501966906022774937549)
    ·
      refine ⟨29009063237589758540601581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77357501966906022774937549 29009063237589758540601581)
      ·
        refine ⟨10878398714096159452725593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29009063237589758540601581 10878398714096159452725593)
        ·
          refine ⟨8158799035572119589544195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10878398714096159452725593 8158799035572119589544195)
          ·
            refine ⟨12238198553358179384316293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8158799035572119589544195 12238198553358179384316293)
            ·
              refine ⟨2294662228754658634559305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12238198553358179384316293 2294662228754658634559305)
              ·
                refine ⟨1720996671565993975919479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2294662228754658634559305 1720996671565993975919479)
                ·
                  refine ⟨2581495007348990963879219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720996671565993975919479 2581495007348990963879219)
                  ·
                    refine ⟨3872242511023486445818829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2581495007348990963879219 3872242511023486445818829)
                    ·
                      refine ⟨1452090941633807417182061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3872242511023486445818829 1452090941633807417182061)
                      ·
                        rfl

theorem cell23_2827937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_2827937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827937 prefixEnd_2827937 := by exact prefixLift 2827937
  have htrace : WordTrace (prefixWord ++ tailWord_2827937) baseStart_2827937 baseEnd_2827937 := by
    simpa [prefixWord, tailWord_2827937, baseEnd_2827937] using wordTrace_append hprefix tailTrace_2827937
  have hstable : (prefixWord ++ tailWord_2827937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827937).length < 2 ^ (prefixWord ++ tailWord_2827937).sum := by decide
  have hdescent : baseEnd_2827937 < baseStart_2827937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827939 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 4]
def baseStart_2827939 : Nat := 118140960795 + 2827939 * 2 ^ 59
def prefixEnd_2827939 : Nat := 4983230072969 + 3 ^ 40 * 2827939 * 2
def baseEnd_2827939 : Nat := 1452091968595116409357051

theorem tailTrace_2827939 : CollatzResearch.WordTrace tailWord_2827939 prefixEnd_2827939 1452091968595116409357051 := by
  unfold tailWord_2827939
  simp only [CollatzResearch.WordTrace]
  refine ⟨103143408901867451374822871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68762272601244967583215247 103143408901867451374822871)
  ·
    refine ⟨154715113352801177062234307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103143408901867451374822871 154715113352801177062234307)
    ·
      refine ⟨232072670029201765593351461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154715113352801177062234307 232072670029201765593351461)
      ·
        refine ⟨43513625630475331048753399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232072670029201765593351461 43513625630475331048753399)
        ·
          refine ⟨65270438445712996573130099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43513625630475331048753399 65270438445712996573130099)
          ·
            refine ⟨97905657668569494859695149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65270438445712996573130099 97905657668569494859695149)
            ·
              refine ⟨36714621625713560572385681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97905657668569494859695149 36714621625713560572385681)
              ·
                refine ⟨27535966219285170429289261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36714621625713560572385681 27535966219285170429289261)
                ·
                  refine ⟨10325987332231938910983473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27535966219285170429289261 10325987332231938910983473)
                  ·
                    refine ⟨7744490499173954183237605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10325987332231938910983473 7744490499173954183237605)
                    ·
                      refine ⟨1452091968595116409357051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7744490499173954183237605 1452091968595116409357051)
                      ·
                        rfl

theorem cell23_2827939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_2827939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827939 prefixEnd_2827939 := by exact prefixLift 2827939
  have htrace : WordTrace (prefixWord ++ tailWord_2827939) baseStart_2827939 baseEnd_2827939 := by
    simpa [prefixWord, tailWord_2827939, baseEnd_2827939] using wordTrace_append hprefix tailTrace_2827939
  have hstable : (prefixWord ++ tailWord_2827939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827939).length < 2 ^ (prefixWord ++ tailWord_2827939).sum := by decide
  have hdescent : baseEnd_2827939 < baseStart_2827939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827974 : List Nat := [6, 1, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_2827974 : Nat := 118140960795 + 2827974 * 2 ^ 59
def prefixEnd_2827974 : Nat := 4983230072969 + 3 ^ 40 * 2827974 * 2
def baseEnd_2827974 : Nat := 484036646806007924139797

theorem tailTrace_2827974 : CollatzResearch.WordTrace tailWord_2827974 prefixEnd_2827974 484036646806007924139797 := by
  unfold tailWord_2827974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3223271420523145386010843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68763123637827101568231317 3223271420523145386010843)
  ·
    refine ⟨4834907130784718079016265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3223271420523145386010843 4834907130784718079016265)
    ·
      refine ⟨3626180348088538559262199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4834907130784718079016265 3626180348088538559262199)
      ·
        refine ⟨5439270522132807838893299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3626180348088538559262199 5439270522132807838893299)
        ·
          refine ⟨8158905783199211758339949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5439270522132807838893299 8158905783199211758339949)
          ·
            refine ⟨3059589668699704409377481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8158905783199211758339949 3059589668699704409377481)
            ·
              refine ⟨2294692251524778307033111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3059589668699704409377481 2294692251524778307033111)
              ·
                refine ⟨3442038377287167460549667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2294692251524778307033111 3442038377287167460549667)
                ·
                  refine ⟨5163057565930751190824501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3442038377287167460549667 5163057565930751190824501)
                  ·
                    refine ⟨484036646806007924139797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5163057565930751190824501 484036646806007924139797)
                    ·
                      rfl

theorem cell23_2827974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_2827974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827974 prefixEnd_2827974 := by exact prefixLift 2827974
  have htrace : WordTrace (prefixWord ++ tailWord_2827974) baseStart_2827974 baseEnd_2827974 := by
    simpa [prefixWord, tailWord_2827974, baseEnd_2827974] using wordTrace_append hprefix tailTrace_2827974
  have hstable : (prefixWord ++ tailWord_2827974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827974).length < 2 ^ (prefixWord ++ tailWord_2827974).sum := by decide
  have hdescent : baseEnd_2827974 < baseStart_2827974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827976 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 1, 3, 3]
def baseStart_2827976 : Nat := 118140960795 + 2827976 * 2 ^ 59
def prefixEnd_2827976 : Nat := 4983230072969 + 3 ^ 40 * 2827976 * 2
def baseEnd_2827976 : Nat := 1452110967379332764594381

theorem tailTrace_2827976 : CollatzResearch.WordTrace tailWord_2827976 prefixEnd_2827976 1452110967379332764594381 := by
  unfold tailWord_2827976
  simp only [CollatzResearch.WordTrace]
  refine ⟨51572379201366703346959891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68763172268488937795946521 51572379201366703346959891)
  ·
    refine ⟨77358568802050055020439837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51572379201366703346959891 77358568802050055020439837)
    ·
      refine ⟨29009463300768770632664939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77358568802050055020439837 29009463300768770632664939)
      ·
        refine ⟨43514194951153155948997409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29009463300768770632664939 43514194951153155948997409)
        ·
          refine ⟨32635646213364866961748057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43514194951153155948997409 32635646213364866961748057)
          ·
            refine ⟨24476734660023650221311043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32635646213364866961748057 24476734660023650221311043)
            ·
              refine ⟨36715101990035475331966565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24476734660023650221311043 36715101990035475331966565)
              ·
                refine ⟨6884081623131651624743731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36715101990035475331966565 6884081623131651624743731)
                ·
                  refine ⟨10326122434697477437115597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6884081623131651624743731 10326122434697477437115597)
                  ·
                    refine ⟨3872295913011554038918349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10326122434697477437115597 3872295913011554038918349)
                    ·
                      refine ⟨1452110967379332764594381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3872295913011554038918349 1452110967379332764594381)
                      ·
                        rfl

theorem cell23_2827976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_2827976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827976 prefixEnd_2827976 := by exact prefixLift 2827976
  have htrace : WordTrace (prefixWord ++ tailWord_2827976) baseStart_2827976 baseEnd_2827976 := by
    simpa [prefixWord, tailWord_2827976, baseEnd_2827976] using wordTrace_append hprefix tailTrace_2827976
  have hstable : (prefixWord ++ tailWord_2827976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827976).length < 2 ^ (prefixWord ++ tailWord_2827976).sum := by decide
  have hdescent : baseEnd_2827976 < baseStart_2827976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827980 : List Nat := [2, 2, 1, 5, 2, 1, 1, 3, 1, 2, 3]
def baseStart_2827980 : Nat := 118140960795 + 2827980 * 2 ^ 59
def prefixEnd_2827980 : Nat := 4983230072969 + 3 ^ 40 * 2827980 * 2
def baseEnd_2827980 : Nat := 1452113021301950748944363

theorem tailTrace_2827980 : CollatzResearch.WordTrace tailWord_2827980 prefixEnd_2827980 1452113021301950748944363 := by
  unfold tailWord_2827980
  simp only [CollatzResearch.WordTrace]
  refine ⟨51572452147359457688532697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68763269529812610251376929 51572452147359457688532697)
  ·
    refine ⟨38679339110519593266399523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51572452147359457688532697 38679339110519593266399523)
    ·
      refine ⟨58019008665779389899599285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38679339110519593266399523 58019008665779389899599285)
      ·
        refine ⟨5439282062416817803087433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58019008665779389899599285 5439282062416817803087433)
        ·
          refine ⟨4079461546812613352315575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5439282062416817803087433 4079461546812613352315575)
          ·
            refine ⟨6119192320218920028473363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4079461546812613352315575 6119192320218920028473363)
            ·
              refine ⟨9178788480328380042710045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6119192320218920028473363 9178788480328380042710045)
              ·
                refine ⟨3442045680123142516016267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9178788480328380042710045 3442045680123142516016267)
                ·
                  refine ⟨5163068520184713774024401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3442045680123142516016267 5163068520184713774024401)
                  ·
                    refine ⟨3872301390138535330518301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5163068520184713774024401 3872301390138535330518301)
                    ·
                      refine ⟨1452113021301950748944363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3872301390138535330518301 1452113021301950748944363)
                      ·
                        rfl

theorem cell23_2827980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_2827980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827980 prefixEnd_2827980 := by exact prefixLift 2827980
  have htrace : WordTrace (prefixWord ++ tailWord_2827980) baseStart_2827980 baseEnd_2827980 := by
    simpa [prefixWord, tailWord_2827980, baseEnd_2827980] using wordTrace_append hprefix tailTrace_2827980
  have hstable : (prefixWord ++ tailWord_2827980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827980).length < 2 ^ (prefixWord ++ tailWord_2827980).sum := by decide
  have hdescent : baseEnd_2827980 < baseStart_2827980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827993 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 4, 1, 3]
def baseStart_2827993 : Nat := 118140960795 + 2827993 * 2 ^ 59
def prefixEnd_2827993 : Nat := 4983230072969 + 3 ^ 40 * 2827993 * 2
def baseEnd_2827993 : Nat := 1452119696550459198081803

theorem tailTrace_2827993 : CollatzResearch.WordTrace tailWord_2827993 prefixEnd_2827993 1452119696550459198081803 := by
  unfold tailWord_2827993
  simp only [CollatzResearch.WordTrace]
  refine ⟨103145378443671818597288633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68763585629114545731525755 103145378443671818597288633)
  ·
    refine ⟨77359033832753863947966475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103145378443671818597288633 77359033832753863947966475)
    ·
      refine ⟨116038550749130795921949713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77359033832753863947966475 116038550749130795921949713)
      ·
        refine ⟨87028913061848096941462285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116038550749130795921949713 87028913061848096941462285)
        ·
          refine ⟨32635842398193036353048357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87028913061848096941462285 32635842398193036353048357)
          ·
            refine ⟨6119220449661194316196567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32635842398193036353048357 6119220449661194316196567)
            ·
              refine ⟨9178830674491791474294851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6119220449661194316196567 9178830674491791474294851)
              ·
                refine ⟨13768246011737687211442277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9178830674491791474294851 13768246011737687211442277)
                ·
                  refine ⟨2581546127200816352145427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13768246011737687211442277 2581546127200816352145427)
                  ·
                    refine ⟨3872319190801224528218141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2581546127200816352145427 3872319190801224528218141)
                    ·
                      refine ⟨1452119696550459198081803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3872319190801224528218141 1452119696550459198081803)
                      ·
                        rfl

theorem cell23_2827993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_2827993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2827993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2827993 prefixEnd_2827993 := by exact prefixLift 2827993
  have htrace : WordTrace (prefixWord ++ tailWord_2827993) baseStart_2827993 baseEnd_2827993 := by
    simpa [prefixWord, tailWord_2827993, baseEnd_2827993] using wordTrace_append hprefix tailTrace_2827993
  have hstable : (prefixWord ++ tailWord_2827993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827993).length < 2 ^ (prefixWord ++ tailWord_2827993).sum := by decide
  have hdescent : baseEnd_2827993 < baseStart_2827993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828007 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 1, 2, 4]
def baseStart_2828007 : Nat := 118140960795 + 2828007 * 2 ^ 59
def prefixEnd_2828007 : Nat := 4983230072969 + 3 ^ 40 * 2828007 * 2
def baseEnd_2828007 : Nat := 1452126885279622143306739

theorem tailTrace_2828007 : CollatzResearch.WordTrace tailWord_2828007 prefixEnd_2828007 1452126885279622143306739 := by
  unfold tailWord_2828007
  simp only [CollatzResearch.WordTrace]
  refine ⟨103145889065621098988298275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68763926043747399325532183 103145889065621098988298275)
  ·
    refine ⟨154718833598431648482447413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103145889065621098988298275 154718833598431648482447413)
    ·
      refine ⟨14504890649852967045229445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154718833598431648482447413 14504890649852967045229445)
      ·
        refine ⟨2719666996847431320980521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14504890649852967045229445 2719666996847431320980521)
        ·
          refine ⟨2039750247635573490735391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2719666996847431320980521 2039750247635573490735391)
          ·
            refine ⟨3059625371453360236103087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2039750247635573490735391 3059625371453360236103087)
            ·
              refine ⟨4589438057180040354154631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3059625371453360236103087 4589438057180040354154631)
              ·
                refine ⟨6884157085770060531231947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4589438057180040354154631 6884157085770060531231947)
                ·
                  refine ⟨10326235628655090796847921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6884157085770060531231947 10326235628655090796847921)
                  ·
                    refine ⟨7744676721491318097635941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10326235628655090796847921 7744676721491318097635941)
                    ·
                      refine ⟨1452126885279622143306739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7744676721491318097635941 1452126885279622143306739)
                      ·
                        rfl

theorem cell23_2828007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_2828007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828007 prefixEnd_2828007 := by exact prefixLift 2828007
  have htrace : WordTrace (prefixWord ++ tailWord_2828007) baseStart_2828007 baseEnd_2828007 := by
    simpa [prefixWord, tailWord_2828007, baseEnd_2828007] using wordTrace_append hprefix tailTrace_2828007
  have hstable : (prefixWord ++ tailWord_2828007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828007).length < 2 ^ (prefixWord ++ tailWord_2828007).sum := by decide
  have hdescent : baseEnd_2828007 < baseStart_2828007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828033 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 1, 4, 2]
def baseStart_2828033 : Nat := 118140960795 + 2828033 * 2 ^ 59
def prefixEnd_2828033 : Nat := 4983230072969 + 3 ^ 40 * 2828033 * 2
def baseEnd_2828033 : Nat := 1452140235776639041581619

theorem tailTrace_2828033 : CollatzResearch.WordTrace tailWord_2828033 prefixEnd_2828033 1452140235776639041581619 := by
  unfold tailWord_2828033
  simp only [CollatzResearch.WordTrace]
  refine ⟨103146837363526905428744753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68764558242351270285829835 103146837363526905428744753)
  ·
    refine ⟨77360128022645179071558565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103146837363526905428744753 77360128022645179071558565)
    ·
      refine ⟨14505024004245971075917231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77360128022645179071558565 14505024004245971075917231)
      ·
        refine ⟨21757536006368956613875847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14505024004245971075917231 21757536006368956613875847)
        ·
          refine ⟨32636304009553434920813771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21757536006368956613875847 32636304009553434920813771)
          ·
            refine ⟨48954456014330152381220657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32636304009553434920813771 48954456014330152381220657)
            ·
              refine ⟨36715842010747614285915493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48954456014330152381220657 36715842010747614285915493)
              ·
                refine ⟨6884220377015177678609155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36715842010747614285915493 6884220377015177678609155)
                ·
                  refine ⟨10326330565522766517913733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6884220377015177678609155 10326330565522766517913733)
                  ·
                    refine ⟨1936186981035518722108825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10326330565522766517913733 1936186981035518722108825)
                    ·
                      refine ⟨1452140235776639041581619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1936186981035518722108825 1452140235776639041581619)
                      ·
                        rfl

theorem cell23_2828033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_2828033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828033 prefixEnd_2828033 := by exact prefixLift 2828033
  have htrace : WordTrace (prefixWord ++ tailWord_2828033) baseStart_2828033 baseEnd_2828033 := by
    simpa [prefixWord, tailWord_2828033, baseEnd_2828033] using wordTrace_append hprefix tailTrace_2828033
  have hstable : (prefixWord ++ tailWord_2828033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828033).length < 2 ^ (prefixWord ++ tailWord_2828033).sum := by decide
  have hdescent : baseEnd_2828033 < baseStart_2828033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828036 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_2828036 : Nat := 118140960795 + 2828036 * 2 ^ 59
def prefixEnd_2828036 : Nat := 4983230072969 + 3 ^ 40 * 2828036 * 2
def baseEnd_2828036 : Nat := 1452141776218602529844105

theorem tailTrace_2828036 : CollatzResearch.WordTrace tailWord_2828036 prefixEnd_2828036 1452141776218602529844105 := by
  unfold tailWord_2828036
  simp only [CollatzResearch.WordTrace]
  refine ⟨51573473391258018470551981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68764631188344024627402641 51573473391258018470551981)
  ·
    refine ⟨19340052521721756926456993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51573473391258018470551981 19340052521721756926456993)
    ·
      refine ⟨14505039391291317694842745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19340052521721756926456993 14505039391291317694842745)
      ·
        refine ⟨10878779543468488271132059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14505039391291317694842745 10878779543468488271132059)
        ·
          refine ⟨16318169315202732406698089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10878779543468488271132059 16318169315202732406698089)
          ·
            refine ⟨12238626986402049305023567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16318169315202732406698089 12238626986402049305023567)
            ·
              refine ⟨18357940479603073957535351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12238626986402049305023567 18357940479603073957535351)
              ·
                refine ⟨27536910719404610936303027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18357940479603073957535351 27536910719404610936303027)
                ·
                  refine ⟨41305366079106916404454541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27536910719404610936303027 41305366079106916404454541)
                  ·
                    refine ⟨15489512279665093651670453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41305366079106916404454541 15489512279665093651670453)
                    ·
                      refine ⟨1452141776218602529844105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15489512279665093651670453 1452141776218602529844105)
                      ·
                        rfl

theorem cell23_2828036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_2828036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828036 prefixEnd_2828036 := by exact prefixLift 2828036
  have htrace : WordTrace (prefixWord ++ tailWord_2828036) baseStart_2828036 baseEnd_2828036 := by
    simpa [prefixWord, tailWord_2828036, baseEnd_2828036] using wordTrace_append hprefix tailTrace_2828036
  have hstable : (prefixWord ++ tailWord_2828036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828036).length < 2 ^ (prefixWord ++ tailWord_2828036).sum := by decide
  have hdescent : baseEnd_2828036 < baseStart_2828036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828045 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_2828045 : Nat := 118140960795 + 2828045 * 2 ^ 59
def prefixEnd_2828045 : Nat := 4983230072969 + 3 ^ 40 * 2828045 * 2
def baseEnd_2828045 : Nat := 1452146397544492994631565

theorem tailTrace_2828045 : CollatzResearch.WordTrace tailWord_2828045 prefixEnd_2828045 1452146397544492994631565 := by
  unfold tailWord_2828045
  simp only [CollatzResearch.WordTrace]
  refine ⟨103147275039483431478181589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68764850026322287652121059 103147275039483431478181589)
  ·
    refine ⟨2417514258737892925269881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 103147275039483431478181589 2417514258737892925269881)
    ·
      refine ⟨1813135694053419693952411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2417514258737892925269881 1813135694053419693952411)
      ·
        refine ⟨2719703541080129540928617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1813135694053419693952411 2719703541080129540928617)
        ·
          refine ⟨2039777655810097155696463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2719703541080129540928617 2039777655810097155696463)
          ·
            refine ⟨3059666483715145733544695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2039777655810097155696463 3059666483715145733544695)
            ·
              refine ⟨4589499725572718600317043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3059666483715145733544695 4589499725572718600317043)
              ·
                refine ⟨6884249588359077900475565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4589499725572718600317043 6884249588359077900475565)
                ·
                  refine ⟨2581593595634654212678337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6884249588359077900475565 2581593595634654212678337)
                  ·
                    refine ⟨1936195196725990659508753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2581593595634654212678337 1936195196725990659508753)
                    ·
                      refine ⟨1452146397544492994631565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1936195196725990659508753 1452146397544492994631565)
                      ·
                        rfl

theorem cell23_2828045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_2828045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828045 prefixEnd_2828045 := by exact prefixLift 2828045
  have htrace : WordTrace (prefixWord ++ tailWord_2828045) baseStart_2828045 baseEnd_2828045 := by
    simpa [prefixWord, tailWord_2828045, baseEnd_2828045] using wordTrace_append hprefix tailTrace_2828045
  have hstable : (prefixWord ++ tailWord_2828045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828045).length < 2 ^ (prefixWord ++ tailWord_2828045).sum := by decide
  have hdescent : baseEnd_2828045 < baseStart_2828045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828046 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_2828046 : Nat := 118140960795 + 2828046 * 2 ^ 59
def prefixEnd_2828046 : Nat := 4983230072969 + 3 ^ 40 * 2828046 * 2
def baseEnd_2828046 : Nat := 1452146911025147490719059

theorem tailTrace_2828046 : CollatzResearch.WordTrace tailWord_2828046 prefixEnd_2828046 1452146911025147490719059 := by
  unfold tailWord_2828046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12893413939059976081120999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68764874341653205765978661 12893413939059976081120999)
  ·
    refine ⟨19340120908589964121681499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12893413939059976081120999 19340120908589964121681499)
    ·
      refine ⟨29010181362884946182522249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19340120908589964121681499 29010181362884946182522249)
      ·
        refine ⟨21757636022163709636891687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29010181362884946182522249 21757636022163709636891687)
        ·
          refine ⟨32636454033245564455337531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21757636022163709636891687 32636454033245564455337531)
          ·
            refine ⟨48954681049868346683006297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32636454033245564455337531 48954681049868346683006297)
            ·
              refine ⟨36716010787401260012254723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48954681049868346683006297 36716010787401260012254723)
              ·
                refine ⟨55074016181101890018382085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36716010787401260012254723 55074016181101890018382085)
                ·
                  refine ⟨10326378033956604378446641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55074016181101890018382085 10326378033956604378446641)
                  ·
                    refine ⟨7744783525467453283834981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10326378033956604378446641 7744783525467453283834981)
                    ·
                      refine ⟨1452146911025147490719059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7744783525467453283834981 1452146911025147490719059)
                      ·
                        rfl

theorem cell23_2828046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_2828046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828046 prefixEnd_2828046 := by exact prefixLift 2828046
  have htrace : WordTrace (prefixWord ++ tailWord_2828046) baseStart_2828046 baseEnd_2828046 := by
    simpa [prefixWord, tailWord_2828046, baseEnd_2828046] using wordTrace_append hprefix tailTrace_2828046
  have hstable : (prefixWord ++ tailWord_2828046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828046).length < 2 ^ (prefixWord ++ tailWord_2828046).sum := by decide
  have hdescent : baseEnd_2828046 < baseStart_2828046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828049 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 9]
def baseStart_2828049 : Nat := 118140960795 + 2828049 * 2 ^ 59
def prefixEnd_2828049 : Nat := 4983230072969 + 3 ^ 40 * 2828049 * 2
def baseEnd_2828049 : Nat := 1452148451467110978981545

theorem tailTrace_2828049 : CollatzResearch.WordTrace tailWord_2828049 prefixEnd_2828049 1452148451467110978981545 := by
  unfold tailWord_2828049
  simp only [CollatzResearch.WordTrace]
  refine ⟨103147420931468940161327201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68764947287645960107551467 103147420931468940161327201)
  ·
    refine ⟨77360565698601705120995401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103147420931468940161327201 77360565698601705120995401)
    ·
      refine ⟨58020424273951278840746551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77360565698601705120995401 58020424273951278840746551)
      ·
        refine ⟨87030636410926918261119827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58020424273951278840746551 87030636410926918261119827)
        ·
          refine ⟨130545954616390377391679741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87030636410926918261119827 130545954616390377391679741)
          ·
            refine ⟨48954732981146391521879903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130545954616390377391679741 48954732981146391521879903)
            ·
              refine ⟨73432099471719587282819855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48954732981146391521879903 73432099471719587282819855)
              ·
                refine ⟨110148149207579380924229783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73432099471719587282819855 110148149207579380924229783)
                ·
                  refine ⟨165222223811369071386344675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110148149207579380924229783 165222223811369071386344675)
                  ·
                    refine ⟨247833335717053607079517013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 165222223811369071386344675 247833335717053607079517013)
                    ·
                      refine ⟨1452148451467110978981545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 247833335717053607079517013 1452148451467110978981545)
                      ·
                        rfl

theorem cell23_2828049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_2828049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828049 prefixEnd_2828049 := by exact prefixLift 2828049
  have htrace : WordTrace (prefixWord ++ tailWord_2828049) baseStart_2828049 baseEnd_2828049 := by
    simpa [prefixWord, tailWord_2828049, baseEnd_2828049] using wordTrace_append hprefix tailTrace_2828049
  have hstable : (prefixWord ++ tailWord_2828049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828049).length < 2 ^ (prefixWord ++ tailWord_2828049).sum := by decide
  have hdescent : baseEnd_2828049 < baseStart_2828049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828056 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 7]
def baseStart_2828056 : Nat := 118140960795 + 2828056 * 2 ^ 59
def prefixEnd_2828056 : Nat := 4983230072969 + 3 ^ 40 * 2828056 * 2
def baseEnd_2828056 : Nat := 161350227314632494621557

theorem tailTrace_2828056 : CollatzResearch.WordTrace tailWord_2828056 prefixEnd_2828056 161350227314632494621557 := by
  unfold tailWord_2828056
  simp only [CollatzResearch.WordTrace]
  refine ⟨51573838121221790178416011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68765117494962386904554681 51573838121221790178416011)
  ·
    refine ⟨77360757181832685267624017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51573838121221790178416011 77360757181832685267624017)
    ·
      refine ⟨58020567886374513950718013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77360757181832685267624017 58020567886374513950718013)
      ·
        refine ⟨21757712957390442731519255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58020567886374513950718013 21757712957390442731519255)
        ·
          refine ⟨32636569436085664097278883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21757712957390442731519255 32636569436085664097278883)
          ·
            refine ⟨48954854154128496145918325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32636569436085664097278883 48954854154128496145918325)
            ·
              refine ⟨4589517576949546513679843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48954854154128496145918325 4589517576949546513679843)
              ·
                refine ⟨6884276365424319770519765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4589517576949546513679843 6884276365424319770519765)
                ·
                  refine ⟨161350227314632494621557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6884276365424319770519765 161350227314632494621557)
                  ·
                    rfl

theorem cell23_2828056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 7].length) (baseStart_2828056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828056 prefixEnd_2828056 := by exact prefixLift 2828056
  have htrace : WordTrace (prefixWord ++ tailWord_2828056) baseStart_2828056 baseEnd_2828056 := by
    simpa [prefixWord, tailWord_2828056, baseEnd_2828056] using wordTrace_append hprefix tailTrace_2828056
  have hstable : (prefixWord ++ tailWord_2828056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828056).length < 2 ^ (prefixWord ++ tailWord_2828056).sum := by decide
  have hdescent : baseEnd_2828056 < baseStart_2828056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828067 : List Nat := [1, 1, 1, 4, 2, 1, 6, 1, 2, 2, 2]
def baseStart_2828067 : Nat := 118140960795 + 2828067 * 2 ^ 59
def prefixEnd_2828067 : Nat := 4983230072969 + 3 ^ 40 * 2828067 * 2
def baseEnd_2828067 : Nat := 1452157694118891908556463

theorem tailTrace_2828067 : CollatzResearch.WordTrace tailWord_2828067 prefixEnd_2828067 1452157694118891908556463 := by
  unfold tailWord_2828067
  simp only [CollatzResearch.WordTrace]
  refine ⟨103148077445403729235482455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68765384963602486156988303 103148077445403729235482455)
  ·
    refine ⟨154722116168105593853223683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103148077445403729235482455 154722116168105593853223683)
    ·
      refine ⟨232083174252158390779835525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154722116168105593853223683 232083174252158390779835525)
      ·
        refine ⟨43515595172279698271219161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232083174252158390779835525 43515595172279698271219161)
        ·
          refine ⟨32636696379209773703414371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43515595172279698271219161 32636696379209773703414371)
          ·
            refine ⟨48955044568814660555121557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32636696379209773703414371 48955044568814660555121557)
            ·
              refine ⟨2294767714163187213521323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48955044568814660555121557 2294767714163187213521323)
              ·
                refine ⟨3442151571244780820281985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2294767714163187213521323 3442151571244780820281985)
                ·
                  refine ⟨2581613678433585615211489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3442151571244780820281985 2581613678433585615211489)
                  ·
                    refine ⟨1936210258825189211408617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2581613678433585615211489 1936210258825189211408617)
                    ·
                      refine ⟨1452157694118891908556463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1936210258825189211408617 1452157694118891908556463)
                      ·
                        rfl

theorem cell23_2828067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_2828067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828067 prefixEnd_2828067 := by exact prefixLift 2828067
  have htrace : WordTrace (prefixWord ++ tailWord_2828067) baseStart_2828067 baseEnd_2828067 := by
    simpa [prefixWord, tailWord_2828067, baseEnd_2828067] using wordTrace_append hprefix tailTrace_2828067
  have hstable : (prefixWord ++ tailWord_2828067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828067).length < 2 ^ (prefixWord ++ tailWord_2828067).sum := by decide
  have hdescent : baseEnd_2828067 < baseStart_2828067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828140 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 4]
def baseStart_2828140 : Nat := 118140960795 + 2828140 * 2 ^ 59
def prefixEnd_2828140 : Nat := 4983230072969 + 3 ^ 40 * 2828140 * 2
def baseEnd_2828140 : Nat := 1452195178206670122943627

theorem tailTrace_2828140 : CollatzResearch.WordTrace tailWord_2828140 prefixEnd_2828140 1452195178206670122943627 := by
  unfold tailWord_2828140
  simp only [CollatzResearch.WordTrace]
  refine ⟨51575369987069631351444937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68767159982759508468593249 51575369987069631351444937)
  ·
    refine ⟨38681527490302223513583703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51575369987069631351444937 38681527490302223513583703)
    ·
      refine ⟨58022291235453335270375555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38681527490302223513583703 58022291235453335270375555)
      ·
        refine ⟨87033436853180002905563333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58022291235453335270375555 87033436853180002905563333)
        ·
          refine ⟨16318769409971250544793125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87033436853180002905563333 16318769409971250544793125)
          ·
            refine ⟨3059769264369609477148711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16318769409971250544793125 3059769264369609477148711)
            ·
              refine ⟨4589653896554414215723067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3059769264369609477148711 4589653896554414215723067)
              ·
                refine ⟨6884480844831621323584601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4589653896554414215723067 6884480844831621323584601)
                ·
                  refine ⟨5163360633623715992688451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6884480844831621323584601 5163360633623715992688451)
                  ·
                    refine ⟨7745040950435573989032677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5163360633623715992688451 7745040950435573989032677)
                    ·
                      refine ⟨1452195178206670122943627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7745040950435573989032677 1452195178206670122943627)
                      ·
                        rfl

theorem cell23_2828140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_2828140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828140 prefixEnd_2828140 := by exact prefixLift 2828140
  have htrace : WordTrace (prefixWord ++ tailWord_2828140) baseStart_2828140 baseEnd_2828140 := by
    simpa [prefixWord, tailWord_2828140, baseEnd_2828140] using wordTrace_append hprefix tailTrace_2828140
  have hstable : (prefixWord ++ tailWord_2828140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828140).length < 2 ^ (prefixWord ++ tailWord_2828140).sum := by decide
  have hdescent : baseEnd_2828140 < baseStart_2828140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828146 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 8]
def baseStart_2828146 : Nat := 118140960795 + 2828146 * 2 ^ 59
def prefixEnd_2828146 : Nat := 4983230072969 + 3 ^ 40 * 2828146 * 2
def baseEnd_2828146 : Nat := 161355362121177455496511

theorem tailTrace_2828146 : CollatzResearch.WordTrace tailWord_2828146 prefixEnd_2828146 161355362121177455496511 := by
  unfold tailWord_2828146
  simp only [CollatzResearch.WordTrace]
  refine ⟨25787739703029381431902073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68767305874745017151738861 25787739703029381431902073)
  ·
    refine ⟨19340804777272036073926555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25787739703029381431902073 19340804777272036073926555)
    ·
      refine ⟨29011207165908054110889833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19340804777272036073926555 29011207165908054110889833)
      ·
        refine ⟨21758405374431040583167375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29011207165908054110889833 21758405374431040583167375)
        ·
          refine ⟨32637608061646560874751063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21758405374431040583167375 32637608061646560874751063)
          ·
            refine ⟨48956412092469841312126595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32637608061646560874751063 48956412092469841312126595)
            ·
              refine ⟨73434618138704761968189893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48956412092469841312126595 73434618138704761968189893)
              ·
                refine ⟨13768990901007142869035605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73434618138704761968189893 13768990901007142869035605)
                ·
                  refine ⟨161355362121177455496511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13768990901007142869035605 161355362121177455496511)
                  ·
                    rfl

theorem cell23_2828146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_2828146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828146 prefixEnd_2828146 := by exact prefixLift 2828146
  have htrace : WordTrace (prefixWord ++ tailWord_2828146) baseStart_2828146 baseEnd_2828146 := by
    simpa [prefixWord, tailWord_2828146, baseEnd_2828146] using wordTrace_append hprefix tailTrace_2828146
  have hstable : (prefixWord ++ tailWord_2828146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828146).length < 2 ^ (prefixWord ++ tailWord_2828146).sum := by decide
  have hdescent : baseEnd_2828146 < baseStart_2828146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828163 : List Nat := [1, 1, 1, 3, 4, 2, 3, 2, 6]
def baseStart_2828163 : Nat := 118140960795 + 2828163 * 2 ^ 59
def prefixEnd_2828163 : Nat := 4983230072969 + 3 ^ 40 * 2828163 * 2
def baseEnd_2828163 : Nat := 161356332029080392550669

theorem tailTrace_2828163 : CollatzResearch.WordTrace tailWord_2828163 prefixEnd_2828163 161356332029080392550669 := by
  unfold tailWord_2828163
  simp only [CollatzResearch.WordTrace]
  refine ⟨103151578853055937630977143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68767719235370625087318095 103151578853055937630977143)
  ·
    refine ⟨154727368279583906446465715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103151578853055937630977143 154727368279583906446465715)
    ·
      refine ⟨232091052419375859669698573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154727368279583906446465715 232091052419375859669698573)
      ·
        refine ⟨87034144657265947376136965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232091052419375859669698573 87034144657265947376136965)
        ·
          refine ⟨16318902123237365133025681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87034144657265947376136965 16318902123237365133025681)
          ·
            refine ⟨12239176592428023849769261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16318902123237365133025681 12239176592428023849769261)
            ·
              refine ⟨4589691222160508943663473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12239176592428023849769261 4589691222160508943663473)
              ·
                refine ⟨3442268416620381707747605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4589691222160508943663473 3442268416620381707747605)
                ·
                  refine ⟨161356332029080392550669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3442268416620381707747605 161356332029080392550669)
                  ·
                    rfl

theorem cell23_2828163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 6].length) (baseStart_2828163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828163 prefixEnd_2828163 := by exact prefixLift 2828163
  have htrace : WordTrace (prefixWord ++ tailWord_2828163) baseStart_2828163 baseEnd_2828163 := by
    simpa [prefixWord, tailWord_2828163, baseEnd_2828163] using wordTrace_append hprefix tailTrace_2828163
  have hstable : (prefixWord ++ tailWord_2828163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828163).length < 2 ^ (prefixWord ++ tailWord_2828163).sum := by decide
  have hdescent : baseEnd_2828163 < baseStart_2828163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828223 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 4, 4]
def baseStart_2828223 : Nat := 118140960795 + 2828223 * 2 ^ 59
def prefixEnd_2828223 : Nat := 4983230072969 + 3 ^ 40 * 2828223 * 2
def baseEnd_2828223 : Nat := 484079265700331099401915

theorem tailTrace_2828223 : CollatzResearch.WordTrace tailWord_2828223 prefixEnd_2828223 484079265700331099401915 := by
  unfold tailWord_2828223
  simp only [CollatzResearch.WordTrace]
  refine ⟨103153767232838567878161323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68769178155225711918774215 103153767232838567878161323)
  ·
    refine ⟨154730650849257851817241985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103153767232838567878161323 154730650849257851817241985)
    ·
      refine ⟨116047988136943388862931489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154730650849257851817241985 116047988136943388862931489)
      ·
        refine ⟨87035991102707541647198617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116047988136943388862931489 87035991102707541647198617)
        ·
          refine ⟨65276993327030656235398963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87035991102707541647198617 65276993327030656235398963)
          ·
            refine ⟨97915489990545984353098445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65276993327030656235398963 97915489990545984353098445)
            ·
              refine ⟨36718308746454744132411917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97915489990545984353098445 36718308746454744132411917)
              ·
                refine ⟨13769365779920529049654469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36718308746454744132411917 13769365779920529049654469)
                ·
                  refine ⟨2581756083735099196810213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13769365779920529049654469 2581756083735099196810213)
                  ·
                    refine ⟨484079265700331099401915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2581756083735099196810213 484079265700331099401915)
                    ·
                      rfl

theorem cell23_2828223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 4].length) (baseStart_2828223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828223 prefixEnd_2828223 := by exact prefixLift 2828223
  have htrace : WordTrace (prefixWord ++ tailWord_2828223) baseStart_2828223 baseEnd_2828223 := by
    simpa [prefixWord, tailWord_2828223, baseEnd_2828223] using wordTrace_append hprefix tailTrace_2828223
  have hstable : (prefixWord ++ tailWord_2828223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828223).length < 2 ^ (prefixWord ++ tailWord_2828223).sum := by decide
  have hdescent : baseEnd_2828223 < baseStart_2828223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828224 : List Nat := [2, 1, 1, 2, 3, 2, 5, 2, 1, 1, 3]
def baseStart_2828224 : Nat := 118140960795 + 2828224 * 2 ^ 59
def prefixEnd_2828224 : Nat := 4983230072969 + 3 ^ 40 * 2828224 * 2
def baseEnd_2828224 : Nat := 1452238310581647794293241

theorem tailTrace_2828224 : CollatzResearch.WordTrace tailWord_2828224 prefixEnd_2828224 1452238310581647794293241 := by
  unfold tailWord_2828224
  simp only [CollatzResearch.WordTrace]
  refine ⟨51576901852917472524473863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68769202470556630032631817 51576901852917472524473863)
  ·
    refine ⟨77365352779376208786710795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51576901852917472524473863 77365352779376208786710795)
    ·
      refine ⟨116048029169064313180066193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77365352779376208786710795 116048029169064313180066193)
      ·
        refine ⟨87036021876798234885049645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116048029169064313180066193 87036021876798234885049645)
        ·
          refine ⟨32638508203799338081893617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87036021876798234885049645 32638508203799338081893617)
          ·
            refine ⟨24478881152849503561420213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32638508203799338081893617 24478881152849503561420213)
            ·
              refine ⟨2294895108079640958883145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24478881152849503561420213 2294895108079640958883145)
              ·
                refine ⟨1721171331059730719162359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2294895108079640958883145 1721171331059730719162359)
                ·
                  refine ⟨2581756996589596078743539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721171331059730719162359 2581756996589596078743539)
                  ·
                    refine ⟨3872635494884394118115309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2581756996589596078743539 3872635494884394118115309)
                    ·
                      refine ⟨1452238310581647794293241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3872635494884394118115309 1452238310581647794293241)
                      ·
                        rfl

theorem cell23_2828224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 2, 1, 1, 3].length) (baseStart_2828224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828224 prefixEnd_2828224 := by exact prefixLift 2828224
  have htrace : WordTrace (prefixWord ++ tailWord_2828224) baseStart_2828224 baseEnd_2828224 := by
    simpa [prefixWord, tailWord_2828224, baseEnd_2828224] using wordTrace_append hprefix tailTrace_2828224
  have hstable : (prefixWord ++ tailWord_2828224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828224).length < 2 ^ (prefixWord ++ tailWord_2828224).sum := by decide
  have hdescent : baseEnd_2828224 < baseStart_2828224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828233 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 5, 2, 3]
def baseStart_2828233 : Nat := 118140960795 + 2828233 * 2 ^ 59
def prefixEnd_2828233 : Nat := 4983230072969 + 3 ^ 40 * 2828233 * 2
def baseEnd_2828233 : Nat := 1452242931907538259080699

theorem tailTrace_2828233 : CollatzResearch.WordTrace tailWord_2828233 prefixEnd_2828233 1452242931907538259080699 := by
  unfold tailWord_2828233
  simp only [CollatzResearch.WordTrace]
  refine ⟨103154131962802339586025353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68769421308534893057350235 103154131962802339586025353)
  ·
    refine ⟨77365598972101754689519015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103154131962802339586025353 77365598972101754689519015)
    ·
      refine ⟨116048398458152632034278523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77365598972101754689519015 116048398458152632034278523)
      ·
        refine ⟨174072597687228948051417785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116048398458152632034278523 174072597687228948051417785)
        ·
          refine ⟨130554448265421711038563339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174072597687228948051417785 130554448265421711038563339)
          ·
            refine ⟨195831672398132566557845009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130554448265421711038563339 195831672398132566557845009)
            ·
              refine ⟨146873754298599424918383757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195831672398132566557845009 146873754298599424918383757)
              ·
                refine ⟨55077657861974784344393909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146873754298599424918383757 55077657861974784344393909)
                ·
                  refine ⟨5163530424560136032286929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55077657861974784344393909 5163530424560136032286929)
                  ·
                    refine ⟨3872647818420102024215197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5163530424560136032286929 3872647818420102024215197)
                    ·
                      refine ⟨1452242931907538259080699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3872647818420102024215197 1452242931907538259080699)
                      ·
                        rfl

theorem cell23_2828233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 2, 3].length) (baseStart_2828233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828233 prefixEnd_2828233 := by exact prefixLift 2828233
  have htrace : WordTrace (prefixWord ++ tailWord_2828233) baseStart_2828233 baseEnd_2828233 := by
    simpa [prefixWord, tailWord_2828233, baseEnd_2828233] using wordTrace_append hprefix tailTrace_2828233
  have hstable : (prefixWord ++ tailWord_2828233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828233).length < 2 ^ (prefixWord ++ tailWord_2828233).sum := by decide
  have hdescent : baseEnd_2828233 < baseStart_2828233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828264 : List Nat := [2, 1, 4, 1, 1, 1, 1, 7, 1, 2, 2]
def baseStart_2828264 : Nat := 118140960795 + 2828264 * 2 ^ 59
def prefixEnd_2828264 : Nat := 4983230072969 + 3 ^ 40 * 2828264 * 2
def baseEnd_2828264 : Nat := 1452258849807827637793057

theorem tailTrace_2828264 : CollatzResearch.WordTrace tailWord_2828264 prefixEnd_2828264 1452258849807827637793057 := by
  unfold tailWord_2828264
  simp only [CollatzResearch.WordTrace]
  refine ⟨51577631312845015940201923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68770175083793354586935897 51577631312845015940201923)
  ·
    refine ⟨77366446969267523910302885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51577631312845015940201923 77366446969267523910302885)
    ·
      refine ⟨14506208806737660733181791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77366446969267523910302885 14506208806737660733181791)
      ·
        refine ⟨21759313210106491099772687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14506208806737660733181791 21759313210106491099772687)
        ·
          refine ⟨32638969815159736649659031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21759313210106491099772687 32638969815159736649659031)
          ·
            refine ⟨48958454722739604974488547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32638969815159736649659031 48958454722739604974488547)
            ·
              refine ⟨73437682084109407461732821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48958454722739604974488547 73437682084109407461732821)
              ·
                refine ⟨1721195673846314237384363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 73437682084109407461732821 1721195673846314237384363)
                ·
                  refine ⟨2581793510769471356076545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721195673846314237384363 2581793510769471356076545)
                  ·
                    refine ⟨1936345133077103517057409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2581793510769471356076545 1936345133077103517057409)
                    ·
                      refine ⟨1452258849807827637793057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1936345133077103517057409 1452258849807827637793057)
                      ·
                        rfl

theorem cell23_2828264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_2828264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828264 prefixEnd_2828264 := by exact prefixLift 2828264
  have htrace : WordTrace (prefixWord ++ tailWord_2828264) baseStart_2828264 baseEnd_2828264 := by
    simpa [prefixWord, tailWord_2828264, baseEnd_2828264] using wordTrace_append hprefix tailTrace_2828264
  have hstable : (prefixWord ++ tailWord_2828264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828264).length < 2 ^ (prefixWord ++ tailWord_2828264).sum := by decide
  have hdescent : baseEnd_2828264 < baseStart_2828264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828280 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 4, 1, 3]
def baseStart_2828280 : Nat := 118140960795 + 2828280 * 2 ^ 59
def prefixEnd_2828280 : Nat := 4983230072969 + 3 ^ 40 * 2828280 * 2
def baseEnd_2828280 : Nat := 1452267065498299575192983

theorem tailTrace_2828280 : CollatzResearch.WordTrace tailWord_2828280 prefixEnd_2828280 1452267065498299575192983 := by
  unfold tailWord_2828280
  simp only [CollatzResearch.WordTrace]
  refine ⟨51577923096816033306493147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68770564129088044408657529 51577923096816033306493147)
  ·
    refine ⟨77366884645224049959739721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51577923096816033306493147 77366884645224049959739721)
    ·
      refine ⟨58025163483918037469804791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77366884645224049959739721 58025163483918037469804791)
      ·
        refine ⟨87037745225877056204707187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58025163483918037469804791 87037745225877056204707187)
        ·
          refine ⟨130556617838815584307060781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87037745225877056204707187 130556617838815584307060781)
          ·
            refine ⟨48958731689555844115147793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130556617838815584307060781 48958731689555844115147793)
            ·
              refine ⟨36719048767166883086360845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48958731689555844115147793 36719048767166883086360845)
              ·
                refine ⟨13769643287687581157385317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36719048767166883086360845 13769643287687581157385317)
                ·
                  refine ⟨2581808116441421467009747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13769643287687581157385317 2581808116441421467009747)
                  ·
                    refine ⟨3872712174662132200514621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2581808116441421467009747 3872712174662132200514621)
                    ·
                      refine ⟨1452267065498299575192983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3872712174662132200514621 1452267065498299575192983)
                      ·
                        rfl

theorem cell23_2828280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_2828280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828280 prefixEnd_2828280 := by exact prefixLift 2828280
  have htrace : WordTrace (prefixWord ++ tailWord_2828280) baseStart_2828280 baseEnd_2828280 := by
    simpa [prefixWord, tailWord_2828280, baseEnd_2828280] using wordTrace_append hprefix tailTrace_2828280
  have hstable : (prefixWord ++ tailWord_2828280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828280).length < 2 ^ (prefixWord ++ tailWord_2828280).sum := by decide
  have hdescent : baseEnd_2828280 < baseStart_2828280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828281 : List Nat := [1, 2, 1, 3, 1, 4, 4, 2, 1, 2, 2]
def baseStart_2828281 : Nat := 118140960795 + 2828281 * 2 ^ 59
def prefixEnd_2828281 : Nat := 4983230072969 + 3 ^ 40 * 2828281 * 2
def baseEnd_2828281 : Nat := 1452267578978954071280479

theorem tailTrace_2828281 : CollatzResearch.WordTrace tailWord_2828281 prefixEnd_2828281 1452267578978954071280479 := by
  unfold tailWord_2828281
  simp only [CollatzResearch.WordTrace]
  refine ⟨103155882666628443783772697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68770588444418962522515131 103155882666628443783772697)
  ·
    refine ⟨77366911999971332837829523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103155882666628443783772697 77366911999971332837829523)
    ·
      refine ⟨116050367999956999256744285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77366911999971332837829523 116050367999956999256744285)
      ·
        refine ⟨43518887999983874721279107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116050367999956999256744285 43518887999983874721279107)
        ·
          refine ⟨65278331999975812081918661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43518887999983874721279107 65278331999975812081918661)
          ·
            refine ⟨12239687249995464765359749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65278331999975812081918661 12239687249995464765359749)
            ·
              refine ⟨2294941359374149643504953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12239687249995464765359749 2294941359374149643504953)
              ·
                refine ⟨1721206019530612232628715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2294941359374149643504953 1721206019530612232628715)
                ·
                  refine ⟨2581809029295918348943073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721206019530612232628715 2581809029295918348943073)
                  ·
                    refine ⟨1936356771971938761707305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2581809029295918348943073 1936356771971938761707305)
                    ·
                      refine ⟨1452267578978954071280479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1936356771971938761707305 1452267578978954071280479)
                      ·
                        rfl

theorem cell23_2828281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_2828281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828281 prefixEnd_2828281 := by exact prefixLift 2828281
  have htrace : WordTrace (prefixWord ++ tailWord_2828281) baseStart_2828281 baseEnd_2828281 := by
    simpa [prefixWord, tailWord_2828281, baseEnd_2828281] using wordTrace_append hprefix tailTrace_2828281
  have hstable : (prefixWord ++ tailWord_2828281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828281).length < 2 ^ (prefixWord ++ tailWord_2828281).sum := by decide
  have hdescent : baseEnd_2828281 < baseStart_2828281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828323 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 5]
def baseStart_2828323 : Nat := 118140960795 + 2828323 * 2 ^ 59
def prefixEnd_2828323 : Nat := 4983230072969 + 3 ^ 40 * 2828323 * 2
def baseEnd_2828323 : Nat := 1452289145166442906955285

theorem tailTrace_2828323 : CollatzResearch.WordTrace tailWord_2828323 prefixEnd_2828323 1452289145166442906955285 := by
  unfold tailWord_2828323
  simp only [CollatzResearch.WordTrace]
  refine ⟨103157414532476284956801623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68771609688317523304534415 103157414532476284956801623)
  ·
    refine ⟨154736121798714427435202435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103157414532476284956801623 154736121798714427435202435)
    ·
      refine ⟨232104182698071641152803653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154736121798714427435202435 232104182698071641152803653)
      ·
        refine ⟨43519534255888432716150685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232104182698071641152803653 43519534255888432716150685)
        ·
          refine ⟨16319825345958162268556507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43519534255888432716150685 16319825345958162268556507)
          ·
            refine ⟨24479738018937243402834761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16319825345958162268556507 24479738018937243402834761)
            ·
              refine ⟨18359803514202932552126071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24479738018937243402834761 18359803514202932552126071)
              ·
                refine ⟨27539705271304398828189107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18359803514202932552126071 27539705271304398828189107)
                ·
                  refine ⟨41309557906956598242283661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27539705271304398828189107 41309557906956598242283661)
                  ·
                    refine ⟨15491084215108724340856373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41309557906956598242283661 15491084215108724340856373)
                    ·
                      refine ⟨1452289145166442906955285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15491084215108724340856373 1452289145166442906955285)
                      ·
                        rfl

theorem cell23_2828323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_2828323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828323 prefixEnd_2828323 := by exact prefixLift 2828323
  have htrace : WordTrace (prefixWord ++ tailWord_2828323) baseStart_2828323 baseEnd_2828323 := by
    simpa [prefixWord, tailWord_2828323, baseEnd_2828323] using wordTrace_append hprefix tailTrace_2828323
  have hstable : (prefixWord ++ tailWord_2828323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828323).length < 2 ^ (prefixWord ++ tailWord_2828323).sum := by decide
  have hdescent : baseEnd_2828323 < baseStart_2828323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828330 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 2, 6]
def baseStart_2828330 : Nat := 118140960795 + 2828330 * 2 ^ 59
def prefixEnd_2828330 : Nat := 4983230072969 + 3 ^ 40 * 2828330 * 2
def baseEnd_2828330 : Nat := 484097579843674793189251

theorem tailTrace_2828330 : CollatzResearch.WordTrace tailWord_2828330 prefixEnd_2828330 484097579843674793189251 := by
  unfold tailWord_2828330
  simp only [CollatzResearch.WordTrace]
  refine ⟨25789417460862731288076611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68771779895633950101537629 25789417460862731288076611)
  ·
    refine ⟨38684126191294096932114917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25789417460862731288076611 38684126191294096932114917)
    ·
      refine ⟨7253273660867643174771547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38684126191294096932114917 7253273660867643174771547)
      ·
        refine ⟨10879910491301464762157321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7253273660867643174771547 10879910491301464762157321)
        ·
          refine ⟨8159932868476098571617991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10879910491301464762157321 8159932868476098571617991)
          ·
            refine ⟨12239899302714147857426987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8159932868476098571617991 12239899302714147857426987)
            ·
              refine ⟨18359848954071221786140481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12239899302714147857426987 18359848954071221786140481)
              ·
                refine ⟨13769886715553416339605361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18359848954071221786140481 13769886715553416339605361)
                ·
                  refine ⟨10327415036665062254704021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13769886715553416339605361 10327415036665062254704021)
                  ·
                    refine ⟨484097579843674793189251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10327415036665062254704021 484097579843674793189251)
                    ·
                      rfl

theorem cell23_2828330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_2828330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828330 prefixEnd_2828330 := by exact prefixLift 2828330
  have htrace : WordTrace (prefixWord ++ tailWord_2828330) baseStart_2828330 baseEnd_2828330 := by
    simpa [prefixWord, tailWord_2828330, baseEnd_2828330] using wordTrace_append hprefix tailTrace_2828330
  have hstable : (prefixWord ++ tailWord_2828330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828330).length < 2 ^ (prefixWord ++ tailWord_2828330).sum := by decide
  have hdescent : baseEnd_2828330 < baseStart_2828330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828343 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 7]
def baseStart_2828343 : Nat := 118140960795 + 2828343 * 2 ^ 59
def prefixEnd_2828343 : Nat := 4983230072969 + 3 ^ 40 * 2828343 * 2
def baseEnd_2828343 : Nat := 161366601642170314300577

theorem tailTrace_2828343 : CollatzResearch.WordTrace tailWord_2828343 prefixEnd_2828343 161366601642170314300577 := by
  unfold tailWord_2828343
  simp only [CollatzResearch.WordTrace]
  refine ⟨103158143992403828372529683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68772095994935885581686455 103158143992403828372529683)
  ·
    refine ⟨154737215988605742558794525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103158143992403828372529683 154737215988605742558794525)
    ·
      refine ⟨58026455995727153459547947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154737215988605742558794525 58026455995727153459547947)
      ·
        refine ⟨87039683993590730189321921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58026455995727153459547947 87039683993590730189321921)
        ·
          refine ⟨65279762995193047641991441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87039683993590730189321921 65279762995193047641991441)
          ·
            refine ⟨48959822246394785731493581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65279762995193047641991441 48959822246394785731493581)
            ·
              refine ⟨18359933342398044649310093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48959822246394785731493581 18359933342398044649310093)
              ·
                refine ⟨6884975003399266743491285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18359933342398044649310093 6884975003399266743491285)
                ·
                  refine ⟨161366601642170314300577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6884975003399266743491285 161366601642170314300577)
                  ·
                    rfl

theorem cell23_2828343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 7].length) (baseStart_2828343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828343 prefixEnd_2828343 := by exact prefixLift 2828343
  have htrace : WordTrace (prefixWord ++ tailWord_2828343) baseStart_2828343 baseEnd_2828343 := by
    simpa [prefixWord, tailWord_2828343, baseEnd_2828343] using wordTrace_append hprefix tailTrace_2828343
  have hstable : (prefixWord ++ tailWord_2828343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828343).length < 2 ^ (prefixWord ++ tailWord_2828343).sum := by decide
  have hdescent : baseEnd_2828343 < baseStart_2828343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828374 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2828374 : Nat := 118140960795 + 2828374 * 2 ^ 59
def prefixEnd_2828374 : Nat := 4983230072969 + 3 ^ 40 * 2828374 * 2
def baseEnd_2828374 : Nat := 1452315332679822207417551

theorem tailTrace_2828374 : CollatzResearch.WordTrace tailWord_2828374 prefixEnd_2828374 1452315332679822207417551 := by
  unfold tailWord_2828374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6447454665955720041681761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68772849770194347111272117 6447454665955720041681761)
  ·
    refine ⟨4835590999466790031261321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6447454665955720041681761 4835590999466790031261321)
    ·
      refine ⟨3626693249600092523445991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4835590999466790031261321 3626693249600092523445991)
      ·
        refine ⟨5440039874400138785168987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3626693249600092523445991 5440039874400138785168987)
        ·
          refine ⟨8160059811600208177753481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5440039874400138785168987 8160059811600208177753481)
          ·
            refine ⟨6120044858700156133315111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8160059811600208177753481 6120044858700156133315111)
            ·
              refine ⟨9180067288050234199972667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6120044858700156133315111 9180067288050234199972667)
              ·
                refine ⟨13770100932075351299959001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9180067288050234199972667 13770100932075351299959001)
                ·
                  refine ⟨10327575699056513474969251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13770100932075351299959001 10327575699056513474969251)
                  ·
                    refine ⟨15491363548584770212453877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10327575699056513474969251 15491363548584770212453877)
                    ·
                      refine ⟨1452315332679822207417551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15491363548584770212453877 1452315332679822207417551)
                      ·
                        rfl

theorem cell23_2828374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2828374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828374 prefixEnd_2828374 := by exact prefixLift 2828374
  have htrace : WordTrace (prefixWord ++ tailWord_2828374) baseStart_2828374 baseEnd_2828374 := by
    simpa [prefixWord, tailWord_2828374, baseEnd_2828374] using wordTrace_append hprefix tailTrace_2828374
  have hstable : (prefixWord ++ tailWord_2828374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828374).length < 2 ^ (prefixWord ++ tailWord_2828374).sum := by decide
  have hdescent : baseEnd_2828374 < baseStart_2828374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828394 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 7]
def baseStart_2828394 : Nat := 118140960795 + 2828394 * 2 ^ 59
def prefixEnd_2828394 : Nat := 4983230072969 + 3 ^ 40 * 2828394 * 2
def baseEnd_2828394 : Nat := 161369511365879125463051

theorem tailTrace_2828394 : CollatzResearch.WordTrace tailWord_2828394 prefixEnd_2828394 161369511365879125463051 := by
  unfold tailWord_2828394
  simp only [CollatzResearch.WordTrace]
  refine ⟨25790001028804766020659059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68773336076812709388424157 25790001028804766020659059)
  ·
    refine ⟨38685001543207149030988589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25790001028804766020659059 38685001543207149030988589)
    ·
      refine ⟨14506875578702680886620721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38685001543207149030988589 14506875578702680886620721)
      ·
        refine ⟨10880156684027010664965541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14506875578702680886620721 10880156684027010664965541)
        ·
          refine ⟨2040029378255064499681039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10880156684027010664965541 2040029378255064499681039)
          ·
            refine ⟨3060044067382596749521559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040029378255064499681039 3060044067382596749521559)
            ·
              refine ⟨4590066101073895124282339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3060044067382596749521559 4590066101073895124282339)
              ·
                refine ⟨6885099151610842686423509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4590066101073895124282339 6885099151610842686423509)
                ·
                  refine ⟨161369511365879125463051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6885099151610842686423509 161369511365879125463051)
                  ·
                    rfl

theorem cell23_2828394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 7].length) (baseStart_2828394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828394 prefixEnd_2828394 := by exact prefixLift 2828394
  have htrace : WordTrace (prefixWord ++ tailWord_2828394) baseStart_2828394 baseEnd_2828394 := by
    simpa [prefixWord, tailWord_2828394, baseEnd_2828394] using wordTrace_append hprefix tailTrace_2828394
  have hstable : (prefixWord ++ tailWord_2828394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828394).length < 2 ^ (prefixWord ++ tailWord_2828394).sum := by decide
  have hdescent : baseEnd_2828394 < baseStart_2828394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828397 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 2, 5, 2]
def baseStart_2828397 : Nat := 118140960795 + 2828397 * 2 ^ 59
def prefixEnd_2828397 : Nat := 4983230072969 + 3 ^ 40 * 2828397 * 2
def baseEnd_2828397 : Nat := 1452327142734875617429945

theorem tailTrace_2828397 : CollatzResearch.WordTrace tailWord_2828397 prefixEnd_2828397 1452327142734875617429945 := by
  unfold tailWord_2828397
  simp only [CollatzResearch.WordTrace]
  refine ⟨103160113534208195594995445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68773409022805463729996963 103160113534208195594995445)
  ·
    refine ⟨9671260643832018337030823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103160113534208195594995445 9671260643832018337030823)
    ·
      refine ⟨14506890965748027505546235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9671260643832018337030823 14506890965748027505546235)
      ·
        refine ⟨21760336448622041258319353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14506890965748027505546235 21760336448622041258319353)
        ·
          refine ⟨16320252336466530943739515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21760336448622041258319353 16320252336466530943739515)
          ·
            refine ⟨24480378504699796415609273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16320252336466530943739515 24480378504699796415609273)
            ·
              refine ⟨18360283878524847311706955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24480378504699796415609273 18360283878524847311706955)
              ·
                refine ⟨27540425817787270967560433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18360283878524847311706955 27540425817787270967560433)
                ·
                  refine ⟨20655319363340453225670325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27540425817787270967560433 20655319363340453225670325)
                  ·
                    refine ⟨1936436190313167489906593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20655319363340453225670325 1936436190313167489906593)
                    ·
                      refine ⟨1452327142734875617429945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1936436190313167489906593 1452327142734875617429945)
                      ·
                        rfl

theorem cell23_2828397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_2828397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828397 prefixEnd_2828397 := by exact prefixLift 2828397
  have htrace : WordTrace (prefixWord ++ tailWord_2828397) baseStart_2828397 baseEnd_2828397 := by
    simpa [prefixWord, tailWord_2828397, baseEnd_2828397] using wordTrace_append hprefix tailTrace_2828397
  have hstable : (prefixWord ++ tailWord_2828397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828397).length < 2 ^ (prefixWord ++ tailWord_2828397).sum := by decide
  have hdescent : baseEnd_2828397 < baseStart_2828397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828400 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 5]
def baseStart_2828400 : Nat := 118140960795 + 2828400 * 2 ^ 59
def prefixEnd_2828400 : Nat := 4983230072969 + 3 ^ 40 * 2828400 * 2
def baseEnd_2828400 : Nat := 1452328683176839105692431

theorem tailTrace_2828400 : CollatzResearch.WordTrace tailWord_2828400 prefixEnd_2828400 1452328683176839105692431 := by
  unfold tailWord_2828400
  simp only [CollatzResearch.WordTrace]
  refine ⟨51580111476598663553677327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68773481968798218071569769 51580111476598663553677327)
  ·
    refine ⟨77370167214897995330515991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51580111476598663553677327 77370167214897995330515991)
    ·
      refine ⟨116055250822346992995773987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77370167214897995330515991 116055250822346992995773987)
      ·
        refine ⟨174082876233520489493660981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116055250822346992995773987 174082876233520489493660981)
        ·
          refine ⟨16320269646892545890030717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174082876233520489493660981 16320269646892545890030717)
          ·
            refine ⟨6120101117584704708761519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16320269646892545890030717 6120101117584704708761519)
            ·
              refine ⟨9180151676377057063142279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6120101117584704708761519 9180151676377057063142279)
              ·
                refine ⟨13770227514565585594713419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9180151676377057063142279 13770227514565585594713419)
                ·
                  refine ⟨20655341271848378392070129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13770227514565585594713419 20655341271848378392070129)
                  ·
                    refine ⟨15491505953886283794052597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20655341271848378392070129 15491505953886283794052597)
                    ·
                      refine ⟨1452328683176839105692431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15491505953886283794052597 1452328683176839105692431)
                      ·
                        rfl

theorem cell23_2828400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_2828400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828400 prefixEnd_2828400 := by exact prefixLift 2828400
  have htrace : WordTrace (prefixWord ++ tailWord_2828400) baseStart_2828400 baseEnd_2828400 := by
    simpa [prefixWord, tailWord_2828400, baseEnd_2828400] using wordTrace_append hprefix tailTrace_2828400
  have hstable : (prefixWord ++ tailWord_2828400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828400).length < 2 ^ (prefixWord ++ tailWord_2828400).sum := by decide
  have hdescent : baseEnd_2828400 < baseStart_2828400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828501 : List Nat := [1, 3, 2, 4, 3, 1, 1, 2, 6]
def baseStart_2828501 : Nat := 118140960795 + 2828501 * 2 ^ 59
def prefixEnd_2828501 : Nat := 4983230072969 + 3 ^ 40 * 2828501 * 2
def baseEnd_2828501 : Nat := 161375616080327023392163

theorem tailTrace_2828501 : CollatzResearch.WordTrace tailWord_2828501 prefixEnd_2828501 161375616080327023392163 := by
  unfold tailWord_2828501
  simp only [CollatzResearch.WordTrace]
  refine ⟨103163906725831421356781357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68775937817220947571187571 103163906725831421356781357)
  ·
    refine ⟨38686465022186783008793009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103163906725831421356781357 38686465022186783008793009)
    ·
      refine ⟨29014848766640087256594757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38686465022186783008793009 29014848766640087256594757)
      ·
        refine ⟨5440284143745016360611517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29014848766640087256594757 5440284143745016360611517)
        ·
          refine ⟨2040106553904381135229319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5440284143745016360611517 2040106553904381135229319)
          ·
            refine ⟨3060159830856571702843979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040106553904381135229319 3060159830856571702843979)
            ·
              refine ⟨4590239746284857554265969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3060159830856571702843979 4590239746284857554265969)
              ·
                refine ⟨3442679809713643165699477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4590239746284857554265969 3442679809713643165699477)
                ·
                  refine ⟨161375616080327023392163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3442679809713643165699477 161375616080327023392163)
                  ·
                    rfl

theorem cell23_2828501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 6].length) (baseStart_2828501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828501 prefixEnd_2828501 := by exact prefixLift 2828501
  have htrace : WordTrace (prefixWord ++ tailWord_2828501) baseStart_2828501 baseEnd_2828501 := by
    simpa [prefixWord, tailWord_2828501, baseEnd_2828501] using wordTrace_append hprefix tailTrace_2828501
  have hstable : (prefixWord ++ tailWord_2828501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828501).length < 2 ^ (prefixWord ++ tailWord_2828501).sum := by decide
  have hdescent : baseEnd_2828501 < baseStart_2828501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828527 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 1, 6]
def baseStart_2828527 : Nat := 118140960795 + 2828527 * 2 ^ 59
def prefixEnd_2828527 : Nat := 4983230072969 + 3 ^ 40 * 2828527 * 2
def baseEnd_2828527 : Nat := 484131298406653369601449

theorem tailTrace_2828527 : CollatzResearch.WordTrace tailWord_2828527 prefixEnd_2828527 484131298406653369601449 := by
  unfold tailWord_2828527
  simp only [CollatzResearch.WordTrace]
  refine ⟨103164855023737227797227835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68776570015824818531485223 103164855023737227797227835)
  ·
    refine ⟨154747282535605841695841753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103164855023737227797227835 154747282535605841695841753)
    ·
      refine ⟨116060461901704381271881315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154747282535605841695841753 116060461901704381271881315)
      ·
        refine ⟨174090692852556571907821973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116060461901704381271881315 174090692852556571907821973)
        ·
          refine ⟨8160501227463589308179155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 174090692852556571907821973 8160501227463589308179155)
          ·
            refine ⟨12240751841195383962268733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8160501227463589308179155 12240751841195383962268733)
            ·
              refine ⟨4590281940448268985850775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12240751841195383962268733 4590281940448268985850775)
              ·
                refine ⟨6885422910672403478776163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4590281940448268985850775 6885422910672403478776163)
                ·
                  refine ⟨10328134366008605218164245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6885422910672403478776163 10328134366008605218164245)
                  ·
                    refine ⟨484131298406653369601449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10328134366008605218164245 484131298406653369601449)
                    ·
                      rfl

theorem cell23_2828527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 6].length) (baseStart_2828527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828527 prefixEnd_2828527 := by exact prefixLift 2828527
  have htrace : WordTrace (prefixWord ++ tailWord_2828527) baseStart_2828527 baseEnd_2828527 := by
    simpa [prefixWord, tailWord_2828527, baseEnd_2828527] using wordTrace_append hprefix tailTrace_2828527
  have hstable : (prefixWord ++ tailWord_2828527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828527).length < 2 ^ (prefixWord ++ tailWord_2828527).sum := by decide
  have hdescent : baseEnd_2828527 < baseStart_2828527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828534 : List Nat := [5, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_2828534 : Nat := 118140960795 + 2828534 * 2 ^ 59
def prefixEnd_2828534 : Nat := 4983230072969 + 3 ^ 40 * 2828534 * 2
def baseEnd_2828534 : Nat := 1452397489584541581416815

theorem tailTrace_2828534 : CollatzResearch.WordTrace tailWord_2828534 prefixEnd_2828534 1452397489584541581416815 := by
  unfold tailWord_2828534
  simp only [CollatzResearch.WordTrace]
  refine ⟨6447819395919491749545791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68776740223141245328488437 6447819395919491749545791)
  ·
    refine ⟨9671729093879237624318687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6447819395919491749545791 9671729093879237624318687)
    ·
      refine ⟨14507593640818856436478031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9671729093879237624318687 14507593640818856436478031)
      ·
        refine ⟨21761390461228284654717047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14507593640818856436478031 21761390461228284654717047)
        ·
          refine ⟨32642085691842426982075571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21761390461228284654717047 32642085691842426982075571)
          ·
            refine ⟨48963128537763640473113357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32642085691842426982075571 48963128537763640473113357)
            ·
              refine ⟨18361173201661365177417509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48963128537763640473113357 18361173201661365177417509)
              ·
                refine ⟨3442719975311505970765783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18361173201661365177417509 3442719975311505970765783)
                ·
                  refine ⟨5164079962967258956148675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3442719975311505970765783 5164079962967258956148675)
                  ·
                    refine ⟨7746119944450888434223013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5164079962967258956148675 7746119944450888434223013)
                    ·
                      refine ⟨1452397489584541581416815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7746119944450888434223013 1452397489584541581416815)
                      ·
                        rfl

theorem cell23_2828534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_2828534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828534 prefixEnd_2828534 := by exact prefixLift 2828534
  have htrace : WordTrace (prefixWord ++ tailWord_2828534) baseStart_2828534 baseEnd_2828534 := by
    simpa [prefixWord, tailWord_2828534, baseEnd_2828534] using wordTrace_append hprefix tailTrace_2828534
  have hstable : (prefixWord ++ tailWord_2828534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828534).length < 2 ^ (prefixWord ++ tailWord_2828534).sum := by decide
  have hdescent : baseEnd_2828534 < baseStart_2828534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828554 : List Nat := [3, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3]
def baseStart_2828554 : Nat := 118140960795 + 2828554 * 2 ^ 59
def prefixEnd_2828554 : Nat := 4983230072969 + 3 ^ 40 * 2828554 * 2
def baseEnd_2828554 : Nat := 1452407759197631503166723

theorem tailTrace_2828554 : CollatzResearch.WordTrace tailWord_2828554 prefixEnd_2828554 1452407759197631503166723 := by
  unfold tailWord_2828554
  simp only [CollatzResearch.WordTrace]
  refine ⟨25791459948659852852115179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68777226529759607605640477 25791459948659852852115179)
  ·
    refine ⟨38687189922989779278172769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25791459948659852852115179 38687189922989779278172769)
    ·
      refine ⟨29015392442242334458629577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38687189922989779278172769 29015392442242334458629577)
      ·
        refine ⟨21761544331681750843972183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29015392442242334458629577 21761544331681750843972183)
        ·
          refine ⟨32642316497522626265958275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21761544331681750843972183 32642316497522626265958275)
          ·
            refine ⟨48963474746283939398937413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32642316497522626265958275 48963474746283939398937413)
            ·
              refine ⟨9180651514928238637300765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48963474746283939398937413 9180651514928238637300765)
              ·
                refine ⟨3442744318098089488987787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9180651514928238637300765 3442744318098089488987787)
                ·
                  refine ⟨5164116477147134233481681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3442744318098089488987787 5164116477147134233481681)
                  ·
                    refine ⟨3873087357860350675111261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5164116477147134233481681 3873087357860350675111261)
                    ·
                      refine ⟨1452407759197631503166723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3873087357860350675111261 1452407759197631503166723)
                      ·
                        rfl

theorem cell23_2828554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_2828554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828554 prefixEnd_2828554 := by exact prefixLift 2828554
  have htrace : WordTrace (prefixWord ++ tailWord_2828554) baseStart_2828554 baseEnd_2828554 := by
    simpa [prefixWord, tailWord_2828554, baseEnd_2828554] using wordTrace_append hprefix tailTrace_2828554
  have hstable : (prefixWord ++ tailWord_2828554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828554).length < 2 ^ (prefixWord ++ tailWord_2828554).sum := by decide
  have hdescent : baseEnd_2828554 < baseStart_2828554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828574 : List Nat := [4, 3, 2, 1, 1, 1, 1, 10]
def baseStart_2828574 : Nat := 118140960795 + 2828574 * 2 ^ 59
def prefixEnd_2828574 : Nat := 4983230072969 + 3 ^ 40 * 2828574 * 2
def baseEnd_2828574 : Nat := 53793260326323015737653

theorem tailTrace_2828574 : CollatzResearch.WordTrace tailWord_2828574 prefixEnd_2828574 53793260326323015737653 := by
  unfold tailWord_2828574
  simp only [CollatzResearch.WordTrace]
  refine ⟨12895821156820869353023597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68777712836377969882792517 12895821156820869353023597)
  ·
    refine ⟨4835932933807826007383849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12895821156820869353023597 4835932933807826007383849)
    ·
      refine ⟨3626949700355869505537887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4835932933807826007383849 3626949700355869505537887)
      ·
        refine ⟨5440424550533804258306831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3626949700355869505537887 5440424550533804258306831)
        ·
          refine ⟨8160636825800706387460247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5440424550533804258306831 8160636825800706387460247)
          ·
            refine ⟨12240955238701059581190371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8160636825800706387460247 12240955238701059581190371)
            ·
              refine ⟨18361432858051589371785557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12240955238701059581190371 18361432858051589371785557)
              ·
                refine ⟨53793260326323015737653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18361432858051589371785557 53793260326323015737653)
                ·
                  rfl

theorem cell23_2828574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 10].length) (baseStart_2828574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828574 prefixEnd_2828574 := by exact prefixLift 2828574
  have htrace : WordTrace (prefixWord ++ tailWord_2828574) baseStart_2828574 baseEnd_2828574 := by
    simpa [prefixWord, tailWord_2828574, baseEnd_2828574] using wordTrace_append hprefix tailTrace_2828574
  have hstable : (prefixWord ++ tailWord_2828574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828574).length < 2 ^ (prefixWord ++ tailWord_2828574).sum := by decide
  have hdescent : baseEnd_2828574 < baseStart_2828574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828578 : List Nat := [3, 3, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_2828578 : Nat := 118140960795 + 2828578 * 2 ^ 59
def prefixEnd_2828578 : Nat := 4983230072969 + 3 ^ 40 * 2828578 * 2
def baseEnd_2828578 : Nat := 484140027577779803088871

theorem tailTrace_2828578 : CollatzResearch.WordTrace tailWord_2828578 prefixEnd_2828578 484140027577779803088871 := by
  unfold tailWord_2828578
  simp only [CollatzResearch.WordTrace]
  refine ⟨25791678786638115876833597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68777810097701642338222925 25791678786638115876833597)
  ·
    refine ⟨9671879544989293453812599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25791678786638115876833597 9671879544989293453812599)
    ·
      refine ⟨14507819317483940180718899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9671879544989293453812599 14507819317483940180718899)
      ·
        refine ⟨21761728976225910271078349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14507819317483940180718899 21761728976225910271078349)
        ·
          refine ⟨8160648366084716351654381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21761728976225910271078349 8160648366084716351654381)
          ·
            refine ⟨3060243137281768631870393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8160648366084716351654381 3060243137281768631870393)
            ·
              refine ⟨2295182352961326473902795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3060243137281768631870393 2295182352961326473902795)
              ·
                refine ⟨3442773529441989710854193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2295182352961326473902795 3442773529441989710854193)
                ·
                  refine ⟨2582080147081492283140645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3442773529441989710854193 2582080147081492283140645)
                  ·
                    refine ⟨484140027577779803088871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2582080147081492283140645 484140027577779803088871)
                    ·
                      rfl

theorem cell23_2828578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_2828578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828578 prefixEnd_2828578 := by exact prefixLift 2828578
  have htrace : WordTrace (prefixWord ++ tailWord_2828578) baseStart_2828578 baseEnd_2828578 := by
    simpa [prefixWord, tailWord_2828578, baseEnd_2828578] using wordTrace_append hprefix tailTrace_2828578
  have hstable : (prefixWord ++ tailWord_2828578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828578).length < 2 ^ (prefixWord ++ tailWord_2828578).sum := by decide
  have hdescent : baseEnd_2828578 < baseStart_2828578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828647 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 9]
def baseStart_2828647 : Nat := 118140960795 + 2828647 * 2 ^ 59
def prefixEnd_2828647 : Nat := 4983230072969 + 3 ^ 40 * 2828647 * 2
def baseEnd_2828647 : Nat := 161383945877611071033755

theorem tailTrace_2828647 : CollatzResearch.WordTrace tailWord_2828647 prefixEnd_2828647 161383945877611071033755 := by
  unfold tailWord_2828647
  simp only [CollatzResearch.WordTrace]
  refine ⟨103169231783302488291596195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68779487855534992194397463 103169231783302488291596195)
  ·
    refine ⟨154753847674953732437394293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103169231783302488291596195 154753847674953732437394293)
    ·
      refine ⟨14508173219526912416005715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154753847674953732437394293 14508173219526912416005715)
      ·
        refine ⟨21762259829290368624008573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14508173219526912416005715 21762259829290368624008573)
        ·
          refine ⟨8160847435983888234003215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21762259829290368624008573 8160847435983888234003215)
          ·
            refine ⟨12241271153975832351004823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8160847435983888234003215 12241271153975832351004823)
            ·
              refine ⟨18361906730963748526507235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12241271153975832351004823 18361906730963748526507235)
              ·
                refine ⟨27542860096445622789760853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18361906730963748526507235 27542860096445622789760853)
                ·
                  refine ⟨161383945877611071033755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27542860096445622789760853 161383945877611071033755)
                  ·
                    rfl

theorem cell23_2828647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 9].length) (baseStart_2828647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828647 prefixEnd_2828647 := by exact prefixLift 2828647
  have htrace : WordTrace (prefixWord ++ tailWord_2828647) baseStart_2828647 baseEnd_2828647 := by
    simpa [prefixWord, tailWord_2828647, baseEnd_2828647] using wordTrace_append hprefix tailTrace_2828647
  have hstable : (prefixWord ++ tailWord_2828647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828647).length < 2 ^ (prefixWord ++ tailWord_2828647).sum := by decide
  have hdescent : baseEnd_2828647 < baseStart_2828647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828657 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 3, 5, 3]
def baseStart_2828657 : Nat := 118140960795 + 2828657 * 2 ^ 59
def prefixEnd_2828657 : Nat := 4983230072969 + 3 ^ 40 * 2828657 * 2
def baseEnd_2828657 : Nat := 1452460647705044600178749

theorem tailTrace_2828657 : CollatzResearch.WordTrace tailWord_2828657 prefixEnd_2828657 1452460647705044600178749 := by
  unfold tailWord_2828657
  simp only [CollatzResearch.WordTrace]
  refine ⟨103169596513266259999460225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68779731008844173332973483 103169596513266259999460225)
  ·
    refine ⟨77377197384949694999595169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103169596513266259999460225 77377197384949694999595169)
    ·
      refine ⟨58032898038712271249696377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77377197384949694999595169 58032898038712271249696377)
      ·
        refine ⟨43524673529034203437272283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58032898038712271249696377 43524673529034203437272283)
        ·
          refine ⟨65287010293551305155908425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43524673529034203437272283 65287010293551305155908425)
          ·
            refine ⟨48965257720163478866931319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65287010293551305155908425 48965257720163478866931319)
            ·
              refine ⟨73447886580245218300396979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48965257720163478866931319 73447886580245218300396979)
              ·
                refine ⟨110171829870367827450595469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73447886580245218300396979 110171829870367827450595469)
                ·
                  refine ⟨41314436201387935293973301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110171829870367827450595469 41314436201387935293973301)
                  ·
                    refine ⟨3873228393880118933809997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41314436201387935293973301 3873228393880118933809997)
                    ·
                      refine ⟨1452460647705044600178749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3873228393880118933809997 1452460647705044600178749)
                      ·
                        rfl

theorem cell23_2828657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_2828657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828657 prefixEnd_2828657 := by exact prefixLift 2828657
  have htrace : WordTrace (prefixWord ++ tailWord_2828657) baseStart_2828657 baseEnd_2828657 := by
    simpa [prefixWord, tailWord_2828657, baseEnd_2828657] using wordTrace_append hprefix tailTrace_2828657
  have hstable : (prefixWord ++ tailWord_2828657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828657).length < 2 ^ (prefixWord ++ tailWord_2828657).sum := by decide
  have hdescent : baseEnd_2828657 < baseStart_2828657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828675 : List Nat := [1, 1, 1, 3, 6, 2, 1, 2, 2, 2, 2]
def baseStart_2828675 : Nat := 118140960795 + 2828675 * 2 ^ 59
def prefixEnd_2828675 : Nat := 4983230072969 + 3 ^ 40 * 2828675 * 2
def baseEnd_2828675 : Nat := 1452469890356825529753667

theorem tailTrace_2828675 : CollatzResearch.WordTrace tailWord_2828675 prefixEnd_2828675 1452469890356825529753667 := by
  unfold tailWord_2828675
  simp only [CollatzResearch.WordTrace]
  refine ⟨103170253027201049073615479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68780168684800699382410319 103170253027201049073615479)
  ·
    refine ⟨154755379540801573610423219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103170253027201049073615479 154755379540801573610423219)
    ·
      refine ⟨232133069311202360415634829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154755379540801573610423219 232133069311202360415634829)
      ·
        refine ⟨87049900991700885155863061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232133069311202360415634829 87049900991700885155863061)
        ·
          refine ⟨4080464108985978991681081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 87049900991700885155863061 4080464108985978991681081)
          ·
            refine ⟨3060348081739484243760811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4080464108985978991681081 3060348081739484243760811)
            ·
              refine ⟨4590522122609226365641217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3060348081739484243760811 4590522122609226365641217)
              ·
                refine ⟨3442891591956919774230913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4590522122609226365641217 3442891591956919774230913)
                ·
                  refine ⟨2582168693967689830673185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3442891591956919774230913 2582168693967689830673185)
                  ·
                    refine ⟨1936626520475767373004889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2582168693967689830673185 1936626520475767373004889)
                    ·
                      refine ⟨1452469890356825529753667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1936626520475767373004889 1452469890356825529753667)
                      ·
                        rfl

theorem cell23_2828675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 2, 2].length) (baseStart_2828675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828675 prefixEnd_2828675 := by exact prefixLift 2828675
  have htrace : WordTrace (prefixWord ++ tailWord_2828675) baseStart_2828675 baseEnd_2828675 := by
    simpa [prefixWord, tailWord_2828675, baseEnd_2828675] using wordTrace_append hprefix tailTrace_2828675
  have hstable : (prefixWord ++ tailWord_2828675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828675).length < 2 ^ (prefixWord ++ tailWord_2828675).sum := by decide
  have hdescent : baseEnd_2828675 < baseStart_2828675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828677 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 4, 5]
def baseStart_2828677 : Nat := 118140960795 + 2828677 * 2 ^ 59
def prefixEnd_2828677 : Nat := 4983230072969 + 3 ^ 40 * 2828677 * 2
def baseEnd_2828677 : Nat := 484156972439378173976219

theorem tailTrace_2828677 : CollatzResearch.WordTrace tailWord_2828677 prefixEnd_2828677 484156972439378173976219 := by
  unfold tailWord_2828677
  simp only [CollatzResearch.WordTrace]
  refine ⟨103170325973193803415188285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68780217315462535610125523 103170325973193803415188285)
  ·
    refine ⟨38688872239947676280695607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103170325973193803415188285 38688872239947676280695607)
    ·
      refine ⟨58033308359921514421043411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38688872239947676280695607 58033308359921514421043411)
      ·
        refine ⟨87049962539882271631565117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58033308359921514421043411 87049962539882271631565117)
        ·
          refine ⟨32643735952455851861836919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87049962539882271631565117 32643735952455851861836919)
          ·
            refine ⟨48965603928683777792755379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32643735952455851861836919 48965603928683777792755379)
            ·
              refine ⟨73448405893025666689133069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48965603928683777792755379 73448405893025666689133069)
              ·
                refine ⟨27543152209884625008424901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73448405893025666689133069 27543152209884625008424901)
                ·
                  refine ⟨5164341039353367189079669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27543152209884625008424901 5164341039353367189079669)
                  ·
                    refine ⟨484156972439378173976219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5164341039353367189079669 484156972439378173976219)
                    ·
                      rfl

theorem cell23_2828677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_2828677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828677 prefixEnd_2828677 := by exact prefixLift 2828677
  have htrace : WordTrace (prefixWord ++ tailWord_2828677) baseStart_2828677 baseEnd_2828677 := by
    simpa [prefixWord, tailWord_2828677, baseEnd_2828677] using wordTrace_append hprefix tailTrace_2828677
  have hstable : (prefixWord ++ tailWord_2828677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828677).length < 2 ^ (prefixWord ++ tailWord_2828677).sum := by decide
  have hdescent : baseEnd_2828677 < baseStart_2828677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828692 : List Nat := [2, 4, 2, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_2828692 : Nat := 118140960795 + 2828692 * 2 ^ 59
def prefixEnd_2828692 : Nat := 4983230072969 + 3 ^ 40 * 2828692 * 2
def baseEnd_2828692 : Nat := 1452478619527951963241089

theorem tailTrace_2828692 : CollatzResearch.WordTrace tailWord_2828692 prefixEnd_2828692 1452478619527951963241089 := by
  unfold tailWord_2828692
  simp only [CollatzResearch.WordTrace]
  refine ⟨51585436534069730488492165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68780582045426307317989553 51585436534069730488492165)
  ·
    refine ⟨9672269350138074466592281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51585436534069730488492165 9672269350138074466592281)
    ·
      refine ⟨7254202012603555849944211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9672269350138074466592281 7254202012603555849944211)
      ·
        refine ⟨10881303018905333774916317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7254202012603555849944211 10881303018905333774916317)
        ·
          refine ⟨4080488632089500165593619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10881303018905333774916317 4080488632089500165593619)
          ·
            refine ⟨6120732948134250248390429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4080488632089500165593619 6120732948134250248390429)
            ·
              refine ⟨2295274855550343843146411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6120732948134250248390429 2295274855550343843146411)
              ·
                refine ⟨3442912283325515764719617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2295274855550343843146411 3442912283325515764719617)
                ·
                  refine ⟨2582184212494136823539713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3442912283325515764719617 2582184212494136823539713)
                  ·
                    refine ⟨1936638159370602617654785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2582184212494136823539713 1936638159370602617654785)
                    ·
                      refine ⟨1452478619527951963241089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1936638159370602617654785 1452478619527951963241089)
                      ·
                        rfl

theorem cell23_2828692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_2828692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828692 prefixEnd_2828692 := by exact prefixLift 2828692
  have htrace : WordTrace (prefixWord ++ tailWord_2828692) baseStart_2828692 baseEnd_2828692 := by
    simpa [prefixWord, tailWord_2828692, baseEnd_2828692] using wordTrace_append hprefix tailTrace_2828692
  have hstable : (prefixWord ++ tailWord_2828692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828692).length < 2 ^ (prefixWord ++ tailWord_2828692).sum := by decide
  have hdescent : baseEnd_2828692 < baseStart_2828692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828697 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 3, 3, 4]
def baseStart_2828697 : Nat := 118140960795 + 2828697 * 2 ^ 59
def prefixEnd_2828697 : Nat := 4983230072969 + 3 ^ 40 * 2828697 * 2
def baseEnd_2828697 : Nat := 1452481186931224443678565

theorem tailTrace_2828697 : CollatzResearch.WordTrace tailWord_2828697 prefixEnd_2828697 1452481186931224443678565 := by
  unfold tailWord_2828697
  simp only [CollatzResearch.WordTrace]
  refine ⟨103171055433121346830916345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68780703622080897887277563 103171055433121346830916345)
  ·
    refine ⟨77378291574841010123187259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103171055433121346830916345 77378291574841010123187259)
    ·
      refine ⟨116067437362261515184780889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77378291574841010123187259 116067437362261515184780889)
      ·
        refine ⟨87050578021696136388585667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116067437362261515184780889 87050578021696136388585667)
        ·
          refine ⟨130575867032544204582878501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87050578021696136388585667 130575867032544204582878501)
          ·
            refine ⟨24482975068602038359289719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130575867032544204582878501 24482975068602038359289719)
            ·
              refine ⟨36724462602903057538934579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24482975068602038359289719 36724462602903057538934579)
              ·
                refine ⟨55086693904354586308401869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36724462602903057538934579 55086693904354586308401869)
                ·
                  refine ⟨20657510214132969865650701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55086693904354586308401869 20657510214132969865650701)
                  ·
                    refine ⟨7746566330299863699619013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20657510214132969865650701 7746566330299863699619013)
                    ·
                      refine ⟨1452481186931224443678565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7746566330299863699619013 1452481186931224443678565)
                      ·
                        rfl

theorem cell23_2828697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_2828697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828697 prefixEnd_2828697 := by exact prefixLift 2828697
  have htrace : WordTrace (prefixWord ++ tailWord_2828697) baseStart_2828697 baseEnd_2828697 := by
    simpa [prefixWord, tailWord_2828697, baseEnd_2828697] using wordTrace_append hprefix tailTrace_2828697
  have hstable : (prefixWord ++ tailWord_2828697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828697).length < 2 ^ (prefixWord ++ tailWord_2828697).sum := by decide
  have hdescent : baseEnd_2828697 < baseStart_2828697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828777 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 2, 4, 5]
def baseStart_2828777 : Nat := 118140960795 + 2828777 * 2 ^ 59
def prefixEnd_2828777 : Nat := 4983230072969 + 3 ^ 40 * 2828777 * 2
def baseEnd_2828777 : Nat := 1452522265383584130678197

theorem tailTrace_2828777 : CollatzResearch.WordTrace tailWord_2828777 prefixEnd_2828777 1452522265383584130678197 := by
  unfold tailWord_2828777
  simp only [CollatzResearch.WordTrace]
  refine ⟨103173973272831520493828585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68782648848554346995885723 103173973272831520493828585)
  ·
    refine ⟨77380479954623640370371439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103173973272831520493828585 77380479954623640370371439)
    ·
      refine ⟨116070719931935460555557159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77380479954623640370371439 116070719931935460555557159)
      ·
        refine ⟨174106079897903190833335739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116070719931935460555557159 174106079897903190833335739)
        ·
          refine ⟨261159119846854786250003609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174106079897903190833335739 261159119846854786250003609)
          ·
            refine ⟨195869339885141089687502707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261159119846854786250003609 195869339885141089687502707)
            ·
              refine ⟨293804009827711634531254061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195869339885141089687502707 293804009827711634531254061)
              ·
                refine ⟨110176503685391862949220273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293804009827711634531254061 110176503685391862949220273)
                ·
                  refine ⟨82632377764043897211915205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110176503685391862949220273 82632377764043897211915205)
                  ·
                    refine ⟨15493570830758230727234101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82632377764043897211915205 15493570830758230727234101)
                    ·
                      refine ⟨1452522265383584130678197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15493570830758230727234101 1452522265383584130678197)
                      ·
                        rfl

theorem cell23_2828777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_2828777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828777 prefixEnd_2828777 := by exact prefixLift 2828777
  have htrace : WordTrace (prefixWord ++ tailWord_2828777) baseStart_2828777 baseEnd_2828777 := by
    simpa [prefixWord, tailWord_2828777, baseEnd_2828777] using wordTrace_append hprefix tailTrace_2828777
  have hstable : (prefixWord ++ tailWord_2828777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828777).length < 2 ^ (prefixWord ++ tailWord_2828777).sum := by decide
  have hdescent : baseEnd_2828777 < baseStart_2828777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828821 : List Nat := [1, 3, 2, 1, 3, 1, 2, 4, 1, 1, 4]
def baseStart_2828821 : Nat := 118140960795 + 2828821 * 2 ^ 59
def prefixEnd_2828821 : Nat := 4983230072969 + 3 ^ 40 * 2828821 * 2
def baseEnd_2828821 : Nat := 1452544858532381958527995

theorem tailTrace_2828821 : CollatzResearch.WordTrace tailWord_2828821 prefixEnd_2828821 1452544858532381958527995 := by
  unfold tailWord_2828821
  simp only [CollatzResearch.WordTrace]
  refine ⟨103175578084672116008430317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68783718723114744005620211 103175578084672116008430317)
  ·
    refine ⟨38690841781752043503161369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103175578084672116008430317 38690841781752043503161369)
    ·
      refine ⟨29018131336314032627371027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38690841781752043503161369 29018131336314032627371027)
      ·
        refine ⟨43527197004471048941056541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29018131336314032627371027 43527197004471048941056541)
        ·
          refine ⟨16322698876676643352896203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43527197004471048941056541 16322698876676643352896203)
          ·
            refine ⟨24484048315014965029344305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16322698876676643352896203 24484048315014965029344305)
            ·
              refine ⟨18363036236261223772008229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24484048315014965029344305 18363036236261223772008229)
              ·
                refine ⟨3443069294298979457251543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18363036236261223772008229 3443069294298979457251543)
                ·
                  refine ⟨5164603941448469185877315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3443069294298979457251543 5164603941448469185877315)
                  ·
                    refine ⟨7746905912172703778815973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5164603941448469185877315 7746905912172703778815973)
                    ·
                      refine ⟨1452544858532381958527995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7746905912172703778815973 1452544858532381958527995)
                      ·
                        rfl

theorem cell23_2828821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_2828821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828821 prefixEnd_2828821 := by exact prefixLift 2828821
  have htrace : WordTrace (prefixWord ++ tailWord_2828821) baseStart_2828821 baseEnd_2828821 := by
    simpa [prefixWord, tailWord_2828821, baseEnd_2828821] using wordTrace_append hprefix tailTrace_2828821
  have hstable : (prefixWord ++ tailWord_2828821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828821).length < 2 ^ (prefixWord ++ tailWord_2828821).sum := by decide
  have hdescent : baseEnd_2828821 < baseStart_2828821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828832 : List Nat := [2, 1, 1, 6, 2, 1, 2, 3, 1, 1, 3]
def baseStart_2828832 : Nat := 118140960795 + 2828832 * 2 ^ 59
def prefixEnd_2828832 : Nat := 4983230072969 + 3 ^ 40 * 2828832 * 2
def baseEnd_2828832 : Nat := 1452550506819581415490445

theorem tailTrace_2828832 : CollatzResearch.WordTrace tailWord_2828832 prefixEnd_2828832 1452550506819581415490445 := by
  unfold tailWord_2828832
  simp only [CollatzResearch.WordTrace]
  refine ⟨51587989643816132443540375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68783986191754843258053833 51587989643816132443540375)
  ·
    refine ⟨77381984465724198665310563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51587989643816132443540375 77381984465724198665310563)
    ·
      refine ⟨116072976698586297997965845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77381984465724198665310563 116072976698586297997965845)
      ·
        refine ⟨5440920782746232718654649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 116072976698586297997965845 5440920782746232718654649)
        ·
          refine ⟨4080690587059674538990987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5440920782746232718654649 4080690587059674538990987)
          ·
            refine ⟨6121035880589511808486481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4080690587059674538990987 6121035880589511808486481)
            ·
              refine ⟨4590776910442133856364861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6121035880589511808486481 4590776910442133856364861)
              ·
                refine ⟨1721541341415800196136823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4590776910442133856364861 1721541341415800196136823)
                ·
                  refine ⟨2582312012123700294205235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721541341415800196136823 2582312012123700294205235)
                  ·
                    refine ⟨3873468018185550441307853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2582312012123700294205235 3873468018185550441307853)
                    ·
                      refine ⟨1452550506819581415490445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3873468018185550441307853 1452550506819581415490445)
                      ·
                        rfl

theorem cell23_2828832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_2828832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828832 prefixEnd_2828832 := by exact prefixLift 2828832
  have htrace : WordTrace (prefixWord ++ tailWord_2828832) baseStart_2828832 baseEnd_2828832 := by
    simpa [prefixWord, tailWord_2828832, baseEnd_2828832] using wordTrace_append hprefix tailTrace_2828832
  have hstable : (prefixWord ++ tailWord_2828832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828832).length < 2 ^ (prefixWord ++ tailWord_2828832).sum := by decide
  have hdescent : baseEnd_2828832 < baseStart_2828832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828834 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_2828834 : Nat := 118140960795 + 2828834 * 2 ^ 59
def prefixEnd_2828834 : Nat := 4983230072969 + 3 ^ 40 * 2828834 * 2
def baseEnd_2828834 : Nat := 1452551533780890407665435

theorem tailTrace_2828834 : CollatzResearch.WordTrace tailWord_2828834 prefixEnd_2828834 1452551533780890407665435 := by
  unfold tailWord_2828834
  simp only [CollatzResearch.WordTrace]
  refine ⟨25794013058406254807163389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68784034822416679485769037 25794013058406254807163389)
  ·
    refine ⟨9672754896902345552686271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25794013058406254807163389 9672754896902345552686271)
    ·
      refine ⟨14509132345353518329029407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9672754896902345552686271 14509132345353518329029407)
      ·
        refine ⟨21763698518030277493544111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14509132345353518329029407 21763698518030277493544111)
        ·
          refine ⟨32645547777045416240316167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21763698518030277493544111 32645547777045416240316167)
          ·
            refine ⟨48968321665568124360474251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32645547777045416240316167 48968321665568124360474251)
            ·
              refine ⟨73452482498352186540711377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48968321665568124360474251 73452482498352186540711377)
              ·
                refine ⟨55089361873764139905533533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73452482498352186540711377 55089361873764139905533533)
                ·
                  refine ⟨20658510702661552464575075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55089361873764139905533533 20658510702661552464575075)
                  ·
                    refine ⟨30987766053992328696862613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20658510702661552464575075 30987766053992328696862613)
                    ·
                      refine ⟨1452551533780890407665435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30987766053992328696862613 1452551533780890407665435)
                      ·
                        rfl

theorem cell23_2828834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_2828834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828834 prefixEnd_2828834 := by exact prefixLift 2828834
  have htrace : WordTrace (prefixWord ++ tailWord_2828834) baseStart_2828834 baseEnd_2828834 := by
    simpa [prefixWord, tailWord_2828834, baseEnd_2828834] using wordTrace_append hprefix tailTrace_2828834
  have hstable : (prefixWord ++ tailWord_2828834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828834).length < 2 ^ (prefixWord ++ tailWord_2828834).sum := by decide
  have hdescent : baseEnd_2828834 < baseStart_2828834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828855 : List Nat := [1, 1, 3, 1, 2, 3, 1, 6, 1, 2, 2]
def baseStart_2828855 : Nat := 118140960795 + 2828855 * 2 ^ 59
def prefixEnd_2828855 : Nat := 4983230072969 + 3 ^ 40 * 2828855 * 2
def baseEnd_2828855 : Nat := 1452562316874634825502839

theorem tailTrace_2828855 : CollatzResearch.WordTrace tailWord_2828855 prefixEnd_2828855 1452562316874634825502839 := by
  unfold tailWord_2828855
  simp only [CollatzResearch.WordTrace]
  refine ⟨103176818166548939815168019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68784545444365959876778679 103176818166548939815168019)
  ·
    refine ⟨154765227249823409722752029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103176818166548939815168019 154765227249823409722752029)
    ·
      refine ⟨58036960218683778646032011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154765227249823409722752029 58036960218683778646032011)
      ·
        refine ⟨87055440328025667969048017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58036960218683778646032011 87055440328025667969048017)
        ·
          refine ⟨65291580246019250976786013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87055440328025667969048017 65291580246019250976786013)
          ·
            refine ⟨24484342592257219116294755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65291580246019250976786013 24484342592257219116294755)
            ·
              refine ⟨36726513888385828674442133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24484342592257219116294755 36726513888385828674442133)
              ·
                refine ⟨1721555338518085719114475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36726513888385828674442133 1721555338518085719114475)
                ·
                  refine ⟨2582333007777128578671713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721555338518085719114475 2582333007777128578671713)
                  ·
                    refine ⟨1936749755832846434003785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2582333007777128578671713 1936749755832846434003785)
                    ·
                      refine ⟨1452562316874634825502839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1936749755832846434003785 1452562316874634825502839)
                      ·
                        rfl

theorem cell23_2828855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 1, 2, 2].length) (baseStart_2828855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828855 prefixEnd_2828855 := by exact prefixLift 2828855
  have htrace : WordTrace (prefixWord ++ tailWord_2828855) baseStart_2828855 baseEnd_2828855 := by
    simpa [prefixWord, tailWord_2828855, baseEnd_2828855] using wordTrace_append hprefix tailTrace_2828855
  have hstable : (prefixWord ++ tailWord_2828855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828855).length < 2 ^ (prefixWord ++ tailWord_2828855).sum := by decide
  have hdescent : baseEnd_2828855 < baseStart_2828855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828865 : List Nat := [1, 2, 5, 1, 1, 3, 3, 1, 2, 4]
def baseStart_2828865 : Nat := 118140960795 + 2828865 * 2 ^ 59
def prefixEnd_2828865 : Nat := 4983230072969 + 3 ^ 40 * 2828865 * 2
def baseEnd_2828865 : Nat := 484189150560393262125931

theorem tailTrace_2828865 : CollatzResearch.WordTrace tailWord_2828865 prefixEnd_2828865 484189150560393262125931 := by
  unfold tailWord_2828865
  simp only [CollatzResearch.WordTrace]
  refine ⟨103177182896512711523032049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68784788597675141015354699 103177182896512711523032049)
  ·
    refine ⟨77382887172384533642274037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103177182896512711523032049 77382887172384533642274037)
    ·
      refine ⟨7254645672411050028963191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77382887172384533642274037 7254645672411050028963191)
      ·
        refine ⟨10881968508616575043444787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7254645672411050028963191 10881968508616575043444787)
        ·
          refine ⟨16322952762924862565167181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10881968508616575043444787 16322952762924862565167181)
          ·
            refine ⟨6121107286096823461937693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16322952762924862565167181 6121107286096823461937693)
            ·
              refine ⟨2295415232286308798226635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6121107286096823461937693 2295415232286308798226635)
              ·
                refine ⟨3443122848429463197339953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2295415232286308798226635 3443122848429463197339953)
                ·
                  refine ⟨2582342136322097398004965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3443122848429463197339953 2582342136322097398004965)
                  ·
                    refine ⟨484189150560393262125931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2582342136322097398004965 484189150560393262125931)
                    ·
                      rfl

theorem cell23_2828865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_2828865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828865 prefixEnd_2828865 := by exact prefixLift 2828865
  have htrace : WordTrace (prefixWord ++ tailWord_2828865) baseStart_2828865 baseEnd_2828865 := by
    simpa [prefixWord, tailWord_2828865, baseEnd_2828865] using wordTrace_append hprefix tailTrace_2828865
  have hstable : (prefixWord ++ tailWord_2828865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828865).length < 2 ^ (prefixWord ++ tailWord_2828865).sum := by decide
  have hdescent : baseEnd_2828865 < baseStart_2828865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828932 : List Nat := [2, 3, 2, 1, 3, 3, 1, 2, 1, 3, 2]
def baseStart_2828932 : Nat := 118140960795 + 2828932 * 2 ^ 59
def prefixEnd_2828932 : Nat := 4983230072969 + 3 ^ 40 * 2828932 * 2
def baseEnd_2828932 : Nat := 1452601854885031024239985

theorem tailTrace_2828932 : CollatzResearch.WordTrace tailWord_2828932 prefixEnd_2828932 1452601854885031024239985 := by
  unfold tailWord_2828932
  simp only [CollatzResearch.WordTrace]
  refine ⟨51589813293634990982860525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68786417724846654643814033 51589813293634990982860525)
  ·
    refine ⟨19346179985113121618572697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51589813293634990982860525 19346179985113121618572697)
    ·
      refine ⟨14509634988834841213929523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19346179985113121618572697 14509634988834841213929523)
      ·
        refine ⟨21764452483252261820894285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14509634988834841213929523 21764452483252261820894285)
        ·
          refine ⟨8161669681219598182835357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21764452483252261820894285 8161669681219598182835357)
          ·
            refine ⟨3060626130457349318563259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8161669681219598182835357 3060626130457349318563259)
            ·
              refine ⟨4590939195686023977844889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3060626130457349318563259 4590939195686023977844889)
              ·
                refine ⟨3443204396764517983383667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4590939195686023977844889 3443204396764517983383667)
                ·
                  refine ⟨5164806595146776975075501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3443204396764517983383667 5164806595146776975075501)
                  ·
                    refine ⟨1936802473180041365653313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5164806595146776975075501 1936802473180041365653313)
                    ·
                      refine ⟨1452601854885031024239985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1936802473180041365653313 1452601854885031024239985)
                      ·
                        rfl

theorem cell23_2828932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_2828932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828932 prefixEnd_2828932 := by exact prefixLift 2828932
  have htrace : WordTrace (prefixWord ++ tailWord_2828932) baseStart_2828932 baseEnd_2828932 := by
    simpa [prefixWord, tailWord_2828932, baseEnd_2828932] using wordTrace_append hprefix tailTrace_2828932
  have hstable : (prefixWord ++ tailWord_2828932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828932).length < 2 ^ (prefixWord ++ tailWord_2828932).sum := by decide
  have hdescent : baseEnd_2828932 < baseStart_2828932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828948 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2828948 : Nat := 118140960795 + 2828948 * 2 ^ 59
def prefixEnd_2828948 : Nat := 4983230072969 + 3 ^ 40 * 2828948 * 2
def baseEnd_2828948 : Nat := 1452610070575502961639911

theorem tailTrace_2828948 : CollatzResearch.WordTrace tailWord_2828948 prefixEnd_2828948 1452610070575502961639911 := by
  unfold tailWord_2828948
  simp only [CollatzResearch.WordTrace]
  refine ⟨51590105077606008349151749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68786806770141344465535665 51590105077606008349151749)
  ·
    refine ⟨9673144702051126565465953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51590105077606008349151749 9673144702051126565465953)
    ·
      refine ⟨7254858526538344924099465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9673144702051126565465953 7254858526538344924099465)
      ·
        refine ⟨5441143894903758693074599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7254858526538344924099465 5441143894903758693074599)
        ·
          refine ⟨8161715842355638039611899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5441143894903758693074599 8161715842355638039611899)
          ·
            refine ⟨12242573763533457059417849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8161715842355638039611899 12242573763533457059417849)
            ·
              refine ⟨9181930322650092794563387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12242573763533457059417849 9181930322650092794563387)
              ·
                refine ⟨13772895483975139191845081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9181930322650092794563387 13772895483975139191845081)
                ·
                  refine ⟨10329671612981354393883811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13772895483975139191845081 10329671612981354393883811)
                  ·
                    refine ⟨15494507419472031590825717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10329671612981354393883811 15494507419472031590825717)
                    ·
                      refine ⟨1452610070575502961639911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15494507419472031590825717 1452610070575502961639911)
                      ·
                        rfl

theorem cell23_2828948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2828948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828948 prefixEnd_2828948 := by exact prefixLift 2828948
  have htrace : WordTrace (prefixWord ++ tailWord_2828948) baseStart_2828948 baseEnd_2828948 := by
    simpa [prefixWord, tailWord_2828948, baseEnd_2828948] using wordTrace_append hprefix tailTrace_2828948
  have hstable : (prefixWord ++ tailWord_2828948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828948).length < 2 ^ (prefixWord ++ tailWord_2828948).sum := by decide
  have hdescent : baseEnd_2828948 < baseStart_2828948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828958 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_2828958 : Nat := 118140960795 + 2828958 * 2 ^ 59
def prefixEnd_2828958 : Nat := 4983230072969 + 3 ^ 40 * 2828958 * 2
def baseEnd_2828958 : Nat := 1452615205382047922514865

theorem tailTrace_2828958 : CollatzResearch.WordTrace tailWord_2828958 prefixEnd_2828958 1452615205382047922514865 := by
  unfold tailWord_2828958
  simp only [CollatzResearch.WordTrace]
  refine ⟨12897571860646973550770941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68787049923450525604111685 12897571860646973550770941)
  ·
    refine ⟨4836589447742615081539103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12897571860646973550770941 4836589447742615081539103)
    ·
      refine ⟨7254884171613922622308655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4836589447742615081539103 7254884171613922622308655)
      ·
        refine ⟨10882326257420883933462983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7254884171613922622308655 10882326257420883933462983)
        ·
          refine ⟨16323489386131325900194475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10882326257420883933462983 16323489386131325900194475)
          ·
            refine ⟨24485234079196988850291713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16323489386131325900194475 24485234079196988850291713)
            ·
              refine ⟨18363925559397741637718785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24485234079196988850291713 18363925559397741637718785)
              ·
                refine ⟨13772944169548306228289089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18363925559397741637718785 13772944169548306228289089)
                ·
                  refine ⟨10329708127161229671216817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13772944169548306228289089 10329708127161229671216817)
                  ·
                    refine ⟨7747281095370922253412613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10329708127161229671216817 7747281095370922253412613)
                    ·
                      refine ⟨1452615205382047922514865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7747281095370922253412613 1452615205382047922514865)
                      ·
                        rfl

theorem cell23_2828958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_2828958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828958 prefixEnd_2828958 := by exact prefixLift 2828958
  have htrace : WordTrace (prefixWord ++ tailWord_2828958) baseStart_2828958 baseEnd_2828958 := by
    simpa [prefixWord, tailWord_2828958, baseEnd_2828958] using wordTrace_append hprefix tailTrace_2828958
  have hstable : (prefixWord ++ tailWord_2828958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828958).length < 2 ^ (prefixWord ++ tailWord_2828958).sum := by decide
  have hdescent : baseEnd_2828958 < baseStart_2828958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828988 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 2, 5, 2]
def baseStart_2828988 : Nat := 118140960795 + 2828988 * 2 ^ 59
def prefixEnd_2828988 : Nat := 4983230072969 + 3 ^ 40 * 2828988 * 2
def baseEnd_2828988 : Nat := 1452630609801682805139727

theorem tailTrace_2828988 : CollatzResearch.WordTrace tailWord_2828988 prefixEnd_2828988 1452630609801682805139727 := by
  unfold tailWord_2828988
  simp only [CollatzResearch.WordTrace]
  refine ⟨51590834537533551764879809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68787779383378069019839745 51590834537533551764879809)
  ·
    refine ⟨38693125903150163823659857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51590834537533551764879809 38693125903150163823659857)
    ·
      refine ⟨29019844427362622867744893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38693125903150163823659857 29019844427362622867744893)
      ·
        refine ⟨10882441660260983575404335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29019844427362622867744893 10882441660260983575404335)
        ·
          refine ⟨16323662490391475363106503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10882441660260983575404335 16323662490391475363106503)
          ·
            refine ⟨24485493735587213044659755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16323662490391475363106503 24485493735587213044659755)
            ·
              refine ⟨36728240603380819566989633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24485493735587213044659755 36728240603380819566989633)
              ·
                refine ⟨27546180452535614675242225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36728240603380819566989633 27546180452535614675242225)
                ·
                  refine ⟨20659635339401711006431669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27546180452535614675242225 20659635339401711006431669)
                  ·
                    refine ⟨1936840813068910406852969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20659635339401711006431669 1936840813068910406852969)
                    ·
                      refine ⟨1452630609801682805139727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1936840813068910406852969 1452630609801682805139727)
                      ·
                        rfl

theorem cell23_2828988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_2828988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2828988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2828988 prefixEnd_2828988 := by exact prefixLift 2828988
  have htrace : WordTrace (prefixWord ++ tailWord_2828988) baseStart_2828988 baseEnd_2828988 := by
    simpa [prefixWord, tailWord_2828988, baseEnd_2828988] using wordTrace_append hprefix tailTrace_2828988
  have hstable : (prefixWord ++ tailWord_2828988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828988).length < 2 ^ (prefixWord ++ tailWord_2828988).sum := by decide
  have hdescent : baseEnd_2828988 < baseStart_2828988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829018 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2]
def baseStart_2829018 : Nat := 118140960795 + 2829018 * 2 ^ 59
def prefixEnd_2829018 : Nat := 4983230072969 + 3 ^ 40 * 2829018 * 2
def baseEnd_2829018 : Nat := 1452646014221317687764589

theorem tailTrace_2829018 : CollatzResearch.WordTrace tailWord_2829018 prefixEnd_2829018 1452646014221317687764589 := by
  unfold tailWord_2829018
  simp only [CollatzResearch.WordTrace]
  refine ⟨25795690816239604663337927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68788508843305612435567805 25795690816239604663337927)
  ·
    refine ⟨38693536224359406995006891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25795690816239604663337927 38693536224359406995006891)
    ·
      refine ⟨58040304336539110492510337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38693536224359406995006891 58040304336539110492510337)
      ·
        refine ⟨43530228252404332869382753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58040304336539110492510337 43530228252404332869382753)
        ·
          refine ⟨32647671189303249652037065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43530228252404332869382753 32647671189303249652037065)
          ·
            refine ⟨24485753391977437239027799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32647671189303249652037065 24485753391977437239027799)
            ·
              refine ⟨36728630087966155858541699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24485753391977437239027799 36728630087966155858541699)
              ·
                refine ⟨55092945131949233787812549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36728630087966155858541699 55092945131949233787812549)
                ·
                  refine ⟨10329927212240481335214853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55092945131949233787812549 10329927212240481335214853)
                  ·
                    refine ⟨1936861352295090250352785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10329927212240481335214853 1936861352295090250352785)
                    ·
                      refine ⟨1452646014221317687764589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1936861352295090250352785 1452646014221317687764589)
                      ·
                        rfl

theorem cell23_2829018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_2829018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829018 prefixEnd_2829018 := by exact prefixLift 2829018
  have htrace : WordTrace (prefixWord ++ tailWord_2829018) baseStart_2829018 baseEnd_2829018 := by
    simpa [prefixWord, tailWord_2829018, baseEnd_2829018] using wordTrace_append hprefix tailTrace_2829018
  have hstable : (prefixWord ++ tailWord_2829018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829018).length < 2 ^ (prefixWord ++ tailWord_2829018).sum := by decide
  have hdescent : baseEnd_2829018 < baseStart_2829018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829028 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 3, 4]
def baseStart_2829028 : Nat := 118140960795 + 2829028 * 2 ^ 59
def prefixEnd_2829028 : Nat := 4983230072969 + 3 ^ 40 * 2829028 * 2
def baseEnd_2829028 : Nat := 484217049675954216213181

theorem tailTrace_2829028 : CollatzResearch.WordTrace tailWord_2829028 prefixEnd_2829028 484217049675954216213181 := by
  unfold tailWord_2829028
  simp only [CollatzResearch.WordTrace]
  refine ⟨51591563997461095180607869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68788751996614793574143825 51591563997461095180607869)
  ·
    refine ⟨19346836499047910692727951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51591563997461095180607869 19346836499047910692727951)
    ·
      refine ⟨29020254748571866039091927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19346836499047910692727951 29020254748571866039091927)
      ·
        refine ⟨43530382122857799058637891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29020254748571866039091927 43530382122857799058637891)
        ·
          refine ⟨65295573184286698587956837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43530382122857799058637891 65295573184286698587956837)
          ·
            refine ⟨12242919972053755985241907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65295573184286698587956837 12242919972053755985241907)
            ·
              refine ⟨18364379958080633977862861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12242919972053755985241907 18364379958080633977862861)
              ·
                refine ⟨6886642484280237741698573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18364379958080633977862861 6886642484280237741698573)
                ·
                  refine ⟨2582490931605089153136965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6886642484280237741698573 2582490931605089153136965)
                  ·
                    refine ⟨484217049675954216213181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2582490931605089153136965 484217049675954216213181)
                    ·
                      rfl

theorem cell23_2829028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_2829028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829028 prefixEnd_2829028 := by exact prefixLift 2829028
  have htrace : WordTrace (prefixWord ++ tailWord_2829028) baseStart_2829028 baseEnd_2829028 := by
    simpa [prefixWord, tailWord_2829028, baseEnd_2829028] using wordTrace_append hprefix tailTrace_2829028
  have hstable : (prefixWord ++ tailWord_2829028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829028).length < 2 ^ (prefixWord ++ tailWord_2829028).sum := by decide
  have hdescent : baseEnd_2829028 < baseStart_2829028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829038 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_2829038 : Nat := 118140960795 + 2829038 * 2 ^ 59
def prefixEnd_2829038 : Nat := 4983230072969 + 3 ^ 40 * 2829038 * 2
def baseEnd_2829038 : Nat := 1452656283834407609514497

theorem tailTrace_2829038 : CollatzResearch.WordTrace tailWord_2829038 prefixEnd_2829038 1452656283834407609514497 := by
  unfold tailWord_2829038
  simp only [CollatzResearch.WordTrace]
  refine ⟨12897936590610745258634971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68788995149923974712719845 12897936590610745258634971)
  ·
    refine ⟨19346904885916117887952457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12897936590610745258634971 19346904885916117887952457)
    ·
      refine ⟨14510178664437088415964343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19346904885916117887952457 14510178664437088415964343)
      ·
        refine ⟨21765267996655632623946515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14510178664437088415964343 21765267996655632623946515)
        ·
          refine ⟨32647901994983448935919773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21765267996655632623946515 32647901994983448935919773)
          ·
            refine ⟨12242963248118793350969915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32647901994983448935919773 12242963248118793350969915)
            ·
              refine ⟨18364444872178190026454873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12242963248118793350969915 18364444872178190026454873)
              ·
                refine ⟨13773333654133642519841155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18364444872178190026454873 13773333654133642519841155)
                ·
                  refine ⟨20660000481200463779761733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13773333654133642519841155 20660000481200463779761733)
                  ·
                    refine ⟨3873750090225086958705325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20660000481200463779761733 3873750090225086958705325)
                    ·
                      refine ⟨1452656283834407609514497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3873750090225086958705325 1452656283834407609514497)
                      ·
                        rfl

theorem cell23_2829038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_2829038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829038 prefixEnd_2829038 := by exact prefixLift 2829038
  have htrace : WordTrace (prefixWord ++ tailWord_2829038) baseStart_2829038 baseEnd_2829038 := by
    simpa [prefixWord, tailWord_2829038, baseEnd_2829038] using wordTrace_append hprefix tailTrace_2829038
  have hstable : (prefixWord ++ tailWord_2829038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829038).length < 2 ^ (prefixWord ++ tailWord_2829038).sum := by decide
  have hdescent : baseEnd_2829038 < baseStart_2829038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829058 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 8]
def baseStart_2829058 : Nat := 118140960795 + 2829058 * 2 ^ 59
def prefixEnd_2829058 : Nat := 4983230072969 + 3 ^ 40 * 2829058 * 2
def baseEnd_2829058 : Nat := 161407394827499725696045

theorem tailTrace_2829058 : CollatzResearch.WordTrace tailWord_2829058 prefixEnd_2829058 161407394827499725696045 := by
  unfold tailWord_2829058
  simp only [CollatzResearch.WordTrace]
  refine ⟨25796055546203376371201957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68789481456542336989871885 25796055546203376371201957)
  ·
    refine ⟨4836760414913133069600367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25796055546203376371201957 4836760414913133069600367)
    ·
      refine ⟨7255140622369699604400551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4836760414913133069600367 7255140622369699604400551)
      ·
        refine ⟨10882710933554549406600827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7255140622369699604400551 10882710933554549406600827)
        ·
          refine ⟨16324066400331824109901241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10882710933554549406600827 16324066400331824109901241)
          ·
            refine ⟨12243049800248868082425931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16324066400331824109901241 12243049800248868082425931)
            ·
              refine ⟨18364574700373302123638897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12243049800248868082425931 18364574700373302123638897)
              ·
                refine ⟨13773431025279976592729173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18364574700373302123638897 13773431025279976592729173)
                ·
                  refine ⟨161407394827499725696045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13773431025279976592729173 161407394827499725696045)
                  ·
                    rfl

theorem cell23_2829058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_2829058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829058 prefixEnd_2829058 := by exact prefixLift 2829058
  have htrace : WordTrace (prefixWord ++ tailWord_2829058) baseStart_2829058 baseEnd_2829058 := by
    simpa [prefixWord, tailWord_2829058, baseEnd_2829058] using wordTrace_append hprefix tailTrace_2829058
  have hstable : (prefixWord ++ tailWord_2829058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829058).length < 2 ^ (prefixWord ++ tailWord_2829058).sum := by decide
  have hdescent : baseEnd_2829058 < baseStart_2829058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829079 : List Nat := [1, 1, 3, 4, 3, 1, 3, 2, 1, 4]
def baseStart_2829079 : Nat := 118140960795 + 2829079 * 2 ^ 59
def prefixEnd_2829079 : Nat := 4983230072969 + 3 ^ 40 * 2829079 * 2
def baseEnd_2829079 : Nat := 484225778847080649700603

theorem tailTrace_2829079 : CollatzResearch.WordTrace tailWord_2829079 prefixEnd_2829079 484225778847080649700603 := by
  unfold tailWord_2829079
  simp only [CollatzResearch.WordTrace]
  refine ⟨103184988117737426071322291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68789992078491617380881527 103184988117737426071322291)
  ·
    refine ⟨154777482176606139106983437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103184988117737426071322291 154777482176606139106983437)
    ·
      refine ⟨58041555816227302165118789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154777482176606139106983437 58041555816227302165118789)
      ·
        refine ⟨10882791715542619155959773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58041555816227302165118789 10882791715542619155959773)
        ·
          refine ⟨4081046893328482183484915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10882791715542619155959773 4081046893328482183484915)
          ·
            refine ⟨6121570339992723275227373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4081046893328482183484915 6121570339992723275227373)
            ·
              refine ⟨2295588877497271228210265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6121570339992723275227373 2295588877497271228210265)
              ·
                refine ⟨1721691658122953421157699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2295588877497271228210265 1721691658122953421157699)
                ·
                  refine ⟨2582537487184430131736549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721691658122953421157699 2582537487184430131736549)
                  ·
                    refine ⟨484225778847080649700603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2582537487184430131736549 484225778847080649700603)
                    ·
                      rfl

theorem cell23_2829079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 1, 4].length) (baseStart_2829079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829079 prefixEnd_2829079 := by exact prefixLift 2829079
  have htrace : WordTrace (prefixWord ++ tailWord_2829079) baseStart_2829079 baseEnd_2829079 := by
    simpa [prefixWord, tailWord_2829079, baseEnd_2829079] using wordTrace_append hprefix tailTrace_2829079
  have hstable : (prefixWord ++ tailWord_2829079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829079).length < 2 ^ (prefixWord ++ tailWord_2829079).sum := by decide
  have hdescent : baseEnd_2829079 < baseStart_2829079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829091 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 4]
def baseStart_2829091 : Nat := 118140960795 + 2829091 * 2 ^ 59
def prefixEnd_2829091 : Nat := 4983230072969 + 3 ^ 40 * 2829091 * 2
def baseEnd_2829091 : Nat := 1452683498309095902151753

theorem tailTrace_2829091 : CollatzResearch.WordTrace tailWord_2829091 prefixEnd_2829091 1452683498309095902151753 := by
  unfold tailWord_2829091
  simp only [CollatzResearch.WordTrace]
  refine ⟨103185425793693952120759127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68790283862462634747172751 103185425793693952120759127)
  ·
    refine ⟨154778138690540928181138691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103185425793693952120759127 154778138690540928181138691)
    ·
      refine ⟨232167208035811392271708037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154778138690540928181138691 232167208035811392271708037)
      ·
        refine ⟨43531351506714636050945257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232167208035811392271708037 43531351506714636050945257)
        ·
          refine ⟨32648513630035977038208943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43531351506714636050945257 32648513630035977038208943)
          ·
            refine ⟨48972770445053965557313415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32648513630035977038208943 48972770445053965557313415)
            ·
              refine ⟨73459155667580948335970123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48972770445053965557313415 73459155667580948335970123)
              ·
                refine ⟨110188733501371422503955185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73459155667580948335970123 110188733501371422503955185)
                ·
                  refine ⟨82641550126028566877966389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110188733501371422503955185 82641550126028566877966389)
                  ·
                    refine ⟨7747645324315178144809349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82641550126028566877966389 7747645324315178144809349)
                    ·
                      refine ⟨1452683498309095902151753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7747645324315178144809349 1452683498309095902151753)
                      ·
                        rfl

theorem cell23_2829091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_2829091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829091 prefixEnd_2829091 := by exact prefixLift 2829091
  have htrace : WordTrace (prefixWord ++ tailWord_2829091) baseStart_2829091 baseEnd_2829091 := by
    simpa [prefixWord, tailWord_2829091, baseEnd_2829091] using wordTrace_append hprefix tailTrace_2829091
  have hstable : (prefixWord ++ tailWord_2829091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829091).length < 2 ^ (prefixWord ++ tailWord_2829091).sum := by decide
  have hdescent : baseEnd_2829091 < baseStart_2829091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829092 : List Nat := [2, 3, 1, 3, 3, 2, 2, 1, 6]
def baseStart_2829092 : Nat := 118140960795 + 2829092 * 2 ^ 59
def prefixEnd_2829092 : Nat := 4983230072969 + 3 ^ 40 * 2829092 * 2
def baseEnd_2829092 : Nat := 161409334643305599804361

theorem tailTrace_2829092 : CollatzResearch.WordTrace tailWord_2829092 prefixEnd_2829092 161409334643305599804361 := by
  unfold tailWord_2829092
  simp only [CollatzResearch.WordTrace]
  refine ⟨51592731133345164645772765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68790308177793552861030353 51592731133345164645772765)
  ·
    refine ⟨19347274175004436742164787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51592731133345164645772765 19347274175004436742164787)
    ·
      refine ⟨29020911262506655113247181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19347274175004436742164787 29020911262506655113247181)
      ·
        refine ⟨10882841723439995667467693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29020911262506655113247181 10882841723439995667467693)
        ·
          refine ⟨4081065646289998375300385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10882841723439995667467693 4081065646289998375300385)
          ·
            refine ⟨3060799234717498781475289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4081065646289998375300385 3060799234717498781475289)
            ·
              refine ⟨2295599426038124086106467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3060799234717498781475289 2295599426038124086106467)
              ·
                refine ⟨3443399139057186129159701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2295599426038124086106467 3443399139057186129159701)
                ·
                  refine ⟨161409334643305599804361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3443399139057186129159701 161409334643305599804361)
                  ·
                    rfl

theorem cell23_2829092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_2829092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829092 prefixEnd_2829092 := by exact prefixLift 2829092
  have htrace : WordTrace (prefixWord ++ tailWord_2829092) baseStart_2829092 baseEnd_2829092 := by
    simpa [prefixWord, tailWord_2829092, baseEnd_2829092] using wordTrace_append hprefix tailTrace_2829092
  have hstable : (prefixWord ++ tailWord_2829092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829092).length < 2 ^ (prefixWord ++ tailWord_2829092).sum := by decide
  have hdescent : baseEnd_2829092 < baseStart_2829092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829125 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 7, 2, 2]
def baseStart_2829125 : Nat := 118140960795 + 2829125 * 2 ^ 59
def prefixEnd_2829125 : Nat := 4983230072969 + 3 ^ 40 * 2829125 * 2
def baseEnd_2829125 : Nat := 1452700956651348769126597

theorem tailTrace_2829125 : CollatzResearch.WordTrace tailWord_2829125 prefixEnd_2829125 1452700956651348769126597 := by
  unfold tailWord_2829125
  simp only [CollatzResearch.WordTrace]
  refine ⟨103186665875570775927496829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68791110583713850618331219 103186665875570775927496829)
  ·
    refine ⟨38694999703339040972811311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103186665875570775927496829 38694999703339040972811311)
    ·
      refine ⟨58042499555008561459216967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38694999703339040972811311 58042499555008561459216967)
      ·
        refine ⟨87063749332512842188825451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58042499555008561459216967 87063749332512842188825451)
        ·
          refine ⟨130595623998769263283238177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87063749332512842188825451 130595623998769263283238177)
          ·
            refine ⟨97946717999076947462428633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130595623998769263283238177 97946717999076947462428633)
            ·
              refine ⟨73460038499307710596821475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97946717999076947462428633 73460038499307710596821475)
              ·
                refine ⟨110190057748961565895232213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73460038499307710596821475 110190057748961565895232213)
                ·
                  refine ⟨2582579478491286700669505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 110190057748961565895232213 2582579478491286700669505)
                  ·
                    refine ⟨1936934608868465025502129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2582579478491286700669505 1936934608868465025502129)
                    ·
                      refine ⟨1452700956651348769126597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1936934608868465025502129 1452700956651348769126597)
                      ·
                        rfl

theorem cell23_2829125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 2, 2].length) (baseStart_2829125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829125 prefixEnd_2829125 := by exact prefixLift 2829125
  have htrace : WordTrace (prefixWord ++ tailWord_2829125) baseStart_2829125 baseEnd_2829125 := by
    simpa [prefixWord, tailWord_2829125, baseEnd_2829125] using wordTrace_append hprefix tailTrace_2829125
  have hstable : (prefixWord ++ tailWord_2829125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829125).length < 2 ^ (prefixWord ++ tailWord_2829125).sum := by decide
  have hdescent : baseEnd_2829125 < baseStart_2829125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829138 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_2829138 : Nat := 118140960795 + 2829138 * 2 ^ 59
def prefixEnd_2829138 : Nat := 4983230072969 + 3 ^ 40 * 2829138 * 2
def baseEnd_2829138 : Nat := 1452707631899857218264037

theorem tailTrace_2829138 : CollatzResearch.WordTrace tailWord_2829138 prefixEnd_2829138 1452707631899857218264037 := by
  unfold tailWord_2829138
  simp only [CollatzResearch.WordTrace]
  refine ⟨25796785006130919786930017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68791426683015786098480045 25796785006130919786930017)
  ·
    refine ⟨19347588754598189840197513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25796785006130919786930017 19347588754598189840197513)
    ·
      refine ⟨14510691565948642380148135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19347588754598189840197513 14510691565948642380148135)
      ·
        refine ⟨21766037348922963570222203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14510691565948642380148135 21766037348922963570222203)
        ·
          refine ⟨32649056023384445355333305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21766037348922963570222203 32649056023384445355333305)
          ·
            refine ⟨24486792017538334016499979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32649056023384445355333305 24486792017538334016499979)
            ·
              refine ⟨36730188026307501024749969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24486792017538334016499979 36730188026307501024749969)
              ·
                refine ⟨27547641019730625768562477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36730188026307501024749969 27547641019730625768562477)
                ·
                  refine ⟨10330365382398984663210929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27547641019730625768562477 10330365382398984663210929)
                  ·
                    refine ⟨7747774036799238497408197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10330365382398984663210929 7747774036799238497408197)
                    ·
                      refine ⟨1452707631899857218264037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7747774036799238497408197 1452707631899857218264037)
                      ·
                        rfl

theorem cell23_2829138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_2829138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829138 prefixEnd_2829138 := by exact prefixLift 2829138
  have htrace : WordTrace (prefixWord ++ tailWord_2829138) baseStart_2829138 baseEnd_2829138 := by
    simpa [prefixWord, tailWord_2829138, baseEnd_2829138] using wordTrace_append hprefix tailTrace_2829138
  have hstable : (prefixWord ++ tailWord_2829138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829138).length < 2 ^ (prefixWord ++ tailWord_2829138).sum := by decide
  have hdescent : baseEnd_2829138 < baseStart_2829138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829155 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 4]
def baseStart_2829155 : Nat := 118140960795 + 2829155 * 2 ^ 59
def prefixEnd_2829155 : Nat := 4983230072969 + 3 ^ 40 * 2829155 * 2
def baseEnd_2829155 : Nat := 1452716361070983651751459

theorem tailTrace_2829155 : CollatzResearch.WordTrace tailWord_2829155 prefixEnd_2829155 1452716361070983651751459 := by
  unfold tailWord_2829155
  simp only [CollatzResearch.WordTrace]
  refine ⟨103187760065462091051088919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68791840043641394034059279 103187760065462091051088919)
  ·
    refine ⟨154781640098193136576633379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103187760065462091051088919 154781640098193136576633379)
    ·
      refine ⟨232172460147289704864950069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154781640098193136576633379 232172460147289704864950069)
      ·
        refine ⟨21766168138808409831089069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 232172460147289704864950069 21766168138808409831089069)
        ·
          refine ⟨8162313052053153686658401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21766168138808409831089069 8162313052053153686658401)
          ·
            refine ⟨6121734789039865264993801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8162313052053153686658401 6121734789039865264993801)
            ·
              refine ⟨4591301091779898948745351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6121734789039865264993801 4591301091779898948745351)
              ·
                refine ⟨6886951637669848423118027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4591301091779898948745351 6886951637669848423118027)
                ·
                  refine ⟨10330427456504772634677041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6886951637669848423118027 10330427456504772634677041)
                  ·
                    refine ⟨7747820592378579476007781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10330427456504772634677041 7747820592378579476007781)
                    ·
                      refine ⟨1452716361070983651751459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7747820592378579476007781 1452716361070983651751459)
                      ·
                        rfl

theorem cell23_2829155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_2829155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829155 prefixEnd_2829155 := by exact prefixLift 2829155
  have htrace : WordTrace (prefixWord ++ tailWord_2829155) baseStart_2829155 baseEnd_2829155 := by
    simpa [prefixWord, tailWord_2829155, baseEnd_2829155] using wordTrace_append hprefix tailTrace_2829155
  have hstable : (prefixWord ++ tailWord_2829155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829155).length < 2 ^ (prefixWord ++ tailWord_2829155).sum := by decide
  have hdescent : baseEnd_2829155 < baseStart_2829155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829192 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 4, 1, 3]
def baseStart_2829192 : Nat := 118140960795 + 2829192 * 2 ^ 59
def prefixEnd_2829192 : Nat := 4983230072969 + 3 ^ 40 * 2829192 * 2
def baseEnd_2829192 : Nat := 1452735359855200006988789

theorem tailTrace_2829192 : CollatzResearch.WordTrace tailWord_2829192 prefixEnd_2829192 1452735359855200006988789 := by
  unfold tailWord_2829192
  simp only [CollatzResearch.WordTrace]
  refine ⟨51594554783164023185092915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68792739710885364246790553 51594554783164023185092915)
  ·
    refine ⟨77391832174746034777639373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51594554783164023185092915 77391832174746034777639373)
    ·
      refine ⟨29021937065529763041614765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77391832174746034777639373 29021937065529763041614765)
      ·
        refine ⟨10883226399573661140605537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29021937065529763041614765 10883226399573661140605537)
        ·
          refine ⟨8162419799680245855454153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10883226399573661140605537 8162419799680245855454153)
          ·
            refine ⟨6121814849760184391590615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8162419799680245855454153 6121814849760184391590615)
            ·
              refine ⟨9182722274640276587385923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6121814849760184391590615 9182722274640276587385923)
              ·
                refine ⟨13774083411960414881078885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9182722274640276587385923 13774083411960414881078885)
                ·
                  refine ⟨2582640639742577790202291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13774083411960414881078885 2582640639742577790202291)
                  ·
                    refine ⟨3873960959613866685303437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2582640639742577790202291 3873960959613866685303437)
                    ·
                      refine ⟨1452735359855200006988789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3873960959613866685303437 1452735359855200006988789)
                      ·
                        rfl

theorem cell23_2829192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_2829192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829192 prefixEnd_2829192 := by exact prefixLift 2829192
  have htrace : WordTrace (prefixWord ++ tailWord_2829192) baseStart_2829192 baseEnd_2829192 := by
    simpa [prefixWord, tailWord_2829192, baseEnd_2829192] using wordTrace_append hprefix tailTrace_2829192
  have hstable : (prefixWord ++ tailWord_2829192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829192).length < 2 ^ (prefixWord ++ tailWord_2829192).sum := by decide
  have hdescent : baseEnd_2829192 < baseStart_2829192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829206 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2829206 : Nat := 118140960795 + 2829206 * 2 ^ 59
def prefixEnd_2829206 : Nat := 4983230072969 + 3 ^ 40 * 2829206 * 2
def baseEnd_2829206 : Nat := 1452742548584362952213725

theorem tailTrace_2829206 : CollatzResearch.WordTrace tailWord_2829206 prefixEnd_2829206 1452742548584362952213725 := by
  unfold tailWord_2829206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6449351261767332922574717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68793080125518217840796981 6449351261767332922574717)
  ·
    refine ⟨2418506723162749845965519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6449351261767332922574717 2418506723162749845965519)
    ·
      refine ⟨3627760084744124768948279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2418506723162749845965519 3627760084744124768948279)
      ·
        refine ⟨5441640127116187153422419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3627760084744124768948279 5441640127116187153422419)
        ·
          refine ⟨8162460190674280730133629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5441640127116187153422419 8162460190674280730133629)
          ·
            refine ⟨3060922571502855273800111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8162460190674280730133629 3060922571502855273800111)
            ·
              refine ⟨4591383857254282910700167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3060922571502855273800111 4591383857254282910700167)
              ·
                refine ⟨6887075785881424366050251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4591383857254282910700167 6887075785881424366050251)
                ·
                  refine ⟨10330613678822136549075377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6887075785881424366050251 10330613678822136549075377)
                  ·
                    refine ⟨7747960259116602411806533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10330613678822136549075377 7747960259116602411806533)
                    ·
                      refine ⟨1452742548584362952213725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7747960259116602411806533 1452742548584362952213725)
                      ·
                        rfl

theorem cell23_2829206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2829206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829206 prefixEnd_2829206 := by exact prefixLift 2829206
  have htrace : WordTrace (prefixWord ++ tailWord_2829206) baseStart_2829206 baseEnd_2829206 := by
    simpa [prefixWord, tailWord_2829206, baseEnd_2829206] using wordTrace_append hprefix tailTrace_2829206
  have hstable : (prefixWord ++ tailWord_2829206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829206).length < 2 ^ (prefixWord ++ tailWord_2829206).sum := by decide
  have hdescent : baseEnd_2829206 < baseStart_2829206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829236 : List Nat := [2, 5, 2, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_2829236 : Nat := 118140960795 + 2829236 * 2 ^ 59
def prefixEnd_2829236 : Nat := 4983230072969 + 3 ^ 40 * 2829236 * 2
def baseEnd_2829236 : Nat := 1452757953003997834838587

theorem tailTrace_2829236 : CollatzResearch.WordTrace tailWord_2829236 prefixEnd_2829236 1452757953003997834838587 := by
  unfold tailWord_2829236
  simp only [CollatzResearch.WordTrace]
  refine ⟨51595357189084320942393781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68793809585445761256525041 51595357189084320942393781)
  ·
    refine ⟨4837064736476655088349417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51595357189084320942393781 4837064736476655088349417)
    ·
      refine ⟨3627798552357491316262063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4837064736476655088349417 3627798552357491316262063)
      ·
        refine ⟨5441697828536236974393095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3627798552357491316262063 5441697828536236974393095)
        ·
          refine ⟨8162546742804355461589643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5441697828536236974393095 8162546742804355461589643)
          ·
            refine ⟨12243820114206533192384465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8162546742804355461589643 12243820114206533192384465)
            ·
              refine ⟨9182865085654899894288349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12243820114206533192384465 9182865085654899894288349)
              ·
                refine ⟨3443574407120587460358131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9182865085654899894288349 3443574407120587460358131)
                ·
                  refine ⟨5165361610680881190537197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3443574407120587460358131 5165361610680881190537197)
                  ·
                    refine ⟨1937010604005330446451449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5165361610680881190537197 1937010604005330446451449)
                    ·
                      refine ⟨1452757953003997834838587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1937010604005330446451449 1452757953003997834838587)
                      ·
                        rfl

theorem cell23_2829236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_2829236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829236 prefixEnd_2829236 := by exact prefixLift 2829236
  have htrace : WordTrace (prefixWord ++ tailWord_2829236) baseStart_2829236 baseEnd_2829236 := by
    simpa [prefixWord, tailWord_2829236, baseEnd_2829236] using wordTrace_append hprefix tailTrace_2829236
  have hstable : (prefixWord ++ tailWord_2829236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829236).length < 2 ^ (prefixWord ++ tailWord_2829236).sum := by decide
  have hdescent : baseEnd_2829236 < baseStart_2829236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829255 : List Nat := [1, 1, 4, 1, 1, 2, 2, 6, 5]
def baseStart_2829255 : Nat := 118140960795 + 2829255 * 2 ^ 59
def prefixEnd_2829255 : Nat := 4983230072969 + 3 ^ 40 * 2829255 * 2
def baseEnd_2829255 : Nat := 161418634348492584500111

theorem tailTrace_2829255 : CollatzResearch.WordTrace tailWord_2829255 prefixEnd_2829255 161418634348492584500111 := by
  unfold tailWord_2829255
  simp only [CollatzResearch.WordTrace]
  refine ⟨103191407365099808129729219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68794271576733205419819479 103191407365099808129729219)
  ·
    refine ⟨154787111047649712194593829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103191407365099808129729219 154787111047649712194593829)
    ·
      refine ⟨29022583321434321036486343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154787111047649712194593829 29022583321434321036486343)
      ·
        refine ⟨43533874982151481554729515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29022583321434321036486343 43533874982151481554729515)
        ·
          refine ⟨65300812473227222332094273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43533874982151481554729515 65300812473227222332094273)
          ·
            refine ⟨48975609354920416749070705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65300812473227222332094273 48975609354920416749070705)
            ·
              refine ⟨36731707016190312561803029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48975609354920416749070705 36731707016190312561803029)
              ·
                refine ⟨1721798766383920901334517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36731707016190312561803029 1721798766383920901334517)
                ·
                  refine ⟨161418634348492584500111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1721798766383920901334517 161418634348492584500111)
                  ·
                    rfl

theorem cell23_2829255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 6, 5].length) (baseStart_2829255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829255 prefixEnd_2829255 := by exact prefixLift 2829255
  have htrace : WordTrace (prefixWord ++ tailWord_2829255) baseStart_2829255 baseEnd_2829255 := by
    simpa [prefixWord, tailWord_2829255, baseEnd_2829255] using wordTrace_append hprefix tailTrace_2829255
  have hstable : (prefixWord ++ tailWord_2829255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829255).length < 2 ^ (prefixWord ++ tailWord_2829255).sum := by decide
  have hdescent : baseEnd_2829255 < baseStart_2829255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829266 : List Nat := [3, 2, 2, 3, 1, 2, 1, 3, 2, 2, 2]
def baseStart_2829266 : Nat := 118140960795 + 2829266 * 2 ^ 59
def prefixEnd_2829266 : Nat := 4983230072969 + 3 ^ 40 * 2829266 * 2
def baseEnd_2829266 : Nat := 1452773357423632717463449

theorem tailTrace_2829266 : CollatzResearch.WordTrace tailWord_2829266 prefixEnd_2829266 1452773357423632717463449 := by
  unfold tailWord_2829266
  simp only [CollatzResearch.WordTrace]
  refine ⟨25797952142014989252094913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68794539045373304672253101 25797952142014989252094913)
  ·
    refine ⟨19348464106511241939071185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25797952142014989252094913 19348464106511241939071185)
    ·
      refine ⟨14511348079883431454303389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19348464106511241939071185 14511348079883431454303389)
      ·
        refine ⟨5441755529956286795363771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14511348079883431454303389 5441755529956286795363771)
        ·
          refine ⟨8162633294934430193045657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5441755529956286795363771 8162633294934430193045657)
          ·
            refine ⟨6121974971200822644784243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8162633294934430193045657 6121974971200822644784243)
            ·
              refine ⟨9182962456801233967176365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6121974971200822644784243 9182962456801233967176365)
              ·
                refine ⟨3443610921300462737691137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9182962456801233967176365 3443610921300462737691137)
                ·
                  refine ⟨2582708190975347053268353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3443610921300462737691137 2582708190975347053268353)
                  ·
                    refine ⟨1937031143231510289951265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2582708190975347053268353 1937031143231510289951265)
                    ·
                      refine ⟨1452773357423632717463449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1937031143231510289951265 1452773357423632717463449)
                      ·
                        rfl

theorem cell23_2829266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_2829266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829266 prefixEnd_2829266 := by exact prefixLift 2829266
  have htrace : WordTrace (prefixWord ++ tailWord_2829266) baseStart_2829266 baseEnd_2829266 := by
    simpa [prefixWord, tailWord_2829266, baseEnd_2829266] using wordTrace_append hprefix tailTrace_2829266
  have hstable : (prefixWord ++ tailWord_2829266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829266).length < 2 ^ (prefixWord ++ tailWord_2829266).sum := by decide
  have hdescent : baseEnd_2829266 < baseStart_2829266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829302 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_2829302 : Nat := 118140960795 + 2829302 * 2 ^ 59
def prefixEnd_2829302 : Nat := 4983230072969 + 3 ^ 40 * 2829302 * 2
def baseEnd_2829302 : Nat := 484263947575731525537761

theorem tailTrace_2829302 : CollatzResearch.WordTrace tailWord_2829302 prefixEnd_2829302 484263947575731525537761 := by
  unfold tailWord_2829302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6449570099745595947293135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68795414397286356771126773 6449570099745595947293135)
  ·
    refine ⟨9674355149618393920939703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6449570099745595947293135 9674355149618393920939703)
    ·
      refine ⟨14511532724427590881409555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9674355149618393920939703 14511532724427590881409555)
      ·
        refine ⟨21767299086641386322114333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14511532724427590881409555 21767299086641386322114333)
        ·
          refine ⟨8162737157490519870792875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21767299086641386322114333 8162737157490519870792875)
          ·
            refine ⟨12244105736235779806189313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8162737157490519870792875 12244105736235779806189313)
            ·
              refine ⟨9183079302176834854641985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12244105736235779806189313 9183079302176834854641985)
              ·
                refine ⟨6887309476632626140981489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9183079302176834854641985 6887309476632626140981489)
                ·
                  refine ⟨5165482107474469605736117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6887309476632626140981489 5165482107474469605736117)
                  ·
                    refine ⟨484263947575731525537761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5165482107474469605736117 484263947575731525537761)
                    ·
                      rfl

theorem cell23_2829302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_2829302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829302 prefixEnd_2829302 := by exact prefixLift 2829302
  have htrace : WordTrace (prefixWord ++ tailWord_2829302) baseStart_2829302 baseEnd_2829302 := by
    simpa [prefixWord, tailWord_2829302, baseEnd_2829302] using wordTrace_append hprefix tailTrace_2829302
  have hstable : (prefixWord ++ tailWord_2829302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829302).length < 2 ^ (prefixWord ++ tailWord_2829302).sum := by decide
  have hdescent : baseEnd_2829302 < baseStart_2829302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829305 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 2, 1, 4]
def baseStart_2829305 : Nat := 118140960795 + 2829305 * 2 ^ 59
def prefixEnd_2829305 : Nat := 4983230072969 + 3 ^ 40 * 2829305 * 2
def baseEnd_2829305 : Nat := 1452793383169158064875769

theorem tailTrace_2829305 : CollatzResearch.WordTrace tailWord_2829305 prefixEnd_2829305 1452793383169158064875769 := by
  unfold tailWord_2829305
  simp only [CollatzResearch.WordTrace]
  refine ⟨103193231014918666669049369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68795487343279111112699579 103193231014918666669049369)
  ·
    refine ⟨77394923261189000001787027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103193231014918666669049369 77394923261189000001787027)
    ·
      refine ⟨116092384891783500002680541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77394923261189000001787027 116092384891783500002680541)
      ·
        refine ⟨43534644334418812501005203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116092384891783500002680541 43534644334418812501005203)
        ·
          refine ⟨65301966501628218751507805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43534644334418812501005203 65301966501628218751507805)
          ·
            refine ⟨24488237438110582031815427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65301966501628218751507805 24488237438110582031815427)
            ·
              refine ⟨36732356157165873047723141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24488237438110582031815427 36732356157165873047723141)
              ·
                refine ⟨6887316779468601196448089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36732356157165873047723141 6887316779468601196448089)
                ·
                  refine ⟨5165487584601450897336067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6887316779468601196448089 5165487584601450897336067)
                  ·
                    refine ⟨7748231376902176346004101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5165487584601450897336067 7748231376902176346004101)
                    ·
                      refine ⟨1452793383169158064875769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7748231376902176346004101 1452793383169158064875769)
                      ·
                        rfl

theorem cell23_2829305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_2829305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829305 prefixEnd_2829305 := by exact prefixLift 2829305
  have htrace : WordTrace (prefixWord ++ tailWord_2829305) baseStart_2829305 baseEnd_2829305 := by
    simpa [prefixWord, tailWord_2829305, baseEnd_2829305] using wordTrace_append hprefix tailTrace_2829305
  have hstable : (prefixWord ++ tailWord_2829305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829305).length < 2 ^ (prefixWord ++ tailWord_2829305).sum := by decide
  have hdescent : baseEnd_2829305 < baseStart_2829305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829322 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 1, 6, 2]
def baseStart_2829322 : Nat := 118140960795 + 2829322 * 2 ^ 59
def prefixEnd_2829322 : Nat := 4983230072969 + 3 ^ 40 * 2829322 * 2
def baseEnd_2829322 : Nat := 1452802112340284498363191

theorem tailTrace_2829322 : CollatzResearch.WordTrace tailWord_2829322 prefixEnd_2829322 1452802112340284498363191 := by
  unfold tailWord_2829322
  simp only [CollatzResearch.WordTrace]
  refine ⟨25798462763964269643104555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68795900703904719048278813 25798462763964269643104555)
  ·
    refine ⟨38697694145946404464656833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25798462763964269643104555 38697694145946404464656833)
    ·
      refine ⟨29023270609459803348492625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38697694145946404464656833 29023270609459803348492625)
      ·
        refine ⟨21767452957094852511369469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29023270609459803348492625 21767452957094852511369469)
        ·
          refine ⟨8162794858910569691763551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21767452957094852511369469 8162794858910569691763551)
          ·
            refine ⟨12244192288365854537645327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8162794858910569691763551 12244192288365854537645327)
            ·
              refine ⟨18366288432548781806467991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12244192288365854537645327 18366288432548781806467991)
              ·
                refine ⟨27549432648823172709701987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18366288432548781806467991 27549432648823172709701987)
                ·
                  refine ⟨41324148973234759064552981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27549432648823172709701987 41324148973234759064552981)
                  ·
                    refine ⟨1937069483120379331150921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41324148973234759064552981 1937069483120379331150921)
                    ·
                      refine ⟨1452802112340284498363191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1937069483120379331150921 1452802112340284498363191)
                      ·
                        rfl

theorem cell23_2829322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_2829322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829322 prefixEnd_2829322 := by exact prefixLift 2829322
  have htrace : WordTrace (prefixWord ++ tailWord_2829322) baseStart_2829322 baseEnd_2829322 := by
    simpa [prefixWord, tailWord_2829322, baseEnd_2829322] using wordTrace_append hprefix tailTrace_2829322
  have hstable : (prefixWord ++ tailWord_2829322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829322).length < 2 ^ (prefixWord ++ tailWord_2829322).sum := by decide
  have hdescent : baseEnd_2829322 < baseStart_2829322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829349 : List Nat := [1, 3, 1, 2, 2, 2, 4, 3, 1, 4]
def baseStart_2829349 : Nat := 118140960795 + 2829349 * 2 ^ 59
def prefixEnd_2829349 : Nat := 4983230072969 + 3 ^ 40 * 2829349 * 2
def baseEnd_2829349 : Nat := 484271992105985297575189

theorem tailTrace_2829349 : CollatzResearch.WordTrace tailWord_2829349 prefixEnd_2829349 484271992105985297575189 := by
  unfold tailWord_2829349
  simp only [CollatzResearch.WordTrace]
  refine ⟨103194835826759262183651101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68796557217839508122434067 103194835826759262183651101)
  ·
    refine ⟨38698063435034723318869163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103194835826759262183651101 38698063435034723318869163)
    ·
      refine ⟨58047095152552084978303745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38698063435034723318869163 58047095152552084978303745)
      ·
        refine ⟨43535321364414063733727809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58047095152552084978303745 43535321364414063733727809)
        ·
          refine ⟨32651491023310547800295857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43535321364414063733727809 32651491023310547800295857)
          ·
            refine ⟨24488618267482910850221893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32651491023310547800295857 24488618267482910850221893)
            ·
              refine ⟨4591615925153045784416605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24488618267482910850221893 4591615925153045784416605)
              ·
                refine ⟨1721855971932392169156227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4591615925153045784416605 1721855971932392169156227)
                ·
                  refine ⟨2582783957898588253734341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721855971932392169156227 2582783957898588253734341)
                  ·
                    refine ⟨484271992105985297575189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2582783957898588253734341 484271992105985297575189)
                    ·
                      rfl

theorem cell23_2829349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 1, 4].length) (baseStart_2829349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829349 prefixEnd_2829349 := by exact prefixLift 2829349
  have htrace : WordTrace (prefixWord ++ tailWord_2829349) baseStart_2829349 baseEnd_2829349 := by
    simpa [prefixWord, tailWord_2829349, baseEnd_2829349] using wordTrace_append hprefix tailTrace_2829349
  have hstable : (prefixWord ++ tailWord_2829349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829349).length < 2 ^ (prefixWord ++ tailWord_2829349).sum := by decide
  have hdescent : baseEnd_2829349 < baseStart_2829349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829366 : List Nat := [5, 1, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_2829366 : Nat := 118140960795 + 2829366 * 2 ^ 59
def prefixEnd_2829366 : Nat := 4983230072969 + 3 ^ 40 * 2829366 * 2
def baseEnd_2829366 : Nat := 484274901829694108737663

theorem tailTrace_2829366 : CollatzResearch.WordTrace tailWord_2829366 prefixEnd_2829366 484274901829694108737663 := by
  unfold tailWord_2829366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6449715991731104630438747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68796970578465116058013301 6449715991731104630438747)
  ·
    refine ⟨9674573987596656945658121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6449715991731104630438747 9674573987596656945658121)
    ·
      refine ⟨7255930490697492709243591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9674573987596656945658121 7255930490697492709243591)
      ·
        refine ⟨10883895736046239063865387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7255930490697492709243591 10883895736046239063865387)
        ·
          refine ⟨16325843604069358595798081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10883895736046239063865387 16325843604069358595798081)
          ·
            refine ⟨12244382703052018946848561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16325843604069358595798081 12244382703052018946848561)
            ·
              refine ⟨9183287027289014210136421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12244382703052018946848561 9183287027289014210136421)
              ·
                refine ⟨1721866317616690164400579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9183287027289014210136421 1721866317616690164400579)
                ·
                  refine ⟨2582799476425035246600869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721866317616690164400579 2582799476425035246600869)
                  ·
                    refine ⟨484274901829694108737663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2582799476425035246600869 484274901829694108737663)
                    ·
                      rfl

theorem cell23_2829366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_2829366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829366 prefixEnd_2829366 := by exact prefixLift 2829366
  have htrace : WordTrace (prefixWord ++ tailWord_2829366) baseStart_2829366 baseEnd_2829366 := by
    simpa [prefixWord, tailWord_2829366, baseEnd_2829366] using wordTrace_append hprefix tailTrace_2829366
  have hstable : (prefixWord ++ tailWord_2829366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829366).length < 2 ^ (prefixWord ++ tailWord_2829366).sum := by decide
  have hdescent : baseEnd_2829366 < baseStart_2829366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829425 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 5, 2, 4]
def baseStart_2829425 : Nat := 118140960795 + 2829425 * 2 ^ 59
def prefixEnd_2829425 : Nat := 4983230072969 + 3 ^ 40 * 2829425 * 2
def baseEnd_2829425 : Nat := 1452855000847697595375217

theorem tailTrace_2829425 : CollatzResearch.WordTrace tailWord_2829425 prefixEnd_2829425 1452855000847697595375217 := by
  unfold tailWord_2829425
  simp only [CollatzResearch.WordTrace]
  refine ⟨103197607774483927163417729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68798405182989284775611819 103197607774483927163417729)
  ·
    refine ⟨77398205830862945372563297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103197607774483927163417729 77398205830862945372563297)
    ·
      refine ⟨58048654373147209029422473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77398205830862945372563297 58048654373147209029422473)
      ·
        refine ⟨43536490779860406772066855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58048654373147209029422473 43536490779860406772066855)
        ·
          refine ⟨65304736169790610158100283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43536490779860406772066855 65304736169790610158100283)
          ·
            refine ⟨97957104254685915237150425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65304736169790610158100283 97957104254685915237150425)
            ·
              refine ⟨73467828191014436427862819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97957104254685915237150425 73467828191014436427862819)
              ·
                refine ⟨110201742286521654641794229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73467828191014436427862819 110201742286521654641794229)
                ·
                  refine ⟨10331413339361405122668209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110201742286521654641794229 10331413339361405122668209)
                  ·
                    refine ⟨7748560004521053842001157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10331413339361405122668209 7748560004521053842001157)
                    ·
                      refine ⟨1452855000847697595375217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7748560004521053842001157 1452855000847697595375217)
                      ·
                        rfl

theorem cell23_2829425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_2829425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829425 prefixEnd_2829425 := by exact prefixLift 2829425
  have htrace : WordTrace (prefixWord ++ tailWord_2829425) baseStart_2829425 baseEnd_2829425 := by
    simpa [prefixWord, tailWord_2829425, baseEnd_2829425] using wordTrace_append hprefix tailTrace_2829425
  have hstable : (prefixWord ++ tailWord_2829425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829425).length < 2 ^ (prefixWord ++ tailWord_2829425).sum := by decide
  have hdescent : baseEnd_2829425 < baseStart_2829425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829449 : List Nat := [1, 2, 1, 1, 4, 3, 3, 2, 1, 2, 3]
def baseStart_2829449 : Nat := 118140960795 + 2829449 * 2 ^ 59
def prefixEnd_2829449 : Nat := 4983230072969 + 3 ^ 40 * 2829449 * 2
def baseEnd_2829449 : Nat := 1452867324383405501475107

theorem tailTrace_2829449 : CollatzResearch.WordTrace tailWord_2829449 prefixEnd_2829449 1452867324383405501475107 := by
  unfold tailWord_2829449
  simp only [CollatzResearch.WordTrace]
  refine ⟨103198483126396979262291401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68798988750931319508194267 103198483126396979262291401)
  ·
    refine ⟨77398862344797734446718551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103198483126396979262291401 77398862344797734446718551)
    ·
      refine ⟨116098293517196601670077827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77398862344797734446718551 116098293517196601670077827)
      ·
        refine ⟨174147440275794902505116741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116098293517196601670077827 174147440275794902505116741)
        ·
          refine ⟨32652645051711544219709389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174147440275794902505116741 32652645051711544219709389)
          ·
            refine ⟨12244741894391829082391021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32652645051711544219709389 12244741894391829082391021)
            ·
              refine ⟨4591778210396935905896633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12244741894391829082391021 4591778210396935905896633)
              ·
                refine ⟨3443833657797701929422475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4591778210396935905896633 3443833657797701929422475)
                ·
                  refine ⟨5165750486696552894133713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3443833657797701929422475 5165750486696552894133713)
                  ·
                    refine ⟨3874312865022414670600285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5165750486696552894133713 3874312865022414670600285)
                    ·
                      refine ⟨1452867324383405501475107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3874312865022414670600285 1452867324383405501475107)
                      ·
                        rfl

theorem cell23_2829449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 2, 3].length) (baseStart_2829449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829449 prefixEnd_2829449 := by exact prefixLift 2829449
  have htrace : WordTrace (prefixWord ++ tailWord_2829449) baseStart_2829449 baseEnd_2829449 := by
    simpa [prefixWord, tailWord_2829449, baseEnd_2829449] using wordTrace_append hprefix tailTrace_2829449
  have hstable : (prefixWord ++ tailWord_2829449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829449).length < 2 ^ (prefixWord ++ tailWord_2829449).sum := by decide
  have hdescent : baseEnd_2829449 < baseStart_2829449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829475 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 5]
def baseStart_2829475 : Nat := 118140960795 + 2829475 * 2 ^ 59
def prefixEnd_2829475 : Nat := 4983230072969 + 3 ^ 40 * 2829475 * 2
def baseEnd_2829475 : Nat := 1452880674880422399749987

theorem tailTrace_2829475 : CollatzResearch.WordTrace tailWord_2829475 prefixEnd_2829475 1452880674880422399749987 := by
  unfold tailWord_2829475
  simp only [CollatzResearch.WordTrace]
  refine ⟨103199431424302785702737879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68799620949535190468491919 103199431424302785702737879)
  ·
    refine ⟨154799147136454178554106819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103199431424302785702737879 154799147136454178554106819)
    ·
      refine ⟨232198720704681267831160229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154799147136454178554106819 232198720704681267831160229)
      ·
        refine ⟨43537260132127737718342543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232198720704681267831160229 43537260132127737718342543)
        ·
          refine ⟨65305890198191606577513815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43537260132127737718342543 65305890198191606577513815)
          ·
            refine ⟨97958835297287409866270723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65305890198191606577513815 97958835297287409866270723)
            ·
              refine ⟨146938252945931114799406085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97958835297287409866270723 146938252945931114799406085)
              ·
                refine ⟨27550922427362084024888641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146938252945931114799406085 27550922427362084024888641)
                ·
                  refine ⟨20663191820521563018666481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27550922427362084024888641 20663191820521563018666481)
                  ·
                    refine ⟨15497393865391172263999861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20663191820521563018666481 15497393865391172263999861)
                    ·
                      refine ⟨1452880674880422399749987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15497393865391172263999861 1452880674880422399749987)
                      ·
                        rfl

theorem cell23_2829475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_2829475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829475 prefixEnd_2829475 := by exact prefixLift 2829475
  have htrace : WordTrace (prefixWord ++ tailWord_2829475) baseStart_2829475 baseEnd_2829475 := by
    simpa [prefixWord, tailWord_2829475, baseEnd_2829475] using wordTrace_append hprefix tailTrace_2829475
  have hstable : (prefixWord ++ tailWord_2829475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829475).length < 2 ^ (prefixWord ++ tailWord_2829475).sum := by decide
  have hdescent : baseEnd_2829475 < baseStart_2829475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829517 : List Nat := [1, 6, 2, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_2829517 : Nat := 118140960795 + 2829517 * 2 ^ 59
def prefixEnd_2829517 : Nat := 4983230072969 + 3 ^ 40 * 2829517 * 2
def baseEnd_2829517 : Nat := 1452902241067911235424795

theorem tailTrace_2829517 : CollatzResearch.WordTrace tailWord_2829517 prefixEnd_2829517 1452902241067911235424795 := by
  unfold tailWord_2829517
  simp only [CollatzResearch.WordTrace]
  refine ⟨103200963290150626875766805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68800642193433751250511203 103200963290150626875766805)
  ·
    refine ⟨4837545154225810634801569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 103200963290150626875766805 4837545154225810634801569)
    ·
      refine ⟨3628158865669357976101177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4837545154225810634801569 3628158865669357976101177)
      ·
        refine ⟨2721119149252018482075883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3628158865669357976101177 2721119149252018482075883)
        ·
          refine ⟨4081678723878027723113825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2721119149252018482075883 4081678723878027723113825)
          ·
            refine ⟨3061259042908520792335369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4081678723878027723113825 3061259042908520792335369)
            ·
              refine ⟨2295944282181390594251527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3061259042908520792335369 2295944282181390594251527)
              ·
                refine ⟨3443916423272085891377291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2295944282181390594251527 3443916423272085891377291)
                ·
                  refine ⟨5165874634908128837065937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3443916423272085891377291 5165874634908128837065937)
                  ·
                    refine ⟨3874405976181096627799453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5165874634908128837065937 3874405976181096627799453)
                    ·
                      refine ⟨1452902241067911235424795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3874405976181096627799453 1452902241067911235424795)
                      ·
                        rfl

theorem cell23_2829517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_2829517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829517 prefixEnd_2829517 := by exact prefixLift 2829517
  have htrace : WordTrace (prefixWord ++ tailWord_2829517) baseStart_2829517 baseEnd_2829517 := by
    simpa [prefixWord, tailWord_2829517, baseEnd_2829517] using wordTrace_append hprefix tailTrace_2829517
  have hstable : (prefixWord ++ tailWord_2829517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829517).length < 2 ^ (prefixWord ++ tailWord_2829517).sum := by decide
  have hdescent : baseEnd_2829517 < baseStart_2829517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829522 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2829522 : Nat := 118140960795 + 2829522 * 2 ^ 59
def prefixEnd_2829522 : Nat := 4983230072969 + 3 ^ 40 * 2829522 * 2
def baseEnd_2829522 : Nat := 1452904808471183715862271

theorem tailTrace_2829522 : CollatzResearch.WordTrace tailWord_2829522 prefixEnd_2829522 1452904808471183715862271 := by
  unfold tailWord_2829522
  simp only [CollatzResearch.WordTrace]
  refine ⟨25800286413783128182424705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68800763770088341819799213 25800286413783128182424705)
  ·
    refine ⟨19350214810337346136818529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25800286413783128182424705 19350214810337346136818529)
    ·
      refine ⟨14512661107753009602613897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19350214810337346136818529 14512661107753009602613897)
      ·
        refine ⟨10884495830814757201960423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14512661107753009602613897 10884495830814757201960423)
        ·
          refine ⟨16326743746222135802940635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10884495830814757201960423 16326743746222135802940635)
          ·
            refine ⟨24490115619333203704410953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16326743746222135802940635 24490115619333203704410953)
            ·
              refine ⟨18367586714499902778308215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24490115619333203704410953 18367586714499902778308215)
              ·
                refine ⟨27551380071749854167462323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18367586714499902778308215 27551380071749854167462323)
                ·
                  refine ⟨41327070107624781251193485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27551380071749854167462323 41327070107624781251193485)
                  ·
                    refine ⟨15497651290359292969197557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41327070107624781251193485 15497651290359292969197557)
                    ·
                      refine ⟨1452904808471183715862271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15497651290359292969197557 1452904808471183715862271)
                      ·
                        rfl

theorem cell23_2829522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2829522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829522 prefixEnd_2829522 := by exact prefixLift 2829522
  have htrace : WordTrace (prefixWord ++ tailWord_2829522) baseStart_2829522 baseEnd_2829522 := by
    simpa [prefixWord, tailWord_2829522, baseEnd_2829522] using wordTrace_append hprefix tailTrace_2829522
  have hstable : (prefixWord ++ tailWord_2829522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829522).length < 2 ^ (prefixWord ++ tailWord_2829522).sum := by decide
  have hdescent : baseEnd_2829522 < baseStart_2829522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829536 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 4, 2, 2]
def baseStart_2829536 : Nat := 118140960795 + 2829536 * 2 ^ 59
def prefixEnd_2829536 : Nat := 4983230072969 + 3 ^ 40 * 2829536 * 2
def baseEnd_2829536 : Nat := 1452911997200346661087207

theorem tailTrace_2829536 : CollatzResearch.WordTrace tailWord_2829536 prefixEnd_2829536 1452911997200346661087207 := by
  unfold tailWord_2829536
  simp only [CollatzResearch.WordTrace]
  refine ⟨51600828138540896560354231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68801104184721195413805641 51600828138540896560354231)
  ·
    refine ⟨77401242207811344840531347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51600828138540896560354231 77401242207811344840531347)
    ·
      refine ⟨116101863311717017260797021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77401242207811344840531347 116101863311717017260797021)
      ·
        refine ⟨43538198741893881472798883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116101863311717017260797021 43538198741893881472798883)
        ·
          refine ⟨65307298112840822209198325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43538198741893881472798883 65307298112840822209198325)
          ·
            refine ⟨6122559198078827082112343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65307298112840822209198325 6122559198078827082112343)
            ·
              refine ⟨9183838797118240623168515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6122559198078827082112343 9183838797118240623168515)
              ·
                refine ⟨13775758195677360934752773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9183838797118240623168515 13775758195677360934752773)
                ·
                  refine ⟨2582954661689505175266145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13775758195677360934752773 2582954661689505175266145)
                  ·
                    refine ⟨1937215996267128881449609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2582954661689505175266145 1937215996267128881449609)
                    ·
                      refine ⟨1452911997200346661087207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1937215996267128881449609 1452911997200346661087207)
                      ·
                        rfl

theorem cell23_2829536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_2829536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829536 prefixEnd_2829536 := by exact prefixLift 2829536
  have htrace : WordTrace (prefixWord ++ tailWord_2829536) baseStart_2829536 baseEnd_2829536 := by
    simpa [prefixWord, tailWord_2829536, baseEnd_2829536] using wordTrace_append hprefix tailTrace_2829536
  have hstable : (prefixWord ++ tailWord_2829536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829536).length < 2 ^ (prefixWord ++ tailWord_2829536).sum := by decide
  have hdescent : baseEnd_2829536 < baseStart_2829536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829545 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 8]
def baseStart_2829545 : Nat := 118140960795 + 2829545 * 2 ^ 59
def prefixEnd_2829545 : Nat := 4983230072969 + 3 ^ 40 * 2829545 * 2
def baseEnd_2829545 : Nat := 1452916618526237125874665

theorem tailTrace_2829545 : CollatzResearch.WordTrace tailWord_2829545 prefixEnd_2829545 1452916618526237125874665 := by
  unfold tailWord_2829545
  simp only [CollatzResearch.WordTrace]
  refine ⟨103201984534049187657786089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68801323022699458438524059 103201984534049187657786089)
  ·
    refine ⟨77401488400536890743339567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103201984534049187657786089 77401488400536890743339567)
    ·
      refine ⟨116102232600805336115009351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77401488400536890743339567 116102232600805336115009351)
      ·
        refine ⟨174153348901208004172514027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116102232600805336115009351 174153348901208004172514027)
        ·
          refine ⟨261230023351812006258771041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174153348901208004172514027 261230023351812006258771041)
          ·
            refine ⟨195922517513859004694078281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261230023351812006258771041 195922517513859004694078281)
            ·
              refine ⟨146941888135394253520558711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195922517513859004694078281 146941888135394253520558711)
              ·
                refine ⟨220412832203091380280838067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146941888135394253520558711 220412832203091380280838067)
                ·
                  refine ⟨330619248304637070421257101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220412832203091380280838067 330619248304637070421257101)
                  ·
                    refine ⟨123982218114238901407971413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 330619248304637070421257101 123982218114238901407971413)
                    ·
                      refine ⟨1452916618526237125874665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 123982218114238901407971413 1452916618526237125874665)
                      ·
                        rfl

theorem cell23_2829545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_2829545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829545 prefixEnd_2829545 := by exact prefixLift 2829545
  have htrace : WordTrace (prefixWord ++ tailWord_2829545) baseStart_2829545 baseEnd_2829545 := by
    simpa [prefixWord, tailWord_2829545, baseEnd_2829545] using wordTrace_append hprefix tailTrace_2829545
  have hstable : (prefixWord ++ tailWord_2829545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829545).length < 2 ^ (prefixWord ++ tailWord_2829545).sum := by decide
  have hdescent : baseEnd_2829545 < baseStart_2829545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829549 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_2829549 : Nat := 118140960795 + 2829549 * 2 ^ 59
def prefixEnd_2829549 : Nat := 4983230072969 + 3 ^ 40 * 2829549 * 2
def baseEnd_2829549 : Nat := 1452918672448855110224647

theorem tailTrace_2829549 : CollatzResearch.WordTrace tailWord_2829549 prefixEnd_2829549 1452918672448855110224647 := by
  unfold tailWord_2829549
  simp only [CollatzResearch.WordTrace]
  refine ⟨103202130426034696340931701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68801420284023130893954467 103202130426034696340931701)
  ·
    refine ⟨9675199727440752781962347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103202130426034696340931701 9675199727440752781962347)
    ·
      refine ⟨14512799591161129172943521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9675199727440752781962347 14512799591161129172943521)
      ·
        refine ⟨10884599693370846879707641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14512799591161129172943521 10884599693370846879707641)
        ·
          refine ⟨8163449770028135159780731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10884599693370846879707641 8163449770028135159780731)
          ·
            refine ⟨12245174655042202739671097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8163449770028135159780731 12245174655042202739671097)
            ·
              refine ⟨9183880991281652054753323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12245174655042202739671097 9183880991281652054753323)
              ·
                refine ⟨13775821486922478082129985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9183880991281652054753323 13775821486922478082129985)
                ·
                  refine ⟨10331866115191858561597489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13775821486922478082129985 10331866115191858561597489)
                  ·
                    refine ⟨7748899586393893921198117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10331866115191858561597489 7748899586393893921198117)
                    ·
                      refine ⟨1452918672448855110224647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7748899586393893921198117 1452918672448855110224647)
                      ·
                        rfl

theorem cell23_2829549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_2829549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829549 prefixEnd_2829549 := by exact prefixLift 2829549
  have htrace : WordTrace (prefixWord ++ tailWord_2829549) baseStart_2829549 baseEnd_2829549 := by
    simpa [prefixWord, tailWord_2829549, baseEnd_2829549] using wordTrace_append hprefix tailTrace_2829549
  have hstable : (prefixWord ++ tailWord_2829549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829549).length < 2 ^ (prefixWord ++ tailWord_2829549).sum := by decide
  have hdescent : baseEnd_2829549 < baseStart_2829549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829599 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 5]
def baseStart_2829599 : Nat := 118140960795 + 2829599 * 2 ^ 59
def prefixEnd_2829599 : Nat := 4983230072969 + 3 ^ 40 * 2829599 * 2
def baseEnd_2829599 : Nat := 1452944346481579914599417

theorem tailTrace_2829599 : CollatzResearch.WordTrace tailWord_2829599 prefixEnd_2829599 1452944346481579914599417 := by
  unfold tailWord_2829599
  simp only [CollatzResearch.WordTrace]
  refine ⟨103203954075853554880251851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68802636050569036586834567 103203954075853554880251851)
  ·
    refine ⟨154805931113780332320377777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103203954075853554880251851 154805931113780332320377777)
    ·
      refine ⟨116104448335335249240283333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154805931113780332320377777 116104448335335249240283333)
      ·
        refine ⟨21769584062875359232553125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116104448335335249240283333 21769584062875359232553125)
        ·
          refine ⟨4081797011789129856103711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21769584062875359232553125 4081797011789129856103711)
          ·
            refine ⟨6122695517683694784155567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4081797011789129856103711 6122695517683694784155567)
            ·
              refine ⟨9184043276525542176233351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6122695517683694784155567 9184043276525542176233351)
              ·
                refine ⟨13776064914788313264350027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9184043276525542176233351 13776064914788313264350027)
                ·
                  refine ⟨20664097372182469896525041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13776064914788313264350027 20664097372182469896525041)
                  ·
                    refine ⟨15498073029136852422393781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20664097372182469896525041 15498073029136852422393781)
                    ·
                      refine ⟨1452944346481579914599417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15498073029136852422393781 1452944346481579914599417)
                      ·
                        rfl

theorem cell23_2829599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_2829599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829599 prefixEnd_2829599 := by exact prefixLift 2829599
  have htrace : WordTrace (prefixWord ++ tailWord_2829599) baseStart_2829599 baseEnd_2829599 := by
    simpa [prefixWord, tailWord_2829599, baseEnd_2829599] using wordTrace_append hprefix tailTrace_2829599
  have hstable : (prefixWord ++ tailWord_2829599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829599).length < 2 ^ (prefixWord ++ tailWord_2829599).sum := by decide
  have hdescent : baseEnd_2829599 < baseStart_2829599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829649 : List Nat := [1, 2, 2, 1, 4, 1, 4, 2, 6]
def baseStart_2829649 : Nat := 118140960795 + 2829649 * 2 ^ 59
def prefixEnd_2829649 : Nat := 4983230072969 + 3 ^ 40 * 2829649 * 2
def baseEnd_2829649 : Nat := 161441113390478302108243

theorem tailTrace_2829649 : CollatzResearch.WordTrace tailWord_2829649 prefixEnd_2829649 161441113390478302108243 := by
  unfold tailWord_2829649
  simp only [CollatzResearch.WordTrace]
  refine ⟨103205777725672413419572001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68803851817114942279714667 103205777725672413419572001)
  ·
    refine ⟨77404333294254310064679001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103205777725672413419572001 77404333294254310064679001)
    ·
      refine ⟨58053249970690732548509251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77404333294254310064679001 58053249970690732548509251)
      ·
        refine ⟨87079874956036098822763877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58053249970690732548509251 87079874956036098822763877)
        ·
          refine ⟨16327476554256768529268227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87079874956036098822763877 16327476554256768529268227)
          ·
            refine ⟨24491214831385152793902341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16327476554256768529268227 24491214831385152793902341)
            ·
              refine ⟨4592102780884716148856689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24491214831385152793902341 4592102780884716148856689)
              ·
                refine ⟨3444077085663537111642517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4592102780884716148856689 3444077085663537111642517)
                ·
                  refine ⟨161441113390478302108243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3444077085663537111642517 161441113390478302108243)
                  ·
                    rfl

theorem cell23_2829649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 6].length) (baseStart_2829649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829649 prefixEnd_2829649 := by exact prefixLift 2829649
  have htrace : WordTrace (prefixWord ++ tailWord_2829649) baseStart_2829649 baseEnd_2829649 := by
    simpa [prefixWord, tailWord_2829649, baseEnd_2829649] using wordTrace_append hprefix tailTrace_2829649
  have hstable : (prefixWord ++ tailWord_2829649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829649).length < 2 ^ (prefixWord ++ tailWord_2829649).sum := by decide
  have hdescent : baseEnd_2829649 < baseStart_2829649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829653 : List Nat := [1, 3, 2, 2, 3, 2, 1, 4, 1, 4]
def baseStart_2829653 : Nat := 118140960795 + 2829653 * 2 ^ 59
def prefixEnd_2829653 : Nat := 4983230072969 + 3 ^ 40 * 2829653 * 2
def baseEnd_2829653 : Nat := 484324024812307567774723

theorem tailTrace_2829653 : CollatzResearch.WordTrace tailWord_2829653 prefixEnd_2829653 484324024812307567774723 := by
  unfold tailWord_2829653
  simp only [CollatzResearch.WordTrace]
  refine ⟨103205923617657922102717613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68803949078438614735145075 103205923617657922102717613)
  ·
    refine ⟨38702221356621720788519105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103205923617657922102717613 38702221356621720788519105)
    ·
      refine ⟨29026666017466290591389329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38702221356621720788519105 29026666017466290591389329)
      ·
        refine ⟨21769999513099717943541997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29026666017466290591389329 21769999513099717943541997)
        ·
          refine ⟨8163749817412394228828249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21769999513099717943541997 8163749817412394228828249)
          ·
            refine ⟨6122812363059295671621187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8163749817412394228828249 6122812363059295671621187)
            ·
              refine ⟨9184218544588943507431781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6122812363059295671621187 9184218544588943507431781)
              ·
                refine ⟨1722040977110426907643459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9184218544588943507431781 1722040977110426907643459)
                ·
                  refine ⟨2583061465665640361465189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1722040977110426907643459 2583061465665640361465189)
                  ·
                    refine ⟨484324024812307567774723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2583061465665640361465189 484324024812307567774723)
                    ·
                      rfl

theorem cell23_2829653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_2829653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829653 prefixEnd_2829653 := by exact prefixLift 2829653
  have htrace : WordTrace (prefixWord ++ tailWord_2829653) baseStart_2829653 baseEnd_2829653 := by
    simpa [prefixWord, tailWord_2829653, baseEnd_2829653] using wordTrace_append hprefix tailTrace_2829653
  have hstable : (prefixWord ++ tailWord_2829653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829653).length < 2 ^ (prefixWord ++ tailWord_2829653).sum := by decide
  have hdescent : baseEnd_2829653 < baseStart_2829653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829676 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 3]
def baseStart_2829676 : Nat := 118140960795 + 2829676 * 2 ^ 59
def prefixEnd_2829676 : Nat := 4983230072969 + 3 ^ 40 * 2829676 * 2
def baseEnd_2829676 : Nat := 1452983884491976113336563

theorem tailTrace_2829676 : CollatzResearch.WordTrace tailWord_2829676 prefixEnd_2829676 1452983884491976113336563 := by
  unfold tailWord_2829676
  simp only [CollatzResearch.WordTrace]
  refine ⟨51603381248287298515402441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68804508331049731353869921 51603381248287298515402441)
  ·
    refine ⟨38702535936215473886551831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51603381248287298515402441 38702535936215473886551831)
    ·
      refine ⟨58053803904323210829827747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38702535936215473886551831 58053803904323210829827747)
      ·
        refine ⟨87080705856484816244741621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58053803904323210829827747 87080705856484816244741621)
        ·
          refine ⟨8163816174045451522944527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87080705856484816244741621 8163816174045451522944527)
          ·
            refine ⟨12245724261068177284416791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8163816174045451522944527 12245724261068177284416791)
            ·
              refine ⟨18368586391602265926625187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12245724261068177284416791 18368586391602265926625187)
              ·
                refine ⟨27552879587403398889937781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18368586391602265926625187 27552879587403398889937781)
                ·
                  refine ⟨2583082461319068645931667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27552879587403398889937781 2583082461319068645931667)
                  ·
                    refine ⟨3874623691978602968897501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2583082461319068645931667 3874623691978602968897501)
                    ·
                      refine ⟨1452983884491976113336563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3874623691978602968897501 1452983884491976113336563)
                      ·
                        rfl

theorem cell23_2829676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_2829676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829676 prefixEnd_2829676 := by exact prefixLift 2829676
  have htrace : WordTrace (prefixWord ++ tailWord_2829676) baseStart_2829676 baseEnd_2829676 := by
    simpa [prefixWord, tailWord_2829676, baseEnd_2829676] using wordTrace_append hprefix tailTrace_2829676
  have hstable : (prefixWord ++ tailWord_2829676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829676).length < 2 ^ (prefixWord ++ tailWord_2829676).sum := by decide
  have hdescent : baseEnd_2829676 < baseStart_2829676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829679 : List Nat := [1, 1, 2, 1, 3, 1, 4, 4, 1, 5]
def baseStart_2829679 : Nat := 118140960795 + 2829679 * 2 ^ 59
def prefixEnd_2829679 : Nat := 4983230072969 + 3 ^ 40 * 2829679 * 2
def baseEnd_2829679 : Nat := 484328474977979867199683

theorem tailTrace_2829679 : CollatzResearch.WordTrace tailWord_2829679 prefixEnd_2829679 484328474977979867199683 := by
  unfold tailWord_2829679
  simp only [CollatzResearch.WordTrace]
  refine ⟨103206871915563728543164091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68804581277042485695442727 103206871915563728543164091)
  ·
    refine ⟨154810307873345592814746137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103206871915563728543164091 154810307873345592814746137)
    ·
      refine ⟨116107730905009194611059603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154810307873345592814746137 116107730905009194611059603)
      ·
        refine ⟨174161596357513791916589405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116107730905009194611059603 174161596357513791916589405)
        ·
          refine ⟨65310598634067671968721027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174161596357513791916589405 65310598634067671968721027)
          ·
            refine ⟨97965897951101507953081541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65310598634067671968721027 97965897951101507953081541)
            ·
              refine ⟨18368605865831532741202789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97965897951101507953081541 18368605865831532741202789)
              ·
                refine ⟨3444113599843412388975523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18368605865831532741202789 3444113599843412388975523)
                ·
                  refine ⟨5166170399765118583463285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3444113599843412388975523 5166170399765118583463285)
                  ·
                    refine ⟨484328474977979867199683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5166170399765118583463285 484328474977979867199683)
                    ·
                      rfl

theorem cell23_2829679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 5].length) (baseStart_2829679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829679 prefixEnd_2829679 := by exact prefixLift 2829679
  have htrace : WordTrace (prefixWord ++ tailWord_2829679) baseStart_2829679 baseEnd_2829679 := by
    simpa [prefixWord, tailWord_2829679, baseEnd_2829679] using wordTrace_append hprefix tailTrace_2829679
  have hstable : (prefixWord ++ tailWord_2829679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829679).length < 2 ^ (prefixWord ++ tailWord_2829679).sum := by decide
  have hdescent : baseEnd_2829679 < baseStart_2829679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829710 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3]
def baseStart_2829710 : Nat := 118140960795 + 2829710 * 2 ^ 59
def prefixEnd_2829710 : Nat := 4983230072969 + 3 ^ 40 * 2829710 * 2
def baseEnd_2829710 : Nat := 1453001342834228980311407

theorem tailTrace_2829710 : CollatzResearch.WordTrace tailWord_2829710 prefixEnd_2829710 1453001342834228980311407 := by
  unfold tailWord_2829710
  simp only [CollatzResearch.WordTrace]
  refine ⟨12901000322306427604692823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68805335052300947225028389 12901000322306427604692823)
  ·
    refine ⟨19351500483459641407039235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12901000322306427604692823 19351500483459641407039235)
    ·
      refine ⟨29027250725189462110558853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19351500483459641407039235 29027250725189462110558853)
      ·
        refine ⟨5442609510973024145729785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29027250725189462110558853 5442609510973024145729785)
        ·
          refine ⟨4081957133229768109297339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5442609510973024145729785 4081957133229768109297339)
          ·
            refine ⟨6122935699844652163946009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4081957133229768109297339 6122935699844652163946009)
            ·
              refine ⟨4592201774883489122959507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6122935699844652163946009 4592201774883489122959507)
              ·
                refine ⟨6888302662325233684439261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4592201774883489122959507 6888302662325233684439261)
                ·
                  refine ⟨2583113498371962631664723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6888302662325233684439261 2583113498371962631664723)
                  ·
                    refine ⟨3874670247557943947497085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2583113498371962631664723 3874670247557943947497085)
                    ·
                      refine ⟨1453001342834228980311407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3874670247557943947497085 1453001342834228980311407)
                      ·
                        rfl

theorem cell23_2829710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_2829710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829710 prefixEnd_2829710 := by exact prefixLift 2829710
  have htrace : WordTrace (prefixWord ++ tailWord_2829710) baseStart_2829710 baseEnd_2829710 := by
    simpa [prefixWord, tailWord_2829710, baseEnd_2829710] using wordTrace_append hprefix tailTrace_2829710
  have hstable : (prefixWord ++ tailWord_2829710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829710).length < 2 ^ (prefixWord ++ tailWord_2829710).sum := by decide
  have hdescent : baseEnd_2829710 < baseStart_2829710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829756 : List Nat := [2, 2, 2, 4, 2, 2, 9]
def baseStart_2829756 : Nat := 118140960795 + 2829756 * 2 ^ 59
def prefixEnd_2829756 : Nat := 4983230072969 + 3 ^ 40 * 2829756 * 2
def baseEnd_2829756 : Nat := 17938579789436244448595

theorem tailTrace_2829756 : CollatzResearch.WordTrace tailWord_2829756 prefixEnd_2829756 17938579789436244448595 := by
  unfold tailWord_2829756
  simp only [CollatzResearch.WordTrace]
  refine ⟨51604840168142385346858561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68806453557523180462478081 51604840168142385346858561)
  ·
    refine ⟨38703630126106789010143921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51604840168142385346858561 38703630126106789010143921)
    ·
      refine ⟨29027722594580091757607941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38703630126106789010143921 29027722594580091757607941)
      ·
        refine ⟨5442697986483767204551489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29027722594580091757607941 5442697986483767204551489)
        ·
          refine ⟨4082023489862825403413617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5442697986483767204551489 4082023489862825403413617)
          ·
            refine ⟨3061517617397119052560213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4082023489862825403413617 3061517617397119052560213)
            ·
              refine ⟨17938579789436244448595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3061517617397119052560213 17938579789436244448595)
              ·
                rfl

theorem cell23_2829756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 9].length) (baseStart_2829756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829756 prefixEnd_2829756 := by exact prefixLift 2829756
  have htrace : WordTrace (prefixWord ++ tailWord_2829756) baseStart_2829756 baseEnd_2829756 := by
    simpa [prefixWord, tailWord_2829756, baseEnd_2829756] using wordTrace_append hprefix tailTrace_2829756
  have hstable : (prefixWord ++ tailWord_2829756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829756).length < 2 ^ (prefixWord ++ tailWord_2829756).sum := by decide
  have hdescent : baseEnd_2829756 < baseStart_2829756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829767 : List Nat := [1, 1, 4, 1, 1, 3, 5, 2, 1, 2, 2]
def baseStart_2829767 : Nat := 118140960795 + 2829767 * 2 ^ 59
def prefixEnd_2829767 : Nat := 4983230072969 + 3 ^ 40 * 2829767 * 2
def baseEnd_2829767 : Nat := 1453030611231535257298645

theorem tailTrace_2829767 : CollatzResearch.WordTrace tailWord_2829767 prefixEnd_2829767 1453030611231535257298645 := by
  unfold tailWord_2829767
  simp only [CollatzResearch.WordTrace]
  refine ⟨103210081539244919572367555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68806721026163279714911703 103210081539244919572367555)
  ·
    refine ⟨154815122308867379358551333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103210081539244919572367555 154815122308867379358551333)
    ·
      refine ⟨29027835432912633629728375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154815122308867379358551333 29027835432912633629728375)
      ·
        refine ⟨43541753149368950444592563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29027835432912633629728375 43541753149368950444592563)
        ·
          refine ⟨65312629724053425666888845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43541753149368950444592563 65312629724053425666888845)
          ·
            refine ⟨24492236146520034625083317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65312629724053425666888845 24492236146520034625083317)
            ·
              refine ⟨2296147138736253246101561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24492236146520034625083317 2296147138736253246101561)
              ·
                refine ⟨1722110354052189934576171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2296147138736253246101561 1722110354052189934576171)
                ·
                  refine ⟨2583165531078284901864257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1722110354052189934576171 2583165531078284901864257)
                  ·
                    refine ⟨1937374148308713676398193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2583165531078284901864257 1937374148308713676398193)
                    ·
                      refine ⟨1453030611231535257298645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1937374148308713676398193 1453030611231535257298645)
                      ·
                        rfl

theorem cell23_2829767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_2829767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829767 prefixEnd_2829767 := by exact prefixLift 2829767
  have htrace : WordTrace (prefixWord ++ tailWord_2829767) baseStart_2829767 baseEnd_2829767 := by
    simpa [prefixWord, tailWord_2829767, baseEnd_2829767] using wordTrace_append hprefix tailTrace_2829767
  have hstable : (prefixWord ++ tailWord_2829767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829767).length < 2 ^ (prefixWord ++ tailWord_2829767).sum := by decide
  have hdescent : baseEnd_2829767 < baseStart_2829767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829776 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 5, 3, 2]
def baseStart_2829776 : Nat := 118140960795 + 2829776 * 2 ^ 59
def prefixEnd_2829776 : Nat := 4983230072969 + 3 ^ 40 * 2829776 * 2
def baseEnd_2829776 : Nat := 1453035232557425722086103

theorem tailTrace_2829776 : CollatzResearch.WordTrace tailWord_2829776 prefixEnd_2829776 1453035232557425722086103 := by
  unfold tailWord_2829776
  simp only [CollatzResearch.WordTrace]
  refine ⟨51605204898106157054722591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68806939864141542739630121 51605204898106157054722591)
  ·
    refine ⟨77407807347159235582083887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51605204898106157054722591 77407807347159235582083887)
    ·
      refine ⟨116111711020738853373125831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77407807347159235582083887 116111711020738853373125831)
      ·
        refine ⟨174167566531108280059688747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116111711020738853373125831 174167566531108280059688747)
        ·
          refine ⟨261251349796662420089533121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174167566531108280059688747 261251349796662420089533121)
          ·
            refine ⟨195938512347496815067149841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261251349796662420089533121 195938512347496815067149841)
            ·
              refine ⟨146953884260622611300362381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195938512347496815067149841 146953884260622611300362381)
              ·
                refine ⟨55107706597733479237635893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146953884260622611300362381 55107706597733479237635893)
                ·
                  refine ⟨5166347493537513678528365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55107706597733479237635893 5166347493537513678528365)
                  ·
                    refine ⟨1937380310076567629448137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5166347493537513678528365 1937380310076567629448137)
                    ·
                      refine ⟨1453035232557425722086103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1937380310076567629448137 1453035232557425722086103)
                      ·
                        rfl

theorem cell23_2829776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 5, 3, 2].length) (baseStart_2829776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829776 prefixEnd_2829776 := by exact prefixLift 2829776
  have htrace : WordTrace (prefixWord ++ tailWord_2829776) baseStart_2829776 baseEnd_2829776 := by
    simpa [prefixWord, tailWord_2829776, baseEnd_2829776] using wordTrace_append hprefix tailTrace_2829776
  have hstable : (prefixWord ++ tailWord_2829776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829776).length < 2 ^ (prefixWord ++ tailWord_2829776).sum := by decide
  have hdescent : baseEnd_2829776 < baseStart_2829776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829793 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 3, 3, 2]
def baseStart_2829793 : Nat := 118140960795 + 2829793 * 2 ^ 59
def prefixEnd_2829793 : Nat := 4983230072969 + 3 ^ 40 * 2829793 * 2
def baseEnd_2829793 : Nat := 1453043961728552155573525

theorem tailTrace_2829793 : CollatzResearch.WordTrace tailWord_2829793 prefixEnd_2829793 1453043961728552155573525 := by
  unfold tailWord_2829793
  simp only [CollatzResearch.WordTrace]
  refine ⟨103211029837150726012814033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68807353224767150675209355 103211029837150726012814033)
  ·
    refine ⟨77408272377863044509610525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103211029837150726012814033 77408272377863044509610525)
    ·
      refine ⟨29028102141698641691103947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77408272377863044509610525 29028102141698641691103947)
      ·
        refine ⟨43542153212547962536655921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29028102141698641691103947 43542153212547962536655921)
        ·
          refine ⟨32656614909410971902491941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43542153212547962536655921 32656614909410971902491941)
          ·
            refine ⟨6123115295514557231717239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32656614909410971902491941 6123115295514557231717239)
            ·
              refine ⟨9184672943271835847575859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6123115295514557231717239 9184672943271835847575859)
              ·
                refine ⟨13777009414907753771363789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9184672943271835847575859 13777009414907753771363789)
                ·
                  refine ⟨5166378530590407664261421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13777009414907753771363789 5166378530590407664261421)
                  ·
                    refine ⟨1937391948971402874098033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5166378530590407664261421 1937391948971402874098033)
                    ·
                      refine ⟨1453043961728552155573525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1937391948971402874098033 1453043961728552155573525)
                      ·
                        rfl

theorem cell23_2829793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_2829793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829793 prefixEnd_2829793 := by exact prefixLift 2829793
  have htrace : WordTrace (prefixWord ++ tailWord_2829793) baseStart_2829793 baseEnd_2829793 := by
    simpa [prefixWord, tailWord_2829793, baseEnd_2829793] using wordTrace_append hprefix tailTrace_2829793
  have hstable : (prefixWord ++ tailWord_2829793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829793).length < 2 ^ (prefixWord ++ tailWord_2829793).sum := by decide
  have hdescent : baseEnd_2829793 < baseStart_2829793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829819 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 4]
def baseStart_2829819 : Nat := 118140960795 + 2829819 * 2 ^ 59
def prefixEnd_2829819 : Nat := 4983230072969 + 3 ^ 40 * 2829819 * 2
def baseEnd_2829819 : Nat := 1453057312225569053848405

theorem tailTrace_2829819 : CollatzResearch.WordTrace tailWord_2829819 prefixEnd_2829819 1453057312225569053848405 := by
  unfold tailWord_2829819
  simp only [CollatzResearch.WordTrace]
  refine ⟨103211978135056532453260511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68807985423371021635507007 103211978135056532453260511)
  ·
    refine ⟨154817967202584798679890767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103211978135056532453260511 154817967202584798679890767)
    ·
      refine ⟨232226950803877198019836151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154817967202584798679890767 232226950803877198019836151)
      ·
        refine ⟨348340426205815797029754227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232226950803877198019836151 348340426205815797029754227)
        ·
          refine ⟨522510639308723695544631341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348340426205815797029754227 522510639308723695544631341)
          ·
            refine ⟨195941489740771385829236753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 522510639308723695544631341 195941489740771385829236753)
            ·
              refine ⟨146956117305578539371927565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195941489740771385829236753 146956117305578539371927565)
              ·
                refine ⟨55108543989591952264472837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146956117305578539371927565 55108543989591952264472837)
                ·
                  refine ⟨10332851998048491049588657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55108543989591952264472837 10332851998048491049588657)
                  ·
                    refine ⟨7749638998536368287191493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10332851998048491049588657 7749638998536368287191493)
                    ·
                      refine ⟨1453057312225569053848405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7749638998536368287191493 1453057312225569053848405)
                      ·
                        rfl

theorem cell23_2829819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 4].length) (baseStart_2829819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829819 prefixEnd_2829819 := by exact prefixLift 2829819
  have htrace : WordTrace (prefixWord ++ tailWord_2829819) baseStart_2829819 baseEnd_2829819 := by
    simpa [prefixWord, tailWord_2829819, baseEnd_2829819] using wordTrace_append hprefix tailTrace_2829819
  have hstable : (prefixWord ++ tailWord_2829819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829819).length < 2 ^ (prefixWord ++ tailWord_2829819).sum := by decide
  have hdescent : baseEnd_2829819 < baseStart_2829819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829829 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 7]
def baseStart_2829829 : Nat := 118140960795 + 2829829 * 2 ^ 59
def prefixEnd_2829829 : Nat := 4983230072969 + 3 ^ 40 * 2829829 * 2
def baseEnd_2829829 : Nat := 161451383003568223858151

theorem tailTrace_2829829 : CollatzResearch.WordTrace tailWord_2829829 prefixEnd_2829829 161451383003568223858151 := by
  unfold tailWord_2829829
  simp only [CollatzResearch.WordTrace]
  refine ⟨103212342865020304161124541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68808228576680202774083027 103212342865020304161124541)
  ·
    refine ⟨38704628574382614060421703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103212342865020304161124541 38704628574382614060421703)
    ·
      refine ⟨58056942861573921090632555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38704628574382614060421703 58056942861573921090632555)
      ·
        refine ⟨87085414292360881635948833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58056942861573921090632555 87085414292360881635948833)
        ·
          refine ⟨65314060719270661226961625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87085414292360881635948833 65314060719270661226961625)
          ·
            refine ⟨48985545539452995920221219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65314060719270661226961625 48985545539452995920221219)
            ·
              refine ⟨73478318309179493880331829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48985545539452995920221219 73478318309179493880331829)
              ·
                refine ⟨6888592341485577551281109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73478318309179493880331829 6888592341485577551281109)
                ·
                  refine ⟨161451383003568223858151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6888592341485577551281109 161451383003568223858151)
                  ·
                    rfl

theorem cell23_2829829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 7].length) (baseStart_2829829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829829 prefixEnd_2829829 := by exact prefixLift 2829829
  have htrace : WordTrace (prefixWord ++ tailWord_2829829) baseStart_2829829 baseEnd_2829829 := by
    simpa [prefixWord, tailWord_2829829, baseEnd_2829829] using wordTrace_append hprefix tailTrace_2829829
  have hstable : (prefixWord ++ tailWord_2829829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829829).length < 2 ^ (prefixWord ++ tailWord_2829829).sum := by decide
  have hdescent : baseEnd_2829829 < baseStart_2829829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829936 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 8]
def baseStart_2829936 : Nat := 118140960795 + 2829936 * 2 ^ 59
def prefixEnd_2829936 : Nat := 4983230072969 + 3 ^ 40 * 2829936 * 2
def baseEnd_2829936 : Nat := 161457487718016121787263

theorem tailTrace_2829936 : CollatzResearch.WordTrace tailWord_2829936 prefixEnd_2829936 161457487718016121787263 := by
  unfold tailWord_2829936
  simp only [CollatzResearch.WordTrace]
  refine ⟨51608122737816330717634831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68810830317088440956846441 51608122737816330717634831)
  ·
    refine ⟨77412184106724496076452247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51608122737816330717634831 77412184106724496076452247)
    ·
      refine ⟨116118276160086744114678371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77412184106724496076452247 116118276160086744114678371)
      ·
        refine ⟨174177414240130116172017557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116118276160086744114678371 174177414240130116172017557)
        ·
          refine ⟨8164566292506099195563323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 174177414240130116172017557 8164566292506099195563323)
          ·
            refine ⟨12246849438759148793344985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8164566292506099195563323 12246849438759148793344985)
            ·
              refine ⟨9185137079069361595008739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12246849438759148793344985 9185137079069361595008739)
              ·
                refine ⟨13777705618604042392513109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9185137079069361595008739 13777705618604042392513109)
                ·
                  refine ⟨161457487718016121787263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13777705618604042392513109 161457487718016121787263)
                  ·
                    rfl

theorem cell23_2829936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 8].length) (baseStart_2829936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829936 prefixEnd_2829936 := by exact prefixLift 2829936
  have htrace : WordTrace (prefixWord ++ tailWord_2829936) baseStart_2829936 baseEnd_2829936 := by
    simpa [prefixWord, tailWord_2829936, baseEnd_2829936] using wordTrace_append hprefix tailTrace_2829936
  have hstable : (prefixWord ++ tailWord_2829936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829936).length < 2 ^ (prefixWord ++ tailWord_2829936).sum := by decide
  have hdescent : baseEnd_2829936 < baseStart_2829936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829946 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3]
def baseStart_2829946 : Nat := 118140960795 + 2829946 * 2 ^ 59
def prefixEnd_2829946 : Nat := 4983230072969 + 3 ^ 40 * 2829946 * 2
def baseEnd_2829946 : Nat := 1453122524268690056960321

theorem tailTrace_2829946 : CollatzResearch.WordTrace tailWord_2829946 prefixEnd_2829946 1453122524268690056960321 := by
  unfold tailWord_2829946
  simp only [CollatzResearch.WordTrace]
  refine ⟨25804152551399108285783423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68811073470397622095422461 25804152551399108285783423)
  ·
    refine ⟨38706228827098662428675135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25804152551399108285783423 38706228827098662428675135)
    ·
      refine ⟨58059343240647993643012703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38706228827098662428675135 58059343240647993643012703)
      ·
        refine ⟨87089014860971990464519055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58059343240647993643012703 87089014860971990464519055)
        ·
          refine ⟨130633522291457985696778583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87089014860971990464519055 130633522291457985696778583)
          ·
            refine ⟨195950283437186978545167875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130633522291457985696778583 195950283437186978545167875)
            ·
              refine ⟨293925425155780467817751813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195950283437186978545167875 293925425155780467817751813)
              ·
                refine ⟨55111017216708837715828465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 293925425155780467817751813 55111017216708837715828465)
                ·
                  refine ⟨41333262912531628286871349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55111017216708837715828465 41333262912531628286871349)
                  ·
                    refine ⟨3874993398049840151894189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41333262912531628286871349 3874993398049840151894189)
                    ·
                      refine ⟨1453122524268690056960321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3874993398049840151894189 1453122524268690056960321)
                      ·
                        rfl

theorem cell23_2829946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_2829946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829946 prefixEnd_2829946 := by exact prefixLift 2829946
  have htrace : WordTrace (prefixWord ++ tailWord_2829946) baseStart_2829946 baseEnd_2829946 := by
    simpa [prefixWord, tailWord_2829946, baseEnd_2829946] using wordTrace_append hprefix tailTrace_2829946
  have hstable : (prefixWord ++ tailWord_2829946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829946).length < 2 ^ (prefixWord ++ tailWord_2829946).sum := by decide
  have hdescent : baseEnd_2829946 < baseStart_2829946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829953 : List Nat := [1, 2, 4, 2, 1, 3, 1, 3, 6]
def baseStart_2829953 : Nat := 118140960795 + 2829953 * 2 ^ 59
def prefixEnd_2829953 : Nat := 4983230072969 + 3 ^ 40 * 2829953 * 2
def baseEnd_2829953 : Nat := 161458457625919058841421

theorem tailTrace_2829953 : CollatzResearch.WordTrace tailWord_2829953 prefixEnd_2829953 161458457625919058841421 := by
  unfold tailWord_2829953
  simp only [CollatzResearch.WordTrace]
  refine ⟨103216865516571073338638513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68811243677714048892425675 103216865516571073338638513)
  ·
    refine ⟨77412649137428305003978885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103216865516571073338638513 77412649137428305003978885)
    ·
      refine ⟨14514871713267807188246041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77412649137428305003978885 14514871713267807188246041)
      ·
        refine ⟨10886153784950855391184531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14514871713267807188246041 10886153784950855391184531)
        ·
          refine ⟨16329230677426283086776797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10886153784950855391184531 16329230677426283086776797)
          ·
            refine ⟨6123461504034856157541299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16329230677426283086776797 6123461504034856157541299)
            ·
              refine ⟨9185192256052284236311949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6123461504034856157541299 9185192256052284236311949)
              ·
                refine ⟨3444447096019606588616981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9185192256052284236311949 3444447096019606588616981)
                ·
                  refine ⟨161458457625919058841421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3444447096019606588616981 161458457625919058841421)
                  ·
                    rfl

theorem cell23_2829953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 6].length) (baseStart_2829953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829953 prefixEnd_2829953 := by exact prefixLift 2829953
  have htrace : WordTrace (prefixWord ++ tailWord_2829953) baseStart_2829953 baseEnd_2829953 := by
    simpa [prefixWord, tailWord_2829953, baseEnd_2829953] using wordTrace_append hprefix tailTrace_2829953
  have hstable : (prefixWord ++ tailWord_2829953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829953).length < 2 ^ (prefixWord ++ tailWord_2829953).sum := by decide
  have hdescent : baseEnd_2829953 < baseStart_2829953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829963 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 5, 1, 3]
def baseStart_2829963 : Nat := 118140960795 + 2829963 * 2 ^ 59
def prefixEnd_2829963 : Nat := 4983230072969 + 3 ^ 40 * 2829963 * 2
def baseEnd_2829963 : Nat := 1453131253439816490447743

theorem tailTrace_2829963 : CollatzResearch.WordTrace tailWord_2829963 prefixEnd_2829963 1453131253439816490447743 := by
  unfold tailWord_2829963
  simp only [CollatzResearch.WordTrace]
  refine ⟨103217230246534845046502543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68811486831023230031001695 103217230246534845046502543)
  ·
    refine ⟨154825845369802267569753815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103217230246534845046502543 154825845369802267569753815)
    ·
      refine ⟨232238768054703401354630723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154825845369802267569753815 232238768054703401354630723)
      ·
        refine ⟨348358152082055102031946085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232238768054703401354630723 348358152082055102031946085)
        ·
          refine ⟨65317153515385331630989891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 348358152082055102031946085 65317153515385331630989891)
          ·
            refine ⟨97975730273077997446484837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65317153515385331630989891 97975730273077997446484837)
            ·
              refine ⟨18370449426202124521215907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97975730273077997446484837 18370449426202124521215907)
              ·
                refine ⟨27555674139303186781823861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18370449426202124521215907 27555674139303186781823861)
                ·
                  refine ⟨2583344450559673760795987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27555674139303186781823861 2583344450559673760795987)
                  ·
                    refine ⟨3875016675839510641193981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2583344450559673760795987 3875016675839510641193981)
                    ·
                      refine ⟨1453131253439816490447743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3875016675839510641193981 1453131253439816490447743)
                      ·
                        rfl

theorem cell23_2829963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 1, 3].length) (baseStart_2829963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829963 prefixEnd_2829963 := by exact prefixLift 2829963
  have htrace : WordTrace (prefixWord ++ tailWord_2829963) baseStart_2829963 baseEnd_2829963 := by
    simpa [prefixWord, tailWord_2829963, baseEnd_2829963] using wordTrace_append hprefix tailTrace_2829963
  have hstable : (prefixWord ++ tailWord_2829963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829963).length < 2 ^ (prefixWord ++ tailWord_2829963).sum := by decide
  have hdescent : baseEnd_2829963 < baseStart_2829963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829973 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 1, 5, 2]
def baseStart_2829973 : Nat := 118140960795 + 2829973 * 2 ^ 59
def prefixEnd_2829973 : Nat := 4983230072969 + 3 ^ 40 * 2829973 * 2
def baseEnd_2829973 : Nat := 1453136388246361451322697

theorem tailTrace_2829973 : CollatzResearch.WordTrace tailWord_2829973 prefixEnd_2829973 1453136388246361451322697 := by
  unfold tailWord_2829973
  simp only [CollatzResearch.WordTrace]
  refine ⟨103217594976498616754366573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68811729984332411169577715 103217594976498616754366573)
  ·
    refine ⟨38706598116186981282887465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103217594976498616754366573 38706598116186981282887465)
    ·
      refine ⟨29029948587140235962165599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38706598116186981282887465 29029948587140235962165599)
      ·
        refine ⟨43544922880710353943248399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29029948587140235962165599 43544922880710353943248399)
        ·
          refine ⟨65317384321065530914872599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43544922880710353943248399 65317384321065530914872599)
          ·
            refine ⟨97976076481598296372308899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65317384321065530914872599 97976076481598296372308899)
            ·
              refine ⟨146964114722397444558463349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97976076481598296372308899 146964114722397444558463349)
              ·
                refine ⟨13777885755224760427355939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146964114722397444558463349 13777885755224760427355939)
                ·
                  refine ⟨20666828632837140641033909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13777885755224760427355939 20666828632837140641033909)
                  ·
                    refine ⟨1937515184328481935096929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20666828632837140641033909 1937515184328481935096929)
                    ·
                      refine ⟨1453136388246361451322697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1937515184328481935096929 1453136388246361451322697)
                      ·
                        rfl

theorem cell23_2829973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_2829973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2829973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2829973 prefixEnd_2829973 := by exact prefixLift 2829973
  have htrace : WordTrace (prefixWord ++ tailWord_2829973) baseStart_2829973 baseEnd_2829973 := by
    simpa [prefixWord, tailWord_2829973, baseEnd_2829973] using wordTrace_append hprefix tailTrace_2829973
  have hstable : (prefixWord ++ tailWord_2829973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829973).length < 2 ^ (prefixWord ++ tailWord_2829973).sum := by decide
  have hdescent : baseEnd_2829973 < baseStart_2829973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830013 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 1, 6]
def baseStart_2830013 : Nat := 118140960795 + 2830013 * 2 ^ 59
def prefixEnd_2830013 : Nat := 4983230072969 + 3 ^ 40 * 2830013 * 2
def baseEnd_2830013 : Nat := 484385642490847098274171

theorem tailTrace_2830013 : CollatzResearch.WordTrace tailWord_2830013 prefixEnd_2830013 484385642490847098274171 := by
  unfold tailWord_2830013
  simp only [CollatzResearch.WordTrace]
  refine ⟨103219053896353703585822693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68812702597569135723881795 103219053896353703585822693)
  ·
    refine ⟨19353572605566319422341755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103219053896353703585822693 19353572605566319422341755)
    ·
      refine ⟨29030358908349479133512633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19353572605566319422341755 29030358908349479133512633)
      ·
        refine ⟨21772769181262109350134475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29030358908349479133512633 21772769181262109350134475)
        ·
          refine ⟨32659153771893164025201713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21772769181262109350134475 32659153771893164025201713)
          ·
            refine ⟨24494365328919873018901285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32659153771893164025201713 24494365328919873018901285)
            ·
              refine ⟨4592693499172476191043991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24494365328919873018901285 4592693499172476191043991)
              ·
                refine ⟨6889040248758714286565987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4592693499172476191043991 6889040248758714286565987)
                ·
                  refine ⟨10333560373138071429848981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6889040248758714286565987 10333560373138071429848981)
                  ·
                    refine ⟨484385642490847098274171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10333560373138071429848981 484385642490847098274171)
                    ·
                      rfl

theorem cell23_2830013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_2830013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830013 prefixEnd_2830013 := by exact prefixLift 2830013
  have htrace : WordTrace (prefixWord ++ tailWord_2830013) baseStart_2830013 baseEnd_2830013 := by
    simpa [prefixWord, tailWord_2830013, baseEnd_2830013] using wordTrace_append hprefix tailTrace_2830013
  have hstable : (prefixWord ++ tailWord_2830013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830013).length < 2 ^ (prefixWord ++ tailWord_2830013).sum := by decide
  have hdescent : baseEnd_2830013 < baseStart_2830013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830018 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_2830018 : Nat := 118140960795 + 2830018 * 2 ^ 59
def prefixEnd_2830018 : Nat := 4983230072969 + 3 ^ 40 * 2830018 * 2
def baseEnd_2830018 : Nat := 1453159494875813775259991

theorem tailTrace_2830018 : CollatzResearch.WordTrace tailWord_2830018 prefixEnd_2830018 1453159494875813775259991 := by
  unfold tailWord_2830018
  simp only [CollatzResearch.WordTrace]
  refine ⟨25804809065333897359938677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68812824174223726293169805 25804809065333897359938677)
  ·
    refine ⟨2419200849875052877494251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25804809065333897359938677 2419200849875052877494251)
    ·
      refine ⟨3628801274812579316241377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2419200849875052877494251 3628801274812579316241377)
      ·
        refine ⟨2721600956109434487181033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3628801274812579316241377 2721600956109434487181033)
        ·
          refine ⟨2041200717082075865385775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2721600956109434487181033 2041200717082075865385775)
          ·
            refine ⟨3061801075623113798078663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041200717082075865385775 3061801075623113798078663)
            ·
              refine ⟨4592701613434670697117995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3061801075623113798078663 4592701613434670697117995)
              ·
                refine ⟨6889052420152006045676993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4592701613434670697117995 6889052420152006045676993)
                ·
                  refine ⟨5166789315114004534257745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6889052420152006045676993 5166789315114004534257745)
                  ·
                    refine ⟨3875091986335503400693309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5166789315114004534257745 3875091986335503400693309)
                    ·
                      refine ⟨1453159494875813775259991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3875091986335503400693309 1453159494875813775259991)
                      ·
                        rfl

theorem cell23_2830018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_2830018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830018 prefixEnd_2830018 := by exact prefixLift 2830018
  have htrace : WordTrace (prefixWord ++ tailWord_2830018) baseStart_2830018 baseEnd_2830018 := by
    simpa [prefixWord, tailWord_2830018, baseEnd_2830018] using wordTrace_append hprefix tailTrace_2830018
  have hstable : (prefixWord ++ tailWord_2830018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830018).length < 2 ^ (prefixWord ++ tailWord_2830018).sum := by decide
  have hdescent : baseEnd_2830018 < baseStart_2830018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830020 : List Nat := [2, 3, 3, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_2830020 : Nat := 118140960795 + 2830020 * 2 ^ 59
def prefixEnd_2830020 : Nat := 4983230072969 + 3 ^ 40 * 2830020 * 2
def baseEnd_2830020 : Nat := 1453160521837122767434981

theorem tailTrace_2830020 : CollatzResearch.WordTrace tailWord_2830020 prefixEnd_2830020 1453160521837122767434981 := by
  unfold tailWord_2830020
  simp only [CollatzResearch.WordTrace]
  refine ⟨51609654603664171890663757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68812872804885562520885009 51609654603664171890663757)
  ·
    refine ⟨19353620476374064458998909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51609654603664171890663757 19353620476374064458998909)
    ·
      refine ⟨7257607678640274172124591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19353620476374064458998909 7257607678640274172124591)
      ·
        refine ⟨10886411517960411258186887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7257607678640274172124591 10886411517960411258186887)
        ·
          refine ⟨16329617276940616887280331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10886411517960411258186887 16329617276940616887280331)
          ·
            refine ⟨24494425915410925330920497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16329617276940616887280331 24494425915410925330920497)
            ·
              refine ⟨18370819436558193998190373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24494425915410925330920497 18370819436558193998190373)
              ·
                refine ⟨3444528644354661374660695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18370819436558193998190373 3444528644354661374660695)
                ·
                  refine ⟨5166792966531992061991043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3444528644354661374660695 5166792966531992061991043)
                  ·
                    refine ⟨7750189449797988092986565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5166792966531992061991043 7750189449797988092986565)
                    ·
                      refine ⟨1453160521837122767434981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7750189449797988092986565 1453160521837122767434981)
                      ·
                        rfl

theorem cell23_2830020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_2830020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830020 prefixEnd_2830020 := by exact prefixLift 2830020
  have htrace : WordTrace (prefixWord ++ tailWord_2830020) baseStart_2830020 baseEnd_2830020 := by
    simpa [prefixWord, tailWord_2830020, baseEnd_2830020] using wordTrace_append hprefix tailTrace_2830020
  have hstable : (prefixWord ++ tailWord_2830020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830020).length < 2 ^ (prefixWord ++ tailWord_2830020).sum := by decide
  have hdescent : baseEnd_2830020 < baseStart_2830020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830023 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 3]
def baseStart_2830023 : Nat := 118140960795 + 2830023 * 2 ^ 59
def prefixEnd_2830023 : Nat := 4983230072969 + 3 ^ 40 * 2830023 * 2
def baseEnd_2830023 : Nat := 1453162062279086255697467

theorem tailTrace_2830023 : CollatzResearch.WordTrace tailWord_2830023 prefixEnd_2830023 1453162062279086255697467 := by
  unfold tailWord_2830023
  simp only [CollatzResearch.WordTrace]
  refine ⟨103219418626317475293686723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68812945750878316862457815 103219418626317475293686723)
  ·
    refine ⟨154829127939476212940530085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103219418626317475293686723 154829127939476212940530085)
    ·
      refine ⟨29030461488651789926349391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154829127939476212940530085 29030461488651789926349391)
      ·
        refine ⟨43545692232977684889524087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29030461488651789926349391 43545692232977684889524087)
        ·
          refine ⟨65318538349466527334286131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43545692232977684889524087 65318538349466527334286131)
          ·
            refine ⟨97977807524199791001429197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65318538349466527334286131 97977807524199791001429197)
            ·
              refine ⟨36741677821574921625535949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97977807524199791001429197 36741677821574921625535949)
              ·
                refine ⟨13778129183090595609575981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36741677821574921625535949 13778129183090595609575981)
                ·
                  refine ⟨5166798443658973353590993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13778129183090595609575981 5166798443658973353590993)
                  ·
                    refine ⟨3875098832744230015193245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5166798443658973353590993 3875098832744230015193245)
                    ·
                      refine ⟨1453162062279086255697467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3875098832744230015193245 1453162062279086255697467)
                      ·
                        rfl

theorem cell23_2830023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_2830023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830023 prefixEnd_2830023 := by exact prefixLift 2830023
  have htrace : WordTrace (prefixWord ++ tailWord_2830023) baseStart_2830023 baseEnd_2830023 := by
    simpa [prefixWord, tailWord_2830023, baseEnd_2830023] using wordTrace_append hprefix tailTrace_2830023
  have hstable : (prefixWord ++ tailWord_2830023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830023).length < 2 ^ (prefixWord ++ tailWord_2830023).sum := by decide
  have hdescent : baseEnd_2830023 < baseStart_2830023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830033 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 1, 2, 4]
def baseStart_2830033 : Nat := 118140960795 + 2830033 * 2 ^ 59
def prefixEnd_2830033 : Nat := 4983230072969 + 3 ^ 40 * 2830033 * 2
def baseEnd_2830033 : Nat := 1453167197085631216572421

theorem tailTrace_2830033 : CollatzResearch.WordTrace tailWord_2830033 prefixEnd_2830033 1453167197085631216572421 := by
  unfold tailWord_2830033
  simp only [CollatzResearch.WordTrace]
  refine ⟨103219783356281247001550753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68813188904187498001033835 103219783356281247001550753)
  ·
    refine ⟨77414837517210935251163065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103219783356281247001550753 77414837517210935251163065)
    ·
      refine ⟨58061128137908201438372299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77414837517210935251163065 58061128137908201438372299)
      ·
        refine ⟨87091692206862302157558449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58061128137908201438372299 87091692206862302157558449)
        ·
          refine ⟨65318769155146726618168837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87091692206862302157558449 65318769155146726618168837)
          ·
            refine ⟨12247269216590011240906657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65318769155146726618168837 12247269216590011240906657)
            ·
              refine ⟨9185451912442508430679993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12247269216590011240906657 9185451912442508430679993)
              ·
                refine ⟨6889088934331881323009995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9185451912442508430679993 6889088934331881323009995)
                ·
                  refine ⟨10333633401497821984514993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6889088934331881323009995 10333633401497821984514993)
                  ·
                    refine ⟨7750225051123366488386245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10333633401497821984514993 7750225051123366488386245)
                    ·
                      refine ⟨1453167197085631216572421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7750225051123366488386245 1453167197085631216572421)
                      ·
                        rfl

theorem cell23_2830033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_2830033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830033 prefixEnd_2830033 := by exact prefixLift 2830033
  have htrace : WordTrace (prefixWord ++ tailWord_2830033) baseStart_2830033 baseEnd_2830033 := by
    simpa [prefixWord, tailWord_2830033, baseEnd_2830033] using wordTrace_append hprefix tailTrace_2830033
  have hstable : (prefixWord ++ tailWord_2830033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830033).length < 2 ^ (prefixWord ++ tailWord_2830033).sum := by decide
  have hdescent : baseEnd_2830033 < baseStart_2830033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830040 : List Nat := [2, 1, 2, 2, 3, 1, 3, 3, 1, 2, 3]
def baseStart_2830040 : Nat := 118140960795 + 2830040 * 2 ^ 59
def prefixEnd_2830040 : Nat := 4983230072969 + 3 ^ 40 * 2830040 * 2
def baseEnd_2830040 : Nat := 1453170791450212689184889

theorem tailTrace_2830040 : CollatzResearch.WordTrace tailWord_2830040 prefixEnd_2830040 1453170791450212689184889 := by
  unfold tailWord_2830040
  simp only [CollatzResearch.WordTrace]
  refine ⟨51610019333627943598527787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68813359111503924798037049 51610019333627943598527787)
  ·
    refine ⟨77415029000441915397791681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51610019333627943598527787 77415029000441915397791681)
    ·
      refine ⟨58061271750331436548343761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77415029000441915397791681 58061271750331436548343761)
      ·
        refine ⟨43545953812748577411257821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58061271750331436548343761 43545953812748577411257821)
        ·
          refine ⟨16329732679780716529221683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43545953812748577411257821 16329732679780716529221683)
          ·
            refine ⟨24494599019671074793832525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16329732679780716529221683 24494599019671074793832525)
            ·
              refine ⟨9185474632376653047687197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24494599019671074793832525 9185474632376653047687197)
              ·
                refine ⟨3444552987141244892882699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9185474632376653047687197 3444552987141244892882699)
                ·
                  refine ⟨5166829480711867339324049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3444552987141244892882699 5166829480711867339324049)
                  ·
                    refine ⟨3875122110533900504493037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5166829480711867339324049 3875122110533900504493037)
                    ·
                      refine ⟨1453170791450212689184889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3875122110533900504493037 1453170791450212689184889)
                      ·
                        rfl

theorem cell23_2830040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_2830040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830040 prefixEnd_2830040 := by exact prefixLift 2830040
  have htrace : WordTrace (prefixWord ++ tailWord_2830040) baseStart_2830040 baseEnd_2830040 := by
    simpa [prefixWord, tailWord_2830040, baseEnd_2830040] using wordTrace_append hprefix tailTrace_2830040
  have hstable : (prefixWord ++ tailWord_2830040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830040).length < 2 ^ (prefixWord ++ tailWord_2830040).sum := by decide
  have hdescent : baseEnd_2830040 < baseStart_2830040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830127 : List Nat := [1, 1, 2, 1, 2, 1, 2, 7, 2, 2, 2]
def baseStart_2830127 : Nat := 118140960795 + 2830127 * 2 ^ 59
def prefixEnd_2830127 : Nat := 4983230072969 + 3 ^ 40 * 2830127 * 2
def baseEnd_2830127 : Nat := 1453215464267153848796989

theorem tailTrace_2830127 : CollatzResearch.WordTrace tailWord_2830127 prefixEnd_2830127 1453215464267153848796989 := by
  unfold tailWord_2830127
  simp only [CollatzResearch.WordTrace]
  refine ⟨103223211817940701055472635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68815474545293800703648423 103223211817940701055472635)
  ·
    refine ⟨154834817726911051583208953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103223211817940701055472635 154834817726911051583208953)
    ·
      refine ⟨116126113295183288687406715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154834817726911051583208953 116126113295183288687406715)
      ·
        refine ⟨174189169942774933031110073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116126113295183288687406715 174189169942774933031110073)
        ·
          refine ⟨130641877457081199773332555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174189169942774933031110073 130641877457081199773332555)
          ·
            refine ⟨195962816185621799659998833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130641877457081199773332555 195962816185621799659998833)
            ·
              refine ⟨146972112139216349744999125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195962816185621799659998833 146972112139216349744999125)
              ·
                refine ⟨3444658878262883197148417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 146972112139216349744999125 3444658878262883197148417)
                ·
                  refine ⟨2583494158697162397861313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3444658878262883197148417 2583494158697162397861313)
                  ·
                    refine ⟨1937620619022871798395985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2583494158697162397861313 1937620619022871798395985)
                    ·
                      refine ⟨1453215464267153848796989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1937620619022871798395985 1453215464267153848796989)
                      ·
                        rfl

theorem cell23_2830127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 2, 2].length) (baseStart_2830127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830127 prefixEnd_2830127 := by exact prefixLift 2830127
  have htrace : WordTrace (prefixWord ++ tailWord_2830127) baseStart_2830127 baseEnd_2830127 := by
    simpa [prefixWord, tailWord_2830127, baseEnd_2830127] using wordTrace_append hprefix tailTrace_2830127
  have hstable : (prefixWord ++ tailWord_2830127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830127).length < 2 ^ (prefixWord ++ tailWord_2830127).sum := by decide
  have hdescent : baseEnd_2830127 < baseStart_2830127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830131 : List Nat := [1, 1, 1, 2, 8, 1, 1, 2, 1, 3, 2]
def baseStart_2830131 : Nat := 118140960795 + 2830131 * 2 ^ 59
def prefixEnd_2830131 : Nat := 4983230072969 + 3 ^ 40 * 2830131 * 2
def baseEnd_2830131 : Nat := 1453217518189771833146971

theorem tailTrace_2830131 : CollatzResearch.WordTrace tailWord_2830131 prefixEnd_2830131 1453217518189771833146971 := by
  unfold tailWord_2830131
  simp only [CollatzResearch.WordTrace]
  refine ⟨103223357709926209738618247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68815571806617473159078831 103223357709926209738618247)
  ·
    refine ⟨154835036564889314607927371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103223357709926209738618247 154835036564889314607927371)
    ·
      refine ⟨232252554847333971911891057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154835036564889314607927371 232252554847333971911891057)
      ·
        refine ⟨174189416135500478933918293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232252554847333971911891057 174189416135500478933918293)
        ·
          refine ⟨2041282220337896237506855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 174189416135500478933918293 2041282220337896237506855)
          ·
            refine ⟨3061923330506844356260283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041282220337896237506855 3061923330506844356260283)
            ·
              refine ⟨4592884995760266534390425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3061923330506844356260283 4592884995760266534390425)
              ·
                refine ⟨3444663746820199900792819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4592884995760266534390425 3444663746820199900792819)
                ·
                  refine ⟨5166995620230299851189229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3444663746820199900792819 5166995620230299851189229)
                  ·
                    refine ⟨1937623357586362444195961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5166995620230299851189229 1937623357586362444195961)
                    ·
                      refine ⟨1453217518189771833146971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1937623357586362444195961 1453217518189771833146971)
                      ·
                        rfl

theorem cell23_2830131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 1, 3, 2].length) (baseStart_2830131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830131 prefixEnd_2830131 := by exact prefixLift 2830131
  have htrace : WordTrace (prefixWord ++ tailWord_2830131) baseStart_2830131 baseEnd_2830131 := by
    simpa [prefixWord, tailWord_2830131, baseEnd_2830131] using wordTrace_append hprefix tailTrace_2830131
  have hstable : (prefixWord ++ tailWord_2830131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830131).length < 2 ^ (prefixWord ++ tailWord_2830131).sum := by decide
  have hdescent : baseEnd_2830131 < baseStart_2830131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830167 : List Nat := [1, 1, 3, 2, 5, 1, 1, 4, 5]
def baseStart_2830167 : Nat := 118140960795 + 2830167 * 2 ^ 59
def prefixEnd_2830167 : Nat := 4983230072969 + 3 ^ 40 * 2830167 * 2
def baseEnd_2830167 : Nat := 161470667054814854699645

theorem tailTrace_2830167 : CollatzResearch.WordTrace tailWord_2830167 prefixEnd_2830167 161470667054814854699645 := by
  unfold tailWord_2830167
  simp only [CollatzResearch.WordTrace]
  refine ⟨103224670737795787886928755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68816447158530525257952503 103224670737795787886928755)
  ·
    refine ⟨154837006106693681830393133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103224670737795787886928755 154837006106693681830393133)
    ·
      refine ⟨58063877290010130686397425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154837006106693681830393133 58063877290010130686397425)
      ·
        refine ⟨43547907967507598014798069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58063877290010130686397425 43547907967507598014798069)
        ·
          refine ⟨4082616371953837313887319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43547907967507598014798069 4082616371953837313887319)
          ·
            refine ⟨6123924557930755970830979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4082616371953837313887319 6123924557930755970830979)
            ·
              refine ⟨9185886836896133956246469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6123924557930755970830979 9185886836896133956246469)
              ·
                refine ⟨1722353781918025116796213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9185886836896133956246469 1722353781918025116796213)
                ·
                  refine ⟨161470667054814854699645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1722353781918025116796213 161470667054814854699645)
                  ·
                    rfl

theorem cell23_2830167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 5].length) (baseStart_2830167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830167 prefixEnd_2830167 := by exact prefixLift 2830167
  have htrace : WordTrace (prefixWord ++ tailWord_2830167) baseStart_2830167 baseEnd_2830167 := by
    simpa [prefixWord, tailWord_2830167, baseEnd_2830167] using wordTrace_append hprefix tailTrace_2830167
  have hstable : (prefixWord ++ tailWord_2830167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830167).length < 2 ^ (prefixWord ++ tailWord_2830167).sum := by decide
  have hdescent : baseEnd_2830167 < baseStart_2830167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830170 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2]
def baseStart_2830170 : Nat := 118140960795 + 2830170 * 2 ^ 59
def prefixEnd_2830170 : Nat := 4983230072969 + 3 ^ 40 * 2830170 * 2
def baseEnd_2830170 : Nat := 1453237543935297180559291

theorem tailTrace_2830170 : CollatzResearch.WordTrace tailWord_2830170 prefixEnd_2830170 1453237543935297180559291 := by
  unfold tailWord_2830170
  simp only [CollatzResearch.WordTrace]
  refine ⟨25806195039196229849821991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68816520104523279599525309 25806195039196229849821991)
  ·
    refine ⟨38709292558794344774732987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25806195039196229849821991 38709292558794344774732987)
    ·
      refine ⟨58063938838191517162099481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38709292558794344774732987 58063938838191517162099481)
      ·
        refine ⟨43547954128643637871574611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58063938838191517162099481 43547954128643637871574611)
        ·
          refine ⟨65321931192965456807361917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43547954128643637871574611 65321931192965456807361917)
          ·
            refine ⟨24495724197362046302760719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65321931192965456807361917 24495724197362046302760719)
            ·
              refine ⟨36743586296043069454141079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24495724197362046302760719 36743586296043069454141079)
              ·
                refine ⟨55115379444064604181211619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36743586296043069454141079 55115379444064604181211619)
                ·
                  refine ⟨82673069166096906271817429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55115379444064604181211619 82673069166096906271817429)
                  ·
                    refine ⟨1937650058580396240745721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 82673069166096906271817429 1937650058580396240745721)
                    ·
                      refine ⟨1453237543935297180559291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1937650058580396240745721 1453237543935297180559291)
                      ·
                        rfl

theorem cell23_2830170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_2830170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830170 prefixEnd_2830170 := by exact prefixLift 2830170
  have htrace : WordTrace (prefixWord ++ tailWord_2830170) baseStart_2830170 baseEnd_2830170 := by
    simpa [prefixWord, tailWord_2830170, baseEnd_2830170] using wordTrace_append hprefix tailTrace_2830170
  have hstable : (prefixWord ++ tailWord_2830170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830170).length < 2 ^ (prefixWord ++ tailWord_2830170).sum := by decide
  have hdescent : baseEnd_2830170 < baseStart_2830170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830213 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 1, 3, 6]
def baseStart_2830213 : Nat := 118140960795 + 2830213 * 2 ^ 59
def prefixEnd_2830213 : Nat := 4983230072969 + 3 ^ 40 * 2830213 * 2
def baseEnd_2830213 : Nat := 1453259623603440512321593

theorem tailTrace_2830213 : CollatzResearch.WordTrace tailWord_2830213 prefixEnd_2830213 1453259623603440512321593 := by
  unfold tailWord_2830213
  simp only [CollatzResearch.WordTrace]
  refine ⟨103226348495629137743103293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68817565663752758495402195 103226348495629137743103293)
  ·
    refine ⟨38709880685860926653663735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103226348495629137743103293 38709880685860926653663735)
    ·
      refine ⟨58064821028791389980495603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38709880685860926653663735 58064821028791389980495603)
      ·
        refine ⟨87097231543187084970743405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58064821028791389980495603 87097231543187084970743405)
        ·
          refine ⟨32661461828695156864028777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87097231543187084970743405 32661461828695156864028777)
          ·
            refine ⟨24496096371521367648021583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32661461828695156864028777 24496096371521367648021583)
            ·
              refine ⟨36744144557282051472032375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24496096371521367648021583 36744144557282051472032375)
              ·
                refine ⟨55116216835923077208048563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36744144557282051472032375 55116216835923077208048563)
                ·
                  refine ⟨82674325253884615812072845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55116216835923077208048563 82674325253884615812072845)
                  ·
                    refine ⟨31002871970206730929527317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82674325253884615812072845 31002871970206730929527317)
                    ·
                      refine ⟨1453259623603440512321593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31002871970206730929527317 1453259623603440512321593)
                      ·
                        rfl

theorem cell23_2830213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_2830213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830213 prefixEnd_2830213 := by exact prefixLift 2830213
  have htrace : WordTrace (prefixWord ++ tailWord_2830213) baseStart_2830213 baseEnd_2830213 := by
    simpa [prefixWord, tailWord_2830213, baseEnd_2830213] using wordTrace_append hprefix tailTrace_2830213
  have hstable : (prefixWord ++ tailWord_2830213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830213).length < 2 ^ (prefixWord ++ tailWord_2830213).sum := by decide
  have hdescent : baseEnd_2830213 < baseStart_2830213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830220 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 4, 2, 3]
def baseStart_2830220 : Nat := 118140960795 + 2830220 * 2 ^ 59
def prefixEnd_2830220 : Nat := 4983230072969 + 3 ^ 40 * 2830220 * 2
def baseEnd_2830220 : Nat := 1453263217968021984934061

theorem tailTrace_2830220 : CollatzResearch.WordTrace tailWord_2830220 prefixEnd_2830220 1453263217968021984934061 := by
  unfold tailWord_2830220
  simp only [CollatzResearch.WordTrace]
  refine ⟨51613301903301888969304057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68817735871069185292405409 51613301903301888969304057)
  ·
    refine ⟨38709976427476416726978043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51613301903301888969304057 38709976427476416726978043)
    ·
      refine ⟨58064964641214625090467065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38709976427476416726978043 58064964641214625090467065)
      ·
        refine ⟨43548723480910968817850299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58064964641214625090467065 43548723480910968817850299)
        ·
          refine ⟨65323085221366453226775449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43548723480910968817850299 65323085221366453226775449)
          ·
            refine ⟨48992313916024839920081587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65323085221366453226775449 48992313916024839920081587)
            ·
              refine ⟨73488470874037259880122381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48992313916024839920081587 73488470874037259880122381)
              ·
                refine ⟨27558176577763972455045893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73488470874037259880122381 27558176577763972455045893)
                ·
                  refine ⟨5167158108330744835321105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27558176577763972455045893 5167158108330744835321105)
                  ·
                    refine ⟨3875368581248058626490829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5167158108330744835321105 3875368581248058626490829)
                    ·
                      refine ⟨1453263217968021984934061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3875368581248058626490829 1453263217968021984934061)
                      ·
                        rfl

theorem cell23_2830220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_2830220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830220 prefixEnd_2830220 := by exact prefixLift 2830220
  have htrace : WordTrace (prefixWord ++ tailWord_2830220) baseStart_2830220 baseEnd_2830220 := by
    simpa [prefixWord, tailWord_2830220, baseEnd_2830220] using wordTrace_append hprefix tailTrace_2830220
  have hstable : (prefixWord ++ tailWord_2830220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830220).length < 2 ^ (prefixWord ++ tailWord_2830220).sum := by decide
  have hdescent : baseEnd_2830220 < baseStart_2830220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830243 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 6]
def baseStart_2830243 : Nat := 118140960795 + 2830243 * 2 ^ 59
def prefixEnd_2830243 : Nat := 4983230072969 + 3 ^ 40 * 2830243 * 2
def baseEnd_2830243 : Nat := 1453275028023075394946455

theorem tailTrace_2830243 : CollatzResearch.WordTrace tailWord_2830243 prefixEnd_2830243 1453275028023075394946455 := by
  unfold tailWord_2830243
  simp only [CollatzResearch.WordTrace]
  refine ⟨103227442685520452866695383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68818295123680301911130255 103227442685520452866695383)
  ·
    refine ⟨154841164028280679300043075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103227442685520452866695383 154841164028280679300043075)
    ·
      refine ⟨232261746042421018950064613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154841164028280679300043075 232261746042421018950064613)
      ·
        refine ⟨43549077382953941053137115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232261746042421018950064613 43549077382953941053137115)
        ·
          refine ⟨65323616074430911579705673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43549077382953941053137115 65323616074430911579705673)
          ·
            refine ⟨48992712055823183684779255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65323616074430911579705673 48992712055823183684779255)
            ·
              refine ⟨73489068083734775527168883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48992712055823183684779255 73489068083734775527168883)
              ·
                refine ⟨110233602125602163290753325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73489068083734775527168883 110233602125602163290753325)
                ·
                  refine ⟨41337600797100811234032497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110233602125602163290753325 41337600797100811234032497)
                  ·
                    refine ⟨31003200597825608425524373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41337600797100811234032497 31003200597825608425524373)
                    ·
                      refine ⟨1453275028023075394946455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31003200597825608425524373 1453275028023075394946455)
                      ·
                        rfl

theorem cell23_2830243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_2830243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830243 prefixEnd_2830243 := by exact prefixLift 2830243
  have htrace : WordTrace (prefixWord ++ tailWord_2830243) baseStart_2830243 baseEnd_2830243 := by
    simpa [prefixWord, tailWord_2830243, baseEnd_2830243] using wordTrace_append hprefix tailTrace_2830243
  have hstable : (prefixWord ++ tailWord_2830243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830243).length < 2 ^ (prefixWord ++ tailWord_2830243).sum := by decide
  have hdescent : baseEnd_2830243 < baseStart_2830243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830261 : List Nat := [1, 3, 3, 2, 1, 4, 1, 3, 1, 4]
def baseStart_2830261 : Nat := 118140960795 + 2830261 * 2 ^ 59
def prefixEnd_2830261 : Nat := 4983230072969 + 3 ^ 40 * 2830261 * 2
def baseEnd_2830261 : Nat := 484428090224952108173791

theorem tailTrace_2830261 : CollatzResearch.WordTrace tailWord_2830261 prefixEnd_2830261 484428090224952108173791 := by
  unfold tailWord_2830261
  simp only [CollatzResearch.WordTrace]
  refine ⟨103228099199455241940850637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68818732799636827960567091 103228099199455241940850637)
  ·
    refine ⟨38710537199795715727818989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103228099199455241940850637 38710537199795715727818989)
    ·
      refine ⟨14516451449923393397932121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38710537199795715727818989 14516451449923393397932121)
      ·
        refine ⟨10887338587442545048449091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14516451449923393397932121 10887338587442545048449091)
        ·
          refine ⟨16331007881163817572673637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10887338587442545048449091 16331007881163817572673637)
          ·
            refine ⟨3062063977718215794876307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16331007881163817572673637 3062063977718215794876307)
            ·
              refine ⟨4593095966577323692314461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062063977718215794876307 4593095966577323692314461)
              ·
                refine ⟨1722410987466496384617923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4593095966577323692314461 1722410987466496384617923)
                ·
                  refine ⟨2583616481199744576926885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1722410987466496384617923 2583616481199744576926885)
                  ·
                    refine ⟨484428090224952108173791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2583616481199744576926885 484428090224952108173791)
                    ·
                      rfl

theorem cell23_2830261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_2830261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830261 prefixEnd_2830261 := by exact prefixLift 2830261
  have htrace : WordTrace (prefixWord ++ tailWord_2830261) baseStart_2830261 baseEnd_2830261 := by
    simpa [prefixWord, tailWord_2830261, baseEnd_2830261] using wordTrace_append hprefix tailTrace_2830261
  have hstable : (prefixWord ++ tailWord_2830261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830261).length < 2 ^ (prefixWord ++ tailWord_2830261).sum := by decide
  have hdescent : baseEnd_2830261 < baseStart_2830261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830284 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 3, 1, 3]
def baseStart_2830284 : Nat := 118140960795 + 2830284 * 2 ^ 59
def prefixEnd_2830284 : Nat := 4983230072969 + 3 ^ 40 * 2830284 * 2
def baseEnd_2830284 : Nat := 1453296080729909734533767

theorem tailTrace_2830284 : CollatzResearch.WordTrace tailWord_2830284 prefixEnd_2830284 1453296080729909734533767 := by
  unfold tailWord_2830284
  simp only [CollatzResearch.WordTrace]
  refine ⟨51614469039185958434468953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68819292052247944579291937 51614469039185958434468953)
  ·
    refine ⟨38710851779389468825851715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51614469039185958434468953 38710851779389468825851715)
    ·
      refine ⟨58066277669084203238777573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38710851779389468825851715 58066277669084203238777573)
      ·
        refine ⟨10887427062953288107270795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58066277669084203238777573 10887427062953288107270795)
        ·
          refine ⟨16331140594429932160906193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10887427062953288107270795 16331140594429932160906193)
          ·
            refine ⟨12248355445822449120679645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16331140594429932160906193 12248355445822449120679645)
            ·
              refine ⟨4593133292183418420254867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12248355445822449120679645 4593133292183418420254867)
              ·
                refine ⟨6889699938275127630382301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4593133292183418420254867 6889699938275127630382301)
                ·
                  refine ⟨2583637476853172861393363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6889699938275127630382301 2583637476853172861393363)
                  ·
                    refine ⟨3875456215279759292090045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2583637476853172861393363 3875456215279759292090045)
                    ·
                      refine ⟨1453296080729909734533767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3875456215279759292090045 1453296080729909734533767)
                      ·
                        rfl

theorem cell23_2830284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_2830284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830284 prefixEnd_2830284 := by exact prefixLift 2830284
  have htrace : WordTrace (prefixWord ++ tailWord_2830284) baseStart_2830284 baseEnd_2830284 := by
    simpa [prefixWord, tailWord_2830284, baseEnd_2830284] using wordTrace_append hprefix tailTrace_2830284
  have hstable : (prefixWord ++ tailWord_2830284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830284).length < 2 ^ (prefixWord ++ tailWord_2830284).sum := by decide
  have hdescent : baseEnd_2830284 < baseStart_2830284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830307 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 4]
def baseStart_2830307 : Nat := 118140960795 + 2830307 * 2 ^ 59
def prefixEnd_2830307 : Nat := 4983230072969 + 3 ^ 40 * 2830307 * 2
def baseEnd_2830307 : Nat := 1453307890784963144546161

theorem tailTrace_2830307 : CollatzResearch.WordTrace tailWord_2830307 prefixEnd_2830307 1453307890784963144546161 := by
  unfold tailWord_2830307
  simp only [CollatzResearch.WordTrace]
  refine ⟨103229776957288591797025175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68819851304859061198016783 103229776957288591797025175)
  ·
    refine ⟨154844665435932887695537763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103229776957288591797025175 154844665435932887695537763)
    ·
      refine ⟨232266998153899331543306645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154844665435932887695537763 232266998153899331543306645)
      ·
        refine ⟨10887515538464031166092499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 232266998153899331543306645 10887515538464031166092499)
        ·
          refine ⟨16331273307696046749138749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10887515538464031166092499 16331273307696046749138749)
          ·
            refine ⟨6124227490386017530927031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16331273307696046749138749 6124227490386017530927031)
            ·
              refine ⟨9186341235579026296390547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6124227490386017530927031 9186341235579026296390547)
              ·
                refine ⟨13779511853368539444585821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9186341235579026296390547 13779511853368539444585821)
                ·
                  refine ⟨5167316945013202291719683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13779511853368539444585821 5167316945013202291719683)
                  ·
                    refine ⟨7750975417519803437579525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5167316945013202291719683 7750975417519803437579525)
                    ·
                      refine ⟨1453307890784963144546161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7750975417519803437579525 1453307890784963144546161)
                      ·
                        rfl

theorem cell23_2830307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_2830307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830307 prefixEnd_2830307 := by exact prefixLift 2830307
  have htrace : WordTrace (prefixWord ++ tailWord_2830307) baseStart_2830307 baseEnd_2830307 := by
    simpa [prefixWord, tailWord_2830307, baseEnd_2830307] using wordTrace_append hprefix tailTrace_2830307
  have hstable : (prefixWord ++ tailWord_2830307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830307).length < 2 ^ (prefixWord ++ tailWord_2830307).sum := by decide
  have hdescent : baseEnd_2830307 < baseStart_2830307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830311 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 2, 3, 2]
def baseStart_2830311 : Nat := 118140960795 + 2830311 * 2 ^ 59
def prefixEnd_2830311 : Nat := 4983230072969 + 3 ^ 40 * 2830311 * 2
def baseEnd_2830311 : Nat := 1453309944707581128896143

theorem tailTrace_2830311 : CollatzResearch.WordTrace tailWord_2830311 prefixEnd_2830311 1453309944707581128896143 := by
  unfold tailWord_2830311
  simp only [CollatzResearch.WordTrace]
  refine ⟨103229922849274100480170787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68819948566182733653447191 103229922849274100480170787)
  ·
    refine ⟨154844884273911150720256181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103229922849274100480170787 154844884273911150720256181)
    ·
      refine ⟨14516707900679170380024017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154844884273911150720256181 14516707900679170380024017)
      ·
        refine ⟨10887530925509377785018013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14516707900679170380024017 10887530925509377785018013)
        ·
          refine ⟨4082824097066016669381755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10887530925509377785018013 4082824097066016669381755)
          ·
            refine ⟨6124236145599025004072633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4082824097066016669381755 6124236145599025004072633)
            ·
              refine ⟨4593177109199268753054475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6124236145599025004072633 4593177109199268753054475)
              ·
                refine ⟨6889765663798903129581713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4593177109199268753054475 6889765663798903129581713)
                ·
                  refine ⟨5167324247849177347186285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6889765663798903129581713 5167324247849177347186285)
                  ·
                    refine ⟨1937746592943441505194857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5167324247849177347186285 1937746592943441505194857)
                    ·
                      refine ⟨1453309944707581128896143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1937746592943441505194857 1453309944707581128896143)
                      ·
                        rfl

theorem cell23_2830311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_2830311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830311 prefixEnd_2830311 := by exact prefixLift 2830311
  have htrace : WordTrace (prefixWord ++ tailWord_2830311) baseStart_2830311 baseEnd_2830311 := by
    simpa [prefixWord, tailWord_2830311, baseEnd_2830311] using wordTrace_append hprefix tailTrace_2830311
  have hstable : (prefixWord ++ tailWord_2830311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830311).length < 2 ^ (prefixWord ++ tailWord_2830311).sum := by decide
  have hdescent : baseEnd_2830311 < baseStart_2830311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830320 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 4]
def baseStart_2830320 : Nat := 118140960795 + 2830320 * 2 ^ 59
def prefixEnd_2830320 : Nat := 4983230072969 + 3 ^ 40 * 2830320 * 2
def baseEnd_2830320 : Nat := 1453314566033471593683601

theorem tailTrace_2830320 : CollatzResearch.WordTrace tailWord_2830320 prefixEnd_2830320 1453314566033471593683601 := by
  unfold tailWord_2830320
  simp only [CollatzResearch.WordTrace]
  refine ⟨51615125553120747508624207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68820167404160996678165609 51615125553120747508624207)
  ·
    refine ⟨77422688329681121262936311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51615125553120747508624207 77422688329681121262936311)
    ·
      refine ⟨116134032494521681894404467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77422688329681121262936311 116134032494521681894404467)
      ·
        refine ⟨174201048741782522841606701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116134032494521681894404467 174201048741782522841606701)
        ·
          refine ⟨65325393278168446065602513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174201048741782522841606701 65325393278168446065602513)
          ·
            refine ⟨48994044958626334549201885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65325393278168446065602513 48994044958626334549201885)
            ·
              refine ⟨18372766859484875455950707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48994044958626334549201885 18372766859484875455950707)
              ·
                refine ⟨27559150289227313183926061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18372766859484875455950707 27559150289227313183926061)
                ·
                  refine ⟨10334681358460242443972273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27559150289227313183926061 10334681358460242443972273)
                  ·
                    refine ⟨7751011018845181832979205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10334681358460242443972273 7751011018845181832979205)
                    ·
                      refine ⟨1453314566033471593683601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7751011018845181832979205 1453314566033471593683601)
                      ·
                        rfl

theorem cell23_2830320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_2830320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830320 prefixEnd_2830320 := by exact prefixLift 2830320
  have htrace : WordTrace (prefixWord ++ tailWord_2830320) baseStart_2830320 baseEnd_2830320 := by
    simpa [prefixWord, tailWord_2830320, baseEnd_2830320] using wordTrace_append hprefix tailTrace_2830320
  have hstable : (prefixWord ++ tailWord_2830320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830320).length < 2 ^ (prefixWord ++ tailWord_2830320).sum := by decide
  have hdescent : baseEnd_2830320 < baseStart_2830320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830360 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 2, 7]
def baseStart_2830360 : Nat := 118140960795 + 2830360 * 2 ^ 59
def prefixEnd_2830360 : Nat := 4983230072969 + 3 ^ 40 * 2830360 * 2
def baseEnd_2830360 : Nat := 484445035086550479061139

theorem tailTrace_2830360 : CollatzResearch.WordTrace tailWord_2830360 prefixEnd_2830360 484445035086550479061139 := by
  unfold tailWord_2830360
  simp only [CollatzResearch.WordTrace]
  refine ⟨51615855013048290924352267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68821140017397721232469689 51615855013048290924352267)
  ·
    refine ⟨77423782519572436386528401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51615855013048290924352267 77423782519572436386528401)
    ·
      refine ⟨58067836889679327289896301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77423782519572436386528401 58067836889679327289896301)
      ·
        refine ⟨21775438833629747733711113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58067836889679327289896301 21775438833629747733711113)
        ·
          refine ⟨16331579125222310800283335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21775438833629747733711113 16331579125222310800283335)
          ·
            refine ⟨24497368687833466200425003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16331579125222310800283335 24497368687833466200425003)
            ·
              refine ⟨36746053031750199300637505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24497368687833466200425003 36746053031750199300637505)
              ·
                refine ⟨27559539773812649475478129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36746053031750199300637505 27559539773812649475478129)
                ·
                  refine ⟨20669654830359487106608597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27559539773812649475478129 20669654830359487106608597)
                  ·
                    refine ⟨484445035086550479061139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20669654830359487106608597 484445035086550479061139)
                    ·
                      rfl

theorem cell23_2830360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_2830360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830360 prefixEnd_2830360 := by exact prefixLift 2830360
  have htrace : WordTrace (prefixWord ++ tailWord_2830360) baseStart_2830360 baseEnd_2830360 := by
    simpa [prefixWord, tailWord_2830360, baseEnd_2830360] using wordTrace_append hprefix tailTrace_2830360
  have hstable : (prefixWord ++ tailWord_2830360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830360).length < 2 ^ (prefixWord ++ tailWord_2830360).sum := by decide
  have hdescent : baseEnd_2830360 < baseStart_2830360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830375 : List Nat := [1, 1, 7, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_2830375 : Nat := 118140960795 + 2830375 * 2 ^ 59
def prefixEnd_2830375 : Nat := 4983230072969 + 3 ^ 40 * 2830375 * 2
def baseEnd_2830375 : Nat := 1453342807469468878495849

theorem tailTrace_2830375 : CollatzResearch.WordTrace tailWord_2830375 prefixEnd_2830375 1453342807469468878495849 := by
  unfold tailWord_2830375
  simp only [CollatzResearch.WordTrace]
  refine ⟨103232257121042239410500579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68821504747361492940333719 103232257121042239410500579)
  ·
    refine ⟨154848385681563359115750869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103232257121042239410500579 154848385681563359115750869)
    ·
      refine ⟨3629259039411641229275411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 154848385681563359115750869 3629259039411641229275411)
      ·
        refine ⟨5443888559117461843913117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3629259039411641229275411 5443888559117461843913117)
        ·
          refine ⟨2041458209669048191467419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5443888559117461843913117 2041458209669048191467419)
          ·
            refine ⟨3062187314503572287201129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041458209669048191467419 3062187314503572287201129)
            ·
              refine ⟨2296640485877679215400847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3062187314503572287201129 2296640485877679215400847)
              ·
                refine ⟨3444960728816518823101271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2296640485877679215400847 3444960728816518823101271)
                ·
                  refine ⟨5167441093224778234651907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3444960728816518823101271 5167441093224778234651907)
                  ·
                    refine ⟨7751161639837167351977861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5167441093224778234651907 7751161639837167351977861)
                    ·
                      refine ⟨1453342807469468878495849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7751161639837167351977861 1453342807469468878495849)
                      ·
                        rfl

theorem cell23_2830375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_2830375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830375 prefixEnd_2830375 := by exact prefixLift 2830375
  have htrace : WordTrace (prefixWord ++ tailWord_2830375) baseStart_2830375 baseEnd_2830375 := by
    simpa [prefixWord, tailWord_2830375, baseEnd_2830375] using wordTrace_append hprefix tailTrace_2830375
  have hstable : (prefixWord ++ tailWord_2830375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830375).length < 2 ^ (prefixWord ++ tailWord_2830375).sum := by decide
  have hdescent : baseEnd_2830375 < baseStart_2830375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830378 : List Nat := [3, 1, 4, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_2830378 : Nat := 118140960795 + 2830378 * 2 ^ 59
def prefixEnd_2830378 : Nat := 4983230072969 + 3 ^ 40 * 2830378 * 2
def baseEnd_2830378 : Nat := 1453344347911432366758335

theorem tailTrace_2830378 : CollatzResearch.WordTrace tailWord_2830378 prefixEnd_2830378 1453344347911432366758335 := by
  unfold tailWord_2830378
  simp only [CollatzResearch.WordTrace]
  refine ⟨25808091635007842730714947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68821577693354247281906525 25808091635007842730714947)
  ·
    refine ⟨38712137452511764096072421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25808091635007842730714947 38712137452511764096072421)
    ·
      refine ⟨7258525772345955768013579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38712137452511764096072421 7258525772345955768013579)
      ·
        refine ⟨10887788658518933652020369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7258525772345955768013579 10887788658518933652020369)
        ·
          refine ⟨8165841493889200239015277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10887788658518933652020369 8165841493889200239015277)
          ·
            refine ⟨3062190560208450089630729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8165841493889200239015277 3062190560208450089630729)
            ·
              refine ⟨2296642920156337567223047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3062190560208450089630729 2296642920156337567223047)
              ·
                refine ⟨3444964380234506350834571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2296642920156337567223047 3444964380234506350834571)
                ·
                  refine ⟨5167446570351759526251857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3444964380234506350834571 5167446570351759526251857)
                  ·
                    refine ⟨3875584927763819644688893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5167446570351759526251857 3875584927763819644688893)
                    ·
                      refine ⟨1453344347911432366758335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3875584927763819644688893 1453344347911432366758335)
                      ·
                        rfl

theorem cell23_2830378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_2830378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830378 prefixEnd_2830378 := by exact prefixLift 2830378
  have htrace : WordTrace (prefixWord ++ tailWord_2830378) baseStart_2830378 baseEnd_2830378 := by
    simpa [prefixWord, tailWord_2830378, baseEnd_2830378] using wordTrace_append hprefix tailTrace_2830378
  have hstable : (prefixWord ++ tailWord_2830378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830378).length < 2 ^ (prefixWord ++ tailWord_2830378).sum := by decide
  have hdescent : baseEnd_2830378 < baseStart_2830378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830380 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 4]
def baseStart_2830380 : Nat := 118140960795 + 2830380 * 2 ^ 59
def prefixEnd_2830380 : Nat := 4983230072969 + 3 ^ 40 * 2830380 * 2
def baseEnd_2830380 : Nat := 1453345374872741358933325

theorem tailTrace_2830380 : CollatzResearch.WordTrace tailWord_2830380 prefixEnd_2830380 1453345374872741358933325 := by
  unfold tailWord_2830380
  simp only [CollatzResearch.WordTrace]
  refine ⟨51616219743012062632216297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68821626324016083509621729 51616219743012062632216297)
  ·
    refine ⟨38712164807259046974162223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51616219743012062632216297 38712164807259046974162223)
    ·
      refine ⟨58068247210888570461243335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38712164807259046974162223 58068247210888570461243335)
      ·
        refine ⟨87102370816332855691865003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58068247210888570461243335 87102370816332855691865003)
        ·
          refine ⟨130653556224499283537797505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87102370816332855691865003 130653556224499283537797505)
          ·
            refine ⟨97990167168374462653348129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130653556224499283537797505 97990167168374462653348129)
            ·
              refine ⟨73492625376280846990011097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97990167168374462653348129 73492625376280846990011097)
              ·
                refine ⟨55119469032210635242508323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73492625376280846990011097 55119469032210635242508323)
                ·
                  refine ⟨82679203548315952863762485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55119469032210635242508323 82679203548315952863762485)
                  ·
                    refine ⟨7751175332654620580977733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82679203548315952863762485 7751175332654620580977733)
                    ·
                      refine ⟨1453345374872741358933325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7751175332654620580977733 1453345374872741358933325)
                      ·
                        rfl

theorem cell23_2830380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_2830380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830380 prefixEnd_2830380 := by exact prefixLift 2830380
  have htrace : WordTrace (prefixWord ++ tailWord_2830380) baseStart_2830380 baseEnd_2830380 := by
    simpa [prefixWord, tailWord_2830380, baseEnd_2830380] using wordTrace_append hprefix tailTrace_2830380
  have hstable : (prefixWord ++ tailWord_2830380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830380).length < 2 ^ (prefixWord ++ tailWord_2830380).sum := by decide
  have hdescent : baseEnd_2830380 < baseStart_2830380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830418 : List Nat := [3, 2, 2, 1, 4, 1, 2, 2, 1, 3, 2]
def baseStart_2830418 : Nat := 118140960795 + 2830418 * 2 ^ 59
def prefixEnd_2830418 : Nat := 4983230072969 + 3 ^ 40 * 2830418 * 2
def baseEnd_2830418 : Nat := 1453364887137612210258151

theorem tailTrace_2830418 : CollatzResearch.WordTrace tailWord_2830418 prefixEnd_2830418 1453364887137612210258151 := by
  unfold tailWord_2830418
  simp only [CollatzResearch.WordTrace]
  refine ⟨25808456364971614438578977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68822550306590971836210605 25808456364971614438578977)
  ·
    refine ⟨19356342273728710828934233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25808456364971614438578977 19356342273728710828934233)
    ·
      refine ⟨14517256705296533121700675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19356342273728710828934233 14517256705296533121700675)
      ·
        refine ⟨21775885057944799682551013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14517256705296533121700675 21775885057944799682551013)
        ·
          refine ⟨4082978448364649940478315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21775885057944799682551013 4082978448364649940478315)
          ·
            refine ⟨6124467672546974910717473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4082978448364649940478315 6124467672546974910717473)
            ·
              refine ⟨4593350754410231183038105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6124467672546974910717473 4593350754410231183038105)
              ·
                refine ⟨3445013065807673387278579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4593350754410231183038105 3445013065807673387278579)
                ·
                  refine ⟨5167519598711510080917869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3445013065807673387278579 5167519598711510080917869)
                  ·
                    refine ⟨1937819849516816280344201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5167519598711510080917869 1937819849516816280344201)
                    ·
                      refine ⟨1453364887137612210258151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1937819849516816280344201 1453364887137612210258151)
                      ·
                        rfl

theorem cell23_2830418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_2830418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830418 prefixEnd_2830418 := by exact prefixLift 2830418
  have htrace : WordTrace (prefixWord ++ tailWord_2830418) baseStart_2830418 baseEnd_2830418 := by
    simpa [prefixWord, tailWord_2830418, baseEnd_2830418] using wordTrace_append hprefix tailTrace_2830418
  have hstable : (prefixWord ++ tailWord_2830418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830418).length < 2 ^ (prefixWord ++ tailWord_2830418).sum := by decide
  have hdescent : baseEnd_2830418 < baseStart_2830418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830454 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 7]
def baseStart_2830454 : Nat := 118140960795 + 2830454 * 2 ^ 59
def prefixEnd_2830454 : Nat := 4983230072969 + 3 ^ 40 * 2830454 * 2
def baseEnd_2830454 : Nat := 161487041382352674378665

theorem tailTrace_2830454 : CollatzResearch.WordTrace tailWord_2830454 prefixEnd_2830454 161487041382352674378665 := by
  unfold tailWord_2830454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6452196155484752243914151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68823425658504023935084277 6452196155484752243914151)
  ·
    refine ⟨9678294233227128365871227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6452196155484752243914151 9678294233227128365871227)
    ·
      refine ⟨14517441349840692548806841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9678294233227128365871227 14517441349840692548806841)
      ·
        refine ⟨10888081012380519411605131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14517441349840692548806841 10888081012380519411605131)
        ·
          refine ⟨16332121518570779117407697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10888081012380519411605131 16332121518570779117407697)
          ·
            refine ⟨12249091138928084338055773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16332121518570779117407697 12249091138928084338055773)
            ·
              refine ⟨4593409177098031626770915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12249091138928084338055773 4593409177098031626770915)
              ·
                refine ⟨6890113765647047440156373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4593409177098031626770915 6890113765647047440156373)
                ·
                  refine ⟨161487041382352674378665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6890113765647047440156373 161487041382352674378665)
                  ·
                    rfl

theorem cell23_2830454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_2830454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830454 prefixEnd_2830454 := by exact prefixLift 2830454
  have htrace : WordTrace (prefixWord ++ tailWord_2830454) baseStart_2830454 baseEnd_2830454 := by
    simpa [prefixWord, tailWord_2830454, baseEnd_2830454] using wordTrace_append hprefix tailTrace_2830454
  have hstable : (prefixWord ++ tailWord_2830454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830454).length < 2 ^ (prefixWord ++ tailWord_2830454).sum := by decide
  have hdescent : baseEnd_2830454 < baseStart_2830454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830486 : List Nat := [5, 3, 2, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_2830486 : Nat := 118140960795 + 2830486 * 2 ^ 59
def prefixEnd_2830486 : Nat := 4983230072969 + 3 ^ 40 * 2830486 * 2
def baseEnd_2830486 : Nat := 1453399803822117944207839

theorem tailTrace_2830486 : CollatzResearch.WordTrace tailWord_2830486 prefixEnd_2830486 1453399803822117944207839 := by
  unfold tailWord_2830486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6452269101477506585486957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68824203749093403578527541 6452269101477506585486957)
  ·
    refine ⟨2419600913054064969557609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6452269101477506585486957 2419600913054064969557609)
    ·
      refine ⟨1814700684790548727168207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2419600913054064969557609 1814700684790548727168207)
      ·
        refine ⟨2722051027185823090752311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814700684790548727168207 2722051027185823090752311)
        ·
          refine ⟨4083076540778734636128467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2722051027185823090752311 4083076540778734636128467)
          ·
            refine ⟨6124614811168101954192701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4083076540778734636128467 6124614811168101954192701)
            ·
              refine ⟨2296730554188038232822263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6124614811168101954192701 2296730554188038232822263)
              ·
                refine ⟨3445095831282057349233395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2296730554188038232822263 3445095831282057349233395)
                ·
                  refine ⟨5167643746923086023850093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3445095831282057349233395 5167643746923086023850093)
                  ·
                    refine ⟨1937866405096157258943785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5167643746923086023850093 1937866405096157258943785)
                    ·
                      refine ⟨1453399803822117944207839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1937866405096157258943785 1453399803822117944207839)
                      ·
                        rfl

theorem cell23_2830486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_2830486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830486 prefixEnd_2830486 := by exact prefixLift 2830486
  have htrace : WordTrace (prefixWord ++ tailWord_2830486) baseStart_2830486 baseEnd_2830486 := by
    simpa [prefixWord, tailWord_2830486, baseEnd_2830486] using wordTrace_append hprefix tailTrace_2830486
  have hstable : (prefixWord ++ tailWord_2830486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830486).length < 2 ^ (prefixWord ++ tailWord_2830486).sum := by decide
  have hdescent : baseEnd_2830486 < baseStart_2830486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830514 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 3, 4]
def baseStart_2830514 : Nat := 118140960795 + 2830514 * 2 ^ 59
def prefixEnd_2830514 : Nat := 4983230072969 + 3 ^ 40 * 2830514 * 2
def baseEnd_2830514 : Nat := 484471393760147944885903

theorem tailTrace_2830514 : CollatzResearch.WordTrace tailWord_2830514 prefixEnd_2830514 484471393760147944885903 := by
  unfold tailWord_2830514
  simp only [CollatzResearch.WordTrace]
  refine ⟨25809331716884666537452649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68824884578359110766540397 25809331716884666537452649)
  ·
    refine ⟨19356998787663499903089487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25809331716884666537452649 19356998787663499903089487)
    ·
      refine ⟨29035498181495249854634231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19356998787663499903089487 29035498181495249854634231)
      ·
        refine ⟨43553247272242874781951347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29035498181495249854634231 43553247272242874781951347)
        ·
          refine ⟨65329870908364312172927021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43553247272242874781951347 65329870908364312172927021)
          ·
            refine ⟨24498701590636617064847633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65329870908364312172927021 24498701590636617064847633)
            ·
              refine ⟨18374026192977462798635725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24498701590636617064847633 18374026192977462798635725)
              ·
                refine ⟨6890259822366548549488397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18374026192977462798635725 6890259822366548549488397)
                ·
                  refine ⟨2583847433387455706058149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6890259822366548549488397 2583847433387455706058149)
                  ·
                    refine ⟨484471393760147944885903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2583847433387455706058149 484471393760147944885903)
                    ·
                      rfl

theorem cell23_2830514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_2830514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830514 prefixEnd_2830514 := by exact prefixLift 2830514
  have htrace : WordTrace (prefixWord ++ tailWord_2830514) baseStart_2830514 baseEnd_2830514 := by
    simpa [prefixWord, tailWord_2830514, baseEnd_2830514] using wordTrace_append hprefix tailTrace_2830514
  have hstable : (prefixWord ++ tailWord_2830514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830514).length < 2 ^ (prefixWord ++ tailWord_2830514).sum := by decide
  have hdescent : baseEnd_2830514 < baseStart_2830514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830537 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 1, 7, 3]
def baseStart_2830537 : Nat := 118140960795 + 2830537 * 2 ^ 59
def prefixEnd_2830537 : Nat := 4983230072969 + 3 ^ 40 * 2830537 * 2
def baseEnd_2830537 : Nat := 1453425991335497244670103

theorem tailTrace_2830537 : CollatzResearch.WordTrace tailWord_2830537 prefixEnd_2830537 1453425991335497244670103 := by
  unfold tailWord_2830537
  simp only [CollatzResearch.WordTrace]
  refine ⟨103238165746455341077897865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68825443830970227385265243 103238165746455341077897865)
  ·
    refine ⟨77428624309841505808423399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103238165746455341077897865 77428624309841505808423399)
    ·
      refine ⟨116142936464762258712635099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77428624309841505808423399 116142936464762258712635099)
      ·
        refine ⟨174214404697143388068952649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116142936464762258712635099 174214404697143388068952649)
        ·
          refine ⟨130660803522857541051714487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174214404697143388068952649 130660803522857541051714487)
          ·
            refine ⟨195991205284286311577571731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130660803522857541051714487 195991205284286311577571731)
            ·
              refine ⟨293986807926429467366357597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195991205284286311577571731 293986807926429467366357597)
              ·
                refine ⟨110245052972411050262384099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293986807926429467366357597 110245052972411050262384099)
                ·
                  refine ⟨165367579458616575393576149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110245052972411050262384099 165367579458616575393576149)
                  ·
                    refine ⟨3875802643561325985786941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 165367579458616575393576149 3875802643561325985786941)
                    ·
                      refine ⟨1453425991335497244670103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3875802643561325985786941 1453425991335497244670103)
                      ·
                        rfl

theorem cell23_2830537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 7, 3].length) (baseStart_2830537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830537 prefixEnd_2830537 := by exact prefixLift 2830537
  have htrace : WordTrace (prefixWord ++ tailWord_2830537) baseStart_2830537 baseEnd_2830537 := by
    simpa [prefixWord, tailWord_2830537, baseEnd_2830537] using wordTrace_append hprefix tailTrace_2830537
  have hstable : (prefixWord ++ tailWord_2830537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830537).length < 2 ^ (prefixWord ++ tailWord_2830537).sum := by decide
  have hdescent : baseEnd_2830537 < baseStart_2830537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830571 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 3, 1, 3]
def baseStart_2830571 : Nat := 118140960795 + 2830571 * 2 ^ 59
def prefixEnd_2830571 : Nat := 4983230072969 + 3 ^ 40 * 2830571 * 2
def baseEnd_2830571 : Nat := 1453443449677750111644947

theorem tailTrace_2830571 : CollatzResearch.WordTrace tailWord_2830571 prefixEnd_2830571 1453443449677750111644947 := by
  unfold tailWord_2830571
  simp only [CollatzResearch.WordTrace]
  refine ⟨103239405828332164884635567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68826270552221443256423711 103239405828332164884635567)
  ·
    refine ⟨154859108742498247326953351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103239405828332164884635567 154859108742498247326953351)
    ·
      refine ⟨232288663113747370990430027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154859108742498247326953351 232288663113747370990430027)
      ·
        refine ⟨348432994670621056485645041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232288663113747370990430027 348432994670621056485645041)
        ·
          refine ⟨261324746002965792364233781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348432994670621056485645041 261324746002965792364233781)
          ·
            refine ⟨24499194937778043034146917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 261324746002965792364233781 24499194937778043034146917)
            ·
              refine ⟨4593599050833383068902547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24499194937778043034146917 4593599050833383068902547)
              ·
                refine ⟨6890398576250074603353821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4593599050833383068902547 6890398576250074603353821)
                ·
                  refine ⟨2583899466093777976257683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6890398576250074603353821 2583899466093777976257683)
                  ·
                    refine ⟨3875849199140666964386525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2583899466093777976257683 3875849199140666964386525)
                    ·
                      refine ⟨1453443449677750111644947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3875849199140666964386525 1453443449677750111644947)
                      ·
                        rfl

theorem cell23_2830571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 1, 3].length) (baseStart_2830571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830571 prefixEnd_2830571 := by exact prefixLift 2830571
  have htrace : WordTrace (prefixWord ++ tailWord_2830571) baseStart_2830571 baseEnd_2830571 := by
    simpa [prefixWord, tailWord_2830571, baseEnd_2830571] using wordTrace_append hprefix tailTrace_2830571
  have hstable : (prefixWord ++ tailWord_2830571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830571).length < 2 ^ (prefixWord ++ tailWord_2830571).sum := by decide
  have hdescent : baseEnd_2830571 < baseStart_2830571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830604 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 6, 4]
def baseStart_2830604 : Nat := 118140960795 + 2830604 * 2 ^ 59
def prefixEnd_2830604 : Nat := 4983230072969 + 3 ^ 40 * 2830604 * 2
def baseEnd_2830604 : Nat := 484486798179782827510765

theorem tailTrace_2830604 : CollatzResearch.WordTrace tailWord_2830604 prefixEnd_2830604 484486798179782827510765 := by
  unfold tailWord_2830604
  simp only [CollatzResearch.WordTrace]
  refine ⟨51620304718606305760293433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68827072958141741013724577 51620304718606305760293433)
  ·
    refine ⟨38715228538954729320220075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51620304718606305760293433 38715228538954729320220075)
    ·
      refine ⟨58072842808432093980330113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38715228538954729320220075 58072842808432093980330113)
      ·
        refine ⟨43554632106324070485247585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58072842808432093980330113 43554632106324070485247585)
        ·
          refine ⟨32665974079743052863935689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43554632106324070485247585 32665974079743052863935689)
          ·
            refine ⟨24499480559807289647951767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32665974079743052863935689 24499480559807289647951767)
            ·
              refine ⟨36749220839710934471927651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24499480559807289647951767 36749220839710934471927651)
              ·
                refine ⟨55123831259566401707891477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36749220839710934471927651 55123831259566401707891477)
                ·
                  refine ⟨2583929590292175080057413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55123831259566401707891477 2583929590292175080057413)
                  ·
                    refine ⟨484486798179782827510765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2583929590292175080057413 484486798179782827510765)
                    ·
                      rfl

theorem cell23_2830604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_2830604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830604 prefixEnd_2830604 := by exact prefixLift 2830604
  have htrace : WordTrace (prefixWord ++ tailWord_2830604) baseStart_2830604 baseEnd_2830604 := by
    simpa [prefixWord, tailWord_2830604, baseEnd_2830604] using wordTrace_append hprefix tailTrace_2830604
  have hstable : (prefixWord ++ tailWord_2830604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830604).length < 2 ^ (prefixWord ++ tailWord_2830604).sum := by decide
  have hdescent : baseEnd_2830604 < baseStart_2830604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830611 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 5, 2, 2]
def baseStart_2830611 : Nat := 118140960795 + 2830611 * 2 ^ 59
def prefixEnd_2830611 : Nat := 4983230072969 + 3 ^ 40 * 2830611 * 2
def baseEnd_2830611 : Nat := 1453463988903929955144763

theorem tailTrace_2830611 : CollatzResearch.WordTrace tailWord_2830611 prefixEnd_2830611 1453463988903929955144763 := by
  unfold tailWord_2830611
  simp only [CollatzResearch.WordTrace]
  refine ⟨103240864748187251716091687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68827243165458167810727791 103240864748187251716091687)
  ·
    refine ⟨154861297122280877574137531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103240864748187251716091687 154861297122280877574137531)
    ·
      refine ⟨232291945683421316361206297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154861297122280877574137531 232291945683421316361206297)
      ·
        refine ⟨174218959262565987270904723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232291945683421316361206297 174218959262565987270904723)
        ·
          refine ⟨261328438893848980906357085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174218959262565987270904723 261328438893848980906357085)
          ·
            refine ⟨97998164585193367839883907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261328438893848980906357085 97998164585193367839883907)
            ·
              refine ⟨146997246877790051759825861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97998164585193367839883907 146997246877790051759825861)
              ·
                refine ⟨27561983789585634704967349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146997246877790051759825861 27561983789585634704967349)
                ·
                  refine ⟨2583935980273653253590689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27561983789585634704967349 2583935980273653253590689)
                  ·
                    refine ⟨1937951985205239940193017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2583935980273653253590689 1937951985205239940193017)
                    ·
                      refine ⟨1453463988903929955144763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1937951985205239940193017 1453463988903929955144763)
                      ·
                        rfl

theorem cell23_2830611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 2, 2].length) (baseStart_2830611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830611 prefixEnd_2830611 := by exact prefixLift 2830611
  have htrace : WordTrace (prefixWord ++ tailWord_2830611) baseStart_2830611 baseEnd_2830611 := by
    simpa [prefixWord, tailWord_2830611, baseEnd_2830611] using wordTrace_append hprefix tailTrace_2830611
  have hstable : (prefixWord ++ tailWord_2830611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830611).length < 2 ^ (prefixWord ++ tailWord_2830611).sum := by decide
  have hdescent : baseEnd_2830611 < baseStart_2830611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830622 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_2830622 : Nat := 118140960795 + 2830622 * 2 ^ 59
def prefixEnd_2830622 : Nat := 4983230072969 + 3 ^ 40 * 2830622 * 2
def baseEnd_2830622 : Nat := 1453469637191129412107213

theorem tailTrace_2830622 : CollatzResearch.WordTrace tailWord_2830622 prefixEnd_2830622 1453469637191129412107213 := by
  unfold tailWord_2830622
  simp only [CollatzResearch.WordTrace]
  refine ⟨12905158243893425074342765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68827510634098267063161413 12905158243893425074342765)
  ·
    refine ⟨4839434341460034402878537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12905158243893425074342765 4839434341460034402878537)
    ·
      refine ⟨3629575756095025802158903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4839434341460034402878537 3629575756095025802158903)
      ·
        refine ⟨5444363634142538703238355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3629575756095025802158903 5444363634142538703238355)
        ·
          refine ⟨8166545451213808054857533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5444363634142538703238355 8166545451213808054857533)
          ·
            refine ⟨3062454544205178020571575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8166545451213808054857533 3062454544205178020571575)
            ·
              refine ⟨4593681816307767030857363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062454544205178020571575 4593681816307767030857363)
              ·
                refine ⟨6890522724461650546286045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4593681816307767030857363 6890522724461650546286045)
                ·
                  refine ⟨2583946021673118954857267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6890522724461650546286045 2583946021673118954857267)
                  ·
                    refine ⟨3875919032509678432285901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2583946021673118954857267 3875919032509678432285901)
                    ·
                      refine ⟨1453469637191129412107213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3875919032509678432285901 1453469637191129412107213)
                      ·
                        rfl

theorem cell23_2830622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_2830622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830622 prefixEnd_2830622 := by exact prefixLift 2830622
  have htrace : WordTrace (prefixWord ++ tailWord_2830622) baseStart_2830622 baseEnd_2830622 := by
    simpa [prefixWord, tailWord_2830622, baseEnd_2830622] using wordTrace_append hprefix tailTrace_2830622
  have hstable : (prefixWord ++ tailWord_2830622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830622).length < 2 ^ (prefixWord ++ tailWord_2830622).sum := by decide
  have hdescent : baseEnd_2830622 < baseStart_2830622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830624 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2830624 : Nat := 118140960795 + 2830624 * 2 ^ 59
def prefixEnd_2830624 : Nat := 4983230072969 + 3 ^ 40 * 2830624 * 2
def baseEnd_2830624 : Nat := 1453470664152438404282203

theorem tailTrace_2830624 : CollatzResearch.WordTrace tailWord_2830624 prefixEnd_2830624 1453470664152438404282203 := by
  unfold tailWord_2830624
  simp only [CollatzResearch.WordTrace]
  refine ⟨51620669448570077468157463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68827559264760103290876617 51620669448570077468157463)
  ·
    refine ⟨77431004172855116202236195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51620669448570077468157463 77431004172855116202236195)
    ·
      refine ⟨116146506259282674303354293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77431004172855116202236195 116146506259282674303354293)
      ·
        refine ⟨10888734961807750715939465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116146506259282674303354293 10888734961807750715939465)
        ·
          refine ⟨8166551221355813036954599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10888734961807750715939465 8166551221355813036954599)
          ·
            refine ⟨12249826832033719555431899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8166551221355813036954599 12249826832033719555431899)
            ·
              refine ⟨18374740248050579333147849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12249826832033719555431899 18374740248050579333147849)
              ·
                refine ⟨13781055186037934499860887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18374740248050579333147849 13781055186037934499860887)
                ·
                  refine ⟨20671582779056901749791331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13781055186037934499860887 20671582779056901749791331)
                  ·
                    refine ⟨31007374168585352624686997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20671582779056901749791331 31007374168585352624686997)
                    ·
                      refine ⟨1453470664152438404282203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31007374168585352624686997 1453470664152438404282203)
                      ·
                        rfl

theorem cell23_2830624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2830624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830624 prefixEnd_2830624 := by exact prefixLift 2830624
  have htrace : WordTrace (prefixWord ++ tailWord_2830624) baseStart_2830624 baseEnd_2830624 := by
    simpa [prefixWord, tailWord_2830624, baseEnd_2830624] using wordTrace_append hprefix tailTrace_2830624
  have hstable : (prefixWord ++ tailWord_2830624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830624).length < 2 ^ (prefixWord ++ tailWord_2830624).sum := by decide
  have hdescent : baseEnd_2830624 < baseStart_2830624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830674 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_2830674 : Nat := 118140960795 + 2830674 * 2 ^ 59
def prefixEnd_2830674 : Nat := 4983230072969 + 3 ^ 40 * 2830674 * 2
def baseEnd_2830674 : Nat := 1453496338185163208656973

theorem tailTrace_2830674 : CollatzResearch.WordTrace tailWord_2830674 prefixEnd_2830674 1453496338185163208656973 := by
  unfold tailWord_2830674
  simp only [CollatzResearch.WordTrace]
  refine ⟨25810790636739753368908769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68828775031306008983756717 25810790636739753368908769)
  ·
    refine ⟨19358092977554815026681577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25810790636739753368908769 19358092977554815026681577)
    ·
      refine ⟨14518569733166111270011183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19358092977554815026681577 14518569733166111270011183)
      ·
        refine ⟨21777854599749166905016775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14518569733166111270011183 21777854599749166905016775)
        ·
          refine ⟨32666781899623750357525163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21777854599749166905016775 32666781899623750357525163)
          ·
            refine ⟨49000172849435625536287745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32666781899623750357525163 49000172849435625536287745)
            ·
              refine ⟨36750129637076719152215809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49000172849435625536287745 36750129637076719152215809)
              ·
                refine ⟨27562597227807539364161857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36750129637076719152215809 27562597227807539364161857)
                ·
                  refine ⟨20671947920855654523121393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27562597227807539364161857 20671947920855654523121393)
                  ·
                    refine ⟨15503960940641740892341045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20671947920855654523121393 15503960940641740892341045)
                    ·
                      refine ⟨1453496338185163208656973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15503960940641740892341045 1453496338185163208656973)
                      ·
                        rfl

theorem cell23_2830674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_2830674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830674 prefixEnd_2830674 := by exact prefixLift 2830674
  have htrace : WordTrace (prefixWord ++ tailWord_2830674) baseStart_2830674 baseEnd_2830674 := by
    simpa [prefixWord, tailWord_2830674, baseEnd_2830674] using wordTrace_append hprefix tailTrace_2830674
  have hstable : (prefixWord ++ tailWord_2830674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830674).length < 2 ^ (prefixWord ++ tailWord_2830674).sum := by decide
  have hdescent : baseEnd_2830674 < baseStart_2830674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830714 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4]
def baseStart_2830714 : Nat := 118140960795 + 2830714 * 2 ^ 59
def prefixEnd_2830714 : Nat := 4983230072969 + 3 ^ 40 * 2830714 * 2
def baseEnd_2830714 : Nat := 1453516877411343052156789

theorem tailTrace_2830714 : CollatzResearch.WordTrace tailWord_2830714 prefixEnd_2830714 1453516877411343052156789 := by
  unfold tailWord_2830714
  simp only [CollatzResearch.WordTrace]
  refine ⟨25811155366703525076772799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68829747644542733538060797 25811155366703525076772799)
  ·
    refine ⟨38716733050055287615159199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25811155366703525076772799 38716733050055287615159199)
    ·
      refine ⟨58075099575082931422738799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38716733050055287615159199 58075099575082931422738799)
      ·
        refine ⟨87112649362624397134108199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58075099575082931422738799 87112649362624397134108199)
        ·
          refine ⟨130668974043936595701162299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87112649362624397134108199 130668974043936595701162299)
          ·
            refine ⟨196003461065904893551743449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130668974043936595701162299 196003461065904893551743449)
            ·
              refine ⟨147002595799428670163807587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196003461065904893551743449 147002595799428670163807587)
              ·
                refine ⟨220503893699143005245711381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147002595799428670163807587 220503893699143005245711381)
                ·
                  refine ⟨10336120017147328370892721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 220503893699143005245711381 10336120017147328370892721)
                  ·
                    refine ⟨7752090012860496278169541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10336120017147328370892721 7752090012860496278169541)
                    ·
                      refine ⟨1453516877411343052156789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7752090012860496278169541 1453516877411343052156789)
                      ·
                        rfl

theorem cell23_2830714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_2830714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830714 prefixEnd_2830714 := by exact prefixLift 2830714
  have htrace : WordTrace (prefixWord ++ tailWord_2830714) baseStart_2830714 baseEnd_2830714 := by
    simpa [prefixWord, tailWord_2830714, baseEnd_2830714] using wordTrace_append hprefix tailTrace_2830714
  have hstable : (prefixWord ++ tailWord_2830714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830714).length < 2 ^ (prefixWord ++ tailWord_2830714).sum := by decide
  have hdescent : baseEnd_2830714 < baseStart_2830714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830724 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 9]
def baseStart_2830724 : Nat := 118140960795 + 2830724 * 2 ^ 59
def prefixEnd_2830724 : Nat := 4983230072969 + 3 ^ 40 * 2830724 * 2
def baseEnd_2830724 : Nat := 161502445801987557003527

theorem tailTrace_2830724 : CollatzResearch.WordTrace tailWord_2830724 prefixEnd_2830724 161502445801987557003527 := by
  unfold tailWord_2830724
  simp only [CollatzResearch.WordTrace]
  refine ⟨51622493098388936007477613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68829990797851914676636817 51622493098388936007477613)
  ·
    refine ⟨19358434911895851002804105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51622493098388936007477613 19358434911895851002804105)
    ·
      refine ⟨14518826183921888252103079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19358434911895851002804105 14518826183921888252103079)
      ·
        refine ⟨21778239275882832378154619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14518826183921888252103079 21778239275882832378154619)
        ·
          refine ⟨32667358913824248567231929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21778239275882832378154619 32667358913824248567231929)
          ·
            refine ⟨24500519185368186425423947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32667358913824248567231929 24500519185368186425423947)
            ·
              refine ⟨36750778778052279638135921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24500519185368186425423947 36750778778052279638135921)
              ·
                refine ⟨27563084083539209728601941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36750778778052279638135921 27563084083539209728601941)
                ·
                  refine ⟨161502445801987557003527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27563084083539209728601941 161502445801987557003527)
                  ·
                    rfl

theorem cell23_2830724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_2830724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830724 prefixEnd_2830724 := by exact prefixLift 2830724
  have htrace : WordTrace (prefixWord ++ tailWord_2830724) baseStart_2830724 baseEnd_2830724 := by
    simpa [prefixWord, tailWord_2830724, baseEnd_2830724] using wordTrace_append hprefix tailTrace_2830724
  have hstable : (prefixWord ++ tailWord_2830724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830724).length < 2 ^ (prefixWord ++ tailWord_2830724).sum := by decide
  have hdescent : baseEnd_2830724 < baseStart_2830724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830751 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 3]
def baseStart_2830751 : Nat := 118140960795 + 2830751 * 2 ^ 59
def prefixEnd_2830751 : Nat := 4983230072969 + 3 ^ 40 * 2830751 * 2
def baseEnd_2830751 : Nat := 1453535876195559407394119

theorem tailTrace_2830751 : CollatzResearch.WordTrace tailWord_2830751 prefixEnd_2830751 1453535876195559407394119 := by
  unfold tailWord_2830751
  simp only [CollatzResearch.WordTrace]
  refine ⟨103245970967680055626188107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68830647311786703750792071 103245970967680055626188107)
  ·
    refine ⟨154868956451520083439282161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103245970967680055626188107 154868956451520083439282161)
    ·
      refine ⟨116151717338640062579461621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154868956451520083439282161 116151717338640062579461621)
      ·
        refine ⟨10889223500497505866824527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116151717338640062579461621 10889223500497505866824527)
        ·
          refine ⟨16333835250746258800236791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10889223500497505866824527 16333835250746258800236791)
          ·
            refine ⟨24500752876119388200355187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16333835250746258800236791 24500752876119388200355187)
            ·
              refine ⟨36751129314179082300532781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24500752876119388200355187 36751129314179082300532781)
              ·
                refine ⟨13781673492817155862699793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36751129314179082300532781 13781673492817155862699793)
                ·
                  refine ⟨10336255119612866897024845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13781673492817155862699793 10336255119612866897024845)
                  ·
                    refine ⟨3876095669854825086384317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10336255119612866897024845 3876095669854825086384317)
                    ·
                      refine ⟨1453535876195559407394119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3876095669854825086384317 1453535876195559407394119)
                      ·
                        rfl

theorem cell23_2830751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_2830751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830751 prefixEnd_2830751 := by exact prefixLift 2830751
  have htrace : WordTrace (prefixWord ++ tailWord_2830751) baseStart_2830751 baseEnd_2830751 := by
    simpa [prefixWord, tailWord_2830751, baseEnd_2830751] using wordTrace_append hprefix tailTrace_2830751
  have hstable : (prefixWord ++ tailWord_2830751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830751).length < 2 ^ (prefixWord ++ tailWord_2830751).sum := by decide
  have hdescent : baseEnd_2830751 < baseStart_2830751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830752 : List Nat := [2, 1, 1, 4, 1, 4, 3, 1, 2, 2, 2]
def baseStart_2830752 : Nat := 118140960795 + 2830752 * 2 ^ 59
def prefixEnd_2830752 : Nat := 4983230072969 + 3 ^ 40 * 2830752 * 2
def baseEnd_2830752 : Nat := 1453536389676213903481615

theorem tailTrace_2830752 : CollatzResearch.WordTrace tailWord_2830752 prefixEnd_2830752 1453536389676213903481615 := by
  unfold tailWord_2830752
  simp only [CollatzResearch.WordTrace]
  refine ⟨51623003720338216398487255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68830671627117621864649673 51623003720338216398487255)
  ·
    refine ⟨77434505580507324597730883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51623003720338216398487255 77434505580507324597730883)
    ·
      refine ⟨116151758370760986896596325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77434505580507324597730883 116151758370760986896596325)
      ·
        refine ⟨21778454694517685043111811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116151758370760986896596325 21778454694517685043111811)
        ·
          refine ⟨32667682041776527564667717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21778454694517685043111811 32667682041776527564667717)
          ·
            refine ⟨6125190382833098918375197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32667682041776527564667717 6125190382833098918375197)
            ·
              refine ⟨2296946393562412094390699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6125190382833098918375197 2296946393562412094390699)
              ·
                refine ⟨3445419590343618141586049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2296946393562412094390699 3445419590343618141586049)
                ·
                  refine ⟨2584064692757713606189537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3445419590343618141586049 2584064692757713606189537)
                  ·
                    refine ⟨1938048519568285204642153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2584064692757713606189537 1938048519568285204642153)
                    ·
                      refine ⟨1453536389676213903481615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1938048519568285204642153 1453536389676213903481615)
                      ·
                        rfl

theorem cell23_2830752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_2830752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830752 prefixEnd_2830752 := by exact prefixLift 2830752
  have htrace : WordTrace (prefixWord ++ tailWord_2830752) baseStart_2830752 baseEnd_2830752 := by
    simpa [prefixWord, tailWord_2830752, baseEnd_2830752] using wordTrace_append hprefix tailTrace_2830752
  have hstable : (prefixWord ++ tailWord_2830752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830752).length < 2 ^ (prefixWord ++ tailWord_2830752).sum := by decide
  have hdescent : baseEnd_2830752 < baseStart_2830752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830761 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 2, 5, 2]
def baseStart_2830761 : Nat := 118140960795 + 2830761 * 2 ^ 59
def prefixEnd_2830761 : Nat := 4983230072969 + 3 ^ 40 * 2830761 * 2
def baseEnd_2830761 : Nat := 1453541011002104368269073

theorem tailTrace_2830761 : CollatzResearch.WordTrace tailWord_2830761 prefixEnd_2830761 1453541011002104368269073 := by
  unfold tailWord_2830761
  simp only [CollatzResearch.WordTrace]
  refine ⟨103246335697643827334052137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68830890465095884889368091 103246335697643827334052137)
  ·
    refine ⟨77434751773232870500539103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103246335697643827334052137 77434751773232870500539103)
    ·
      refine ⟨116152127659849305750808655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77434751773232870500539103 116152127659849305750808655)
      ·
        refine ⟨174228191489773958626212983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116152127659849305750808655 174228191489773958626212983)
        ·
          refine ⟨261342287234660937939319475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174228191489773958626212983 261342287234660937939319475)
          ·
            refine ⟨392013430851991406908979213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261342287234660937939319475 392013430851991406908979213)
            ·
              refine ⟨147005036569496777590867205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 392013430851991406908979213 147005036569496777590867205)
              ·
                refine ⟨27563444356780645798287601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147005036569496777590867205 27563444356780645798287601)
                ·
                  refine ⟨20672583267585484348715701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27563444356780645798287601 20672583267585484348715701)
                  ·
                    refine ⟨1938054681336139157692097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20672583267585484348715701 1938054681336139157692097)
                    ·
                      refine ⟨1453541011002104368269073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1938054681336139157692097 1453541011002104368269073)
                      ·
                        rfl

theorem cell23_2830761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 5, 2].length) (baseStart_2830761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830761 prefixEnd_2830761 := by exact prefixLift 2830761
  have htrace : WordTrace (prefixWord ++ tailWord_2830761) baseStart_2830761 baseEnd_2830761 := by
    simpa [prefixWord, tailWord_2830761, baseEnd_2830761] using wordTrace_append hprefix tailTrace_2830761
  have hstable : (prefixWord ++ tailWord_2830761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830761).length < 2 ^ (prefixWord ++ tailWord_2830761).sum := by decide
  have hdescent : baseEnd_2830761 < baseStart_2830761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830764 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 5]
def baseStart_2830764 : Nat := 118140960795 + 2830764 * 2 ^ 59
def prefixEnd_2830764 : Nat := 4983230072969 + 3 ^ 40 * 2830764 * 2
def baseEnd_2830764 : Nat := 1453542551444067856531559

theorem tailTrace_2830764 : CollatzResearch.WordTrace tailWord_2830764 prefixEnd_2830764 1453542551444067856531559 := by
  unfold tailWord_2830764
  simp only [CollatzResearch.WordTrace]
  refine ⟨51623222558316479423205673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68830963411088639230940897 51623222558316479423205673)
  ·
    refine ⟨38717416918737359567404255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51623222558316479423205673 38717416918737359567404255)
    ·
      refine ⟨58076125378106039351106383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38717416918737359567404255 58076125378106039351106383)
      ·
        refine ⟨87114188067159059026659575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58076125378106039351106383 87114188067159059026659575)
        ·
          refine ⟨130671282100738588539989363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87114188067159059026659575 130671282100738588539989363)
          ·
            refine ⟨196006923151107882809984045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130671282100738588539989363 196006923151107882809984045)
            ·
              refine ⟨73502596181665456053744017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196006923151107882809984045 73502596181665456053744017)
              ·
                refine ⟨55126947136249092040308013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73502596181665456053744017 55126947136249092040308013)
                ·
                  refine ⟨20672605176093409515115505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55126947136249092040308013 20672605176093409515115505)
                  ·
                    refine ⟨15504453882070057136336629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20672605176093409515115505 15504453882070057136336629)
                    ·
                      refine ⟨1453542551444067856531559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15504453882070057136336629 1453542551444067856531559)
                      ·
                        rfl

theorem cell23_2830764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_2830764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830764 prefixEnd_2830764 := by exact prefixLift 2830764
  have htrace : WordTrace (prefixWord ++ tailWord_2830764) baseStart_2830764 baseEnd_2830764 := by
    simpa [prefixWord, tailWord_2830764, baseEnd_2830764] using wordTrace_append hprefix tailTrace_2830764
  have hstable : (prefixWord ++ tailWord_2830764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830764).length < 2 ^ (prefixWord ++ tailWord_2830764).sum := by decide
  have hdescent : baseEnd_2830764 < baseStart_2830764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830791 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_2830791 : Nat := 118140960795 + 2830791 * 2 ^ 59
def prefixEnd_2830791 : Nat := 4983230072969 + 3 ^ 40 * 2830791 * 2
def baseEnd_2830791 : Nat := 1453556415421739250893935

theorem tailTrace_2830791 : CollatzResearch.WordTrace tailWord_2830791 prefixEnd_2830791 1453556415421739250893935 := by
  unfold tailWord_2830791
  simp only [CollatzResearch.WordTrace]
  refine ⟨103247429887535142457644227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68831619925023428305096151 103247429887535142457644227)
  ·
    refine ⟨154871144831302713686466341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103247429887535142457644227 154871144831302713686466341)
    ·
      refine ⟨29038339655869258816212439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154871144831302713686466341 29038339655869258816212439)
      ·
        refine ⟨43557509483803888224318659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29038339655869258816212439 43557509483803888224318659)
        ·
          refine ⟨65336264225705832336477989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43557509483803888224318659 65336264225705832336477989)
          ·
            refine ⟨12250549542319843563089623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65336264225705832336477989 12250549542319843563089623)
            ·
              refine ⟨18375824313479765344634435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12250549542319843563089623 18375824313479765344634435)
              ·
                refine ⟨27563736470219648016951653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18375824313479765344634435 27563736470219648016951653)
                ·
                  refine ⟨5168200588166184003178435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27563736470219648016951653 5168200588166184003178435)
                  ·
                    refine ⟨7752300882249276004767653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5168200588166184003178435 7752300882249276004767653)
                    ·
                      refine ⟨1453556415421739250893935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7752300882249276004767653 1453556415421739250893935)
                      ·
                        rfl

theorem cell23_2830791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_2830791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830791 prefixEnd_2830791 := by exact prefixLift 2830791
  have htrace : WordTrace (prefixWord ++ tailWord_2830791) baseStart_2830791 baseEnd_2830791 := by
    simpa [prefixWord, tailWord_2830791, baseEnd_2830791] using wordTrace_append hprefix tailTrace_2830791
  have hstable : (prefixWord ++ tailWord_2830791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830791).length < 2 ^ (prefixWord ++ tailWord_2830791).sum := by decide
  have hdescent : baseEnd_2830791 < baseStart_2830791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830828 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 3]
def baseStart_2830828 : Nat := 118140960795 + 2830828 * 2 ^ 59
def prefixEnd_2830828 : Nat := 4983230072969 + 3 ^ 40 * 2830828 * 2
def baseEnd_2830828 : Nat := 1453575414205955606131265

theorem tailTrace_2830828 : CollatzResearch.WordTrace tailWord_2830828 prefixEnd_2830828 1453575414205955606131265 := by
  unfold tailWord_2830828
  simp only [CollatzResearch.WordTrace]
  refine ⟨51624389694200548888370569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68832519592267398517827425 51624389694200548888370569)
  ·
    refine ⟨38718292270650411666277927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51624389694200548888370569 38718292270650411666277927)
    ·
      refine ⟨58077438405975617499416891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38718292270650411666277927 58077438405975617499416891)
      ·
        refine ⟨87116157608963426249125337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58077438405975617499416891 87116157608963426249125337)
        ·
          refine ⟨65337118206722569686844003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87116157608963426249125337 65337118206722569686844003)
          ·
            refine ⟨98005677310083854530266005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65337118206722569686844003 98005677310083854530266005)
            ·
              refine ⟨4594016123910180681106219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98005677310083854530266005 4594016123910180681106219)
              ·
                refine ⟨6891024185865271021659329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4594016123910180681106219 6891024185865271021659329)
                ·
                  refine ⟨5168268139398953266244497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6891024185865271021659329 5168268139398953266244497)
                  ·
                    refine ⟨3876201104549214949683373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5168268139398953266244497 3876201104549214949683373)
                    ·
                      refine ⟨1453575414205955606131265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3876201104549214949683373 1453575414205955606131265)
                      ·
                        rfl

theorem cell23_2830828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_2830828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830828 prefixEnd_2830828 := by exact prefixLift 2830828
  have htrace : WordTrace (prefixWord ++ tailWord_2830828) baseStart_2830828 baseEnd_2830828 := by
    simpa [prefixWord, tailWord_2830828, baseEnd_2830828] using wordTrace_append hprefix tailTrace_2830828
  have hstable : (prefixWord ++ tailWord_2830828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830828).length < 2 ^ (prefixWord ++ tailWord_2830828).sum := by decide
  have hdescent : baseEnd_2830828 < baseStart_2830828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830852 : List Nat := [2, 3, 2, 3, 1, 2, 1, 4, 1, 4]
def baseStart_2830852 : Nat := 118140960795 + 2830852 * 2 ^ 59
def prefixEnd_2830852 : Nat := 4983230072969 + 3 ^ 40 * 2830852 * 2
def baseEnd_2830852 : Nat := 484529245913887837410385

theorem tailTrace_2830852 : CollatzResearch.WordTrace tailWord_2830852 prefixEnd_2830852 484529245913887837410385 := by
  unfold tailWord_2830852
  simp only [CollatzResearch.WordTrace]
  refine ⟨51624827370157074937807405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68833103160209433250409873 51624827370157074937807405)
  ·
    refine ⟨19359310263808903101677777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51624827370157074937807405 19359310263808903101677777)
    ·
      refine ⟨14519482697856677326258333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19359310263808903101677777 14519482697856677326258333)
      ·
        refine ⟨5444806011696253997346875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14519482697856677326258333 5444806011696253997346875)
        ·
          refine ⟨8167209017544380996020313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5444806011696253997346875 8167209017544380996020313)
          ·
            refine ⟨6125406763158285747015235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8167209017544380996020313 6125406763158285747015235)
            ·
              refine ⟨9188110144737428620522853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6125406763158285747015235 9188110144737428620522853)
              ·
                refine ⟨1722770652138267866348035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9188110144737428620522853 1722770652138267866348035)
                ·
                  refine ⟨2584155978207401799522053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1722770652138267866348035 2584155978207401799522053)
                  ·
                    refine ⟨484529245913887837410385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2584155978207401799522053 484529245913887837410385)
                    ·
                      rfl

theorem cell23_2830852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_2830852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830852 prefixEnd_2830852 := by exact prefixLift 2830852
  have htrace : WordTrace (prefixWord ++ tailWord_2830852) baseStart_2830852 baseEnd_2830852 := by
    simpa [prefixWord, tailWord_2830852, baseEnd_2830852] using wordTrace_append hprefix tailTrace_2830852
  have hstable : (prefixWord ++ tailWord_2830852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830852).length < 2 ^ (prefixWord ++ tailWord_2830852).sum := by decide
  have hdescent : baseEnd_2830852 < baseStart_2830852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830885 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 2, 3, 2]
def baseStart_2830885 : Nat := 118140960795 + 2830885 * 2 ^ 59
def prefixEnd_2830885 : Nat := 4983230072969 + 3 ^ 40 * 2830885 * 2
def baseEnd_2830885 : Nat := 1453604682603261883118503

theorem tailTrace_2830885 : CollatzResearch.WordTrace tailWord_2830885 prefixEnd_2830885 1453604682603261883118503 := by
  unfold tailWord_2830885
  simp only [CollatzResearch.WordTrace]
  refine ⟨103250858349194596511566109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68833905566129731007710739 103250858349194596511566109)
  ·
    refine ⟨38719071880947973691837291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103250858349194596511566109 38719071880947973691837291)
    ·
      refine ⟨58078607821421960537755937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38719071880947973691837291 58078607821421960537755937)
      ·
        refine ⟨43558955866066470403316953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58078607821421960537755937 43558955866066470403316953)
        ·
          refine ⟨32669216899549852802487715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43558955866066470403316953 32669216899549852802487715)
          ·
            refine ⟨49003825349324779203731573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32669216899549852802487715 49003825349324779203731573)
            ·
              refine ⟨4594108626499198050349835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49003825349324779203731573 4594108626499198050349835)
              ·
                refine ⟨6891162939748797075524753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4594108626499198050349835 6891162939748797075524753)
                ·
                  refine ⟨5168372204811597806643565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6891162939748797075524753 5168372204811597806643565)
                  ·
                    refine ⟨1938139576804349177491337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5168372204811597806643565 1938139576804349177491337)
                    ·
                      refine ⟨1453604682603261883118503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1938139576804349177491337 1453604682603261883118503)
                      ·
                        rfl

theorem cell23_2830885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_2830885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830885 prefixEnd_2830885 := by exact prefixLift 2830885
  have htrace : WordTrace (prefixWord ++ tailWord_2830885) baseStart_2830885 baseEnd_2830885 := by
    simpa [prefixWord, tailWord_2830885, baseEnd_2830885] using wordTrace_append hprefix tailTrace_2830885
  have hstable : (prefixWord ++ tailWord_2830885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830885).length < 2 ^ (prefixWord ++ tailWord_2830885).sum := by decide
  have hdescent : baseEnd_2830885 < baseStart_2830885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830911 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 6]
def baseStart_2830911 : Nat := 118140960795 + 2830911 * 2 ^ 59
def prefixEnd_2830911 : Nat := 4983230072969 + 3 ^ 40 * 2830911 * 2
def baseEnd_2830911 : Nat := 1453618033100278781393383

theorem tailTrace_2830911 : CollatzResearch.WordTrace tailWord_2830911 prefixEnd_2830911 1453618033100278781393383 := by
  unfold tailWord_2830911
  simp only [CollatzResearch.WordTrace]
  refine ⟨103251806647100402952012587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68834537764733601968008391 103251806647100402952012587)
  ·
    refine ⟨154877709970650604428018881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103251806647100402952012587 154877709970650604428018881)
    ·
      refine ⟨116158282477987953321014161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154877709970650604428018881 116158282477987953321014161)
      ·
        refine ⟨87118711858490964990760621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116158282477987953321014161 87118711858490964990760621)
        ·
          refine ⟨32669516946934111871535233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87118711858490964990760621 32669516946934111871535233)
          ·
            refine ⟨24502137710200583903651425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32669516946934111871535233 24502137710200583903651425)
            ·
              refine ⟨18376603282650437927738569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24502137710200583903651425 18376603282650437927738569)
              ·
                refine ⟨13782452461987828445803927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18376603282650437927738569 13782452461987828445803927)
                ·
                  refine ⟨20673678692981742668705891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13782452461987828445803927 20673678692981742668705891)
                  ·
                    refine ⟨31010518039472614003058837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20673678692981742668705891 31010518039472614003058837)
                    ·
                      refine ⟨1453618033100278781393383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31010518039472614003058837 1453618033100278781393383)
                      ·
                        rfl

theorem cell23_2830911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_2830911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830911 prefixEnd_2830911 := by exact prefixLift 2830911
  have htrace : WordTrace (prefixWord ++ tailWord_2830911) baseStart_2830911 baseEnd_2830911 := by
    simpa [prefixWord, tailWord_2830911, baseEnd_2830911] using wordTrace_append hprefix tailTrace_2830911
  have hstable : (prefixWord ++ tailWord_2830911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830911).length < 2 ^ (prefixWord ++ tailWord_2830911).sum := by decide
  have hdescent : baseEnd_2830911 < baseStart_2830911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830925 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_2830925 : Nat := 118140960795 + 2830925 * 2 ^ 59
def prefixEnd_2830925 : Nat := 4983230072969 + 3 ^ 40 * 2830925 * 2
def baseEnd_2830925 : Nat := 484541740609813908872773

theorem tailTrace_2830925 : CollatzResearch.WordTrace tailWord_2830925 prefixEnd_2830925 484541740609813908872773 := by
  unfold tailWord_2830925
  simp only [CollatzResearch.WordTrace]
  refine ⟨103252317269049683343022229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68834878179366455562014819 103252317269049683343022229)
  ·
    refine ⟨4839952371986703906704167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 103252317269049683343022229 4839952371986703906704167)
    ·
      refine ⟨7259928557980055860056251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4839952371986703906704167 7259928557980055860056251)
      ·
        refine ⟨10889892836970083790084377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7259928557980055860056251 10889892836970083790084377)
        ·
          refine ⟨8167419627727562842563283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10889892836970083790084377 8167419627727562842563283)
          ·
            refine ⟨12251129441591344263844925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8167419627727562842563283 12251129441591344263844925)
            ·
              refine ⟨4594173540596754098941847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12251129441591344263844925 4594173540596754098941847)
              ·
                refine ⟨6891260310895131148412771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4594173540596754098941847 6891260310895131148412771)
                ·
                  refine ⟨10336890466342696722619157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6891260310895131148412771 10336890466342696722619157)
                  ·
                    refine ⟨484541740609813908872773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10336890466342696722619157 484541740609813908872773)
                    ·
                      rfl

theorem cell23_2830925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_2830925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830925 prefixEnd_2830925 := by exact prefixLift 2830925
  have htrace : WordTrace (prefixWord ++ tailWord_2830925) baseStart_2830925 baseEnd_2830925 := by
    simpa [prefixWord, tailWord_2830925, baseEnd_2830925] using wordTrace_append hprefix tailTrace_2830925
  have hstable : (prefixWord ++ tailWord_2830925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830925).length < 2 ^ (prefixWord ++ tailWord_2830925).sum := by decide
  have hdescent : baseEnd_2830925 < baseStart_2830925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830932 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 3, 2, 2]
def baseStart_2830932 : Nat := 118140960795 + 2830932 * 2 ^ 59
def prefixEnd_2830932 : Nat := 4983230072969 + 3 ^ 40 * 2830932 * 2
def baseEnd_2830932 : Nat := 1453628816194023199230787

theorem tailTrace_2830932 : CollatzResearch.WordTrace tailWord_2830932 prefixEnd_2830932 1453628816194023199230787 := by
  unfold tailWord_2830932
  simp only [CollatzResearch.WordTrace]
  refine ⟨51626286290012161769263525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68835048386682882359018033 51626286290012161769263525)
  ·
    refine ⟨9679928679377280331736911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51626286290012161769263525 9679928679377280331736911)
    ·
      refine ⟨14519893019065920497605367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9679928679377280331736911 14519893019065920497605367)
      ·
        refine ⟨21779839528598880746408051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14519893019065920497605367 21779839528598880746408051)
        ·
          refine ⟨32669759292898321119612077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21779839528598880746408051 32669759292898321119612077)
          ·
            refine ⟨12251159734836870419854529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32669759292898321119612077 12251159734836870419854529)
            ·
              refine ⟨9188369801127652814890897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12251159734836870419854529 9188369801127652814890897)
              ·
                refine ⟨6891277350845739611168173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9188369801127652814890897 6891277350845739611168173)
                ·
                  refine ⟨2584229006567152354188065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6891277350845739611168173 2584229006567152354188065)
                  ·
                    refine ⟨1938171754925364265641049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2584229006567152354188065 1938171754925364265641049)
                    ·
                      refine ⟨1453628816194023199230787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1938171754925364265641049 1453628816194023199230787)
                      ·
                        rfl

theorem cell23_2830932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_2830932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830932 prefixEnd_2830932 := by exact prefixLift 2830932
  have htrace : WordTrace (prefixWord ++ tailWord_2830932) baseStart_2830932 baseEnd_2830932 := by
    simpa [prefixWord, tailWord_2830932, baseEnd_2830932] using wordTrace_append hprefix tailTrace_2830932
  have hstable : (prefixWord ++ tailWord_2830932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830932).length < 2 ^ (prefixWord ++ tailWord_2830932).sum := by decide
  have hdescent : baseEnd_2830932 < baseStart_2830932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830935 : List Nat := [1, 1, 3, 2, 2, 2, 4, 2, 1, 2, 3]
def baseStart_2830935 : Nat := 118140960795 + 2830935 * 2 ^ 59
def prefixEnd_2830935 : Nat := 4983230072969 + 3 ^ 40 * 2830935 * 2
def baseEnd_2830935 : Nat := 1453630356635986687493273

theorem tailTrace_2830935 : CollatzResearch.WordTrace tailWord_2830935 prefixEnd_2830935 1453630356635986687493273 := by
  unfold tailWord_2830935
  simp only [CollatzResearch.WordTrace]
  refine ⟨103252681999013455050886259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68835121332675636700590839 103252681999013455050886259)
  ·
    refine ⟨154879022998520182576329389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103252681999013455050886259 154879022998520182576329389)
    ·
      refine ⟨58079633624445068466123521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154879022998520182576329389 58079633624445068466123521)
      ·
        refine ⟨43559725218333801349592641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58079633624445068466123521 43559725218333801349592641)
        ·
          refine ⟨32669793913750351012194481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43559725218333801349592641 32669793913750351012194481)
          ·
            refine ⟨24502345435312763259145861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32669793913750351012194481 24502345435312763259145861)
            ·
              refine ⟨4594189769121143111089849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24502345435312763259145861 4594189769121143111089849)
              ·
                refine ⟨3445642326840857333317387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4594189769121143111089849 3445642326840857333317387)
                ·
                  refine ⟨5168463490261285999976081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3445642326840857333317387 5168463490261285999976081)
                  ·
                    refine ⟨3876347617695964499982061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5168463490261285999976081 3876347617695964499982061)
                    ·
                      refine ⟨1453630356635986687493273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3876347617695964499982061 1453630356635986687493273)
                      ·
                        rfl

theorem cell23_2830935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_2830935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830935 prefixEnd_2830935 := by exact prefixLift 2830935
  have htrace : WordTrace (prefixWord ++ tailWord_2830935) baseStart_2830935 baseEnd_2830935 := by
    simpa [prefixWord, tailWord_2830935, baseEnd_2830935] using wordTrace_append hprefix tailTrace_2830935
  have hstable : (prefixWord ++ tailWord_2830935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830935).length < 2 ^ (prefixWord ++ tailWord_2830935).sum := by decide
  have hdescent : baseEnd_2830935 < baseStart_2830935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830948 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 3, 3, 3]
def baseStart_2830948 : Nat := 118140960795 + 2830948 * 2 ^ 59
def prefixEnd_2830948 : Nat := 4983230072969 + 3 ^ 40 * 2830948 * 2
def baseEnd_2830948 : Nat := 1453637031884495136630713

theorem tailTrace_2830948 : CollatzResearch.WordTrace tailWord_2830948 prefixEnd_2830948 1453637031884495136630713 := by
  unfold tailWord_2830948
  simp only [CollatzResearch.WordTrace]
  refine ⟨51626578073983179135554749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68835437431977572180739665 51626578073983179135554749)
  ·
    refine ⟨19359966777743692175833031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51626578073983179135554749 19359966777743692175833031)
    ·
      refine ⟨29039950166615538263749547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19359966777743692175833031 29039950166615538263749547)
      ·
        refine ⟨43559925249923307395624321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29039950166615538263749547 43559925249923307395624321)
        ·
          refine ⟨32669943937442480546718241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43559925249923307395624321 32669943937442480546718241)
          ·
            refine ⟨24502457953081860410038681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32669943937442480546718241 24502457953081860410038681)
            ·
              refine ⟨18376843464811395307529011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24502457953081860410038681 18376843464811395307529011)
              ·
                refine ⟨27565265197217092961293517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18376843464811395307529011 27565265197217092961293517)
                ·
                  refine ⟨10336974448956409860485069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27565265197217092961293517 10336974448956409860485069)
                  ·
                    refine ⟨3876365418358653697681901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10336974448956409860485069 3876365418358653697681901)
                    ·
                      refine ⟨1453637031884495136630713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3876365418358653697681901 1453637031884495136630713)
                      ·
                        rfl

theorem cell23_2830948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_2830948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830948 prefixEnd_2830948 := by exact prefixLift 2830948
  have htrace : WordTrace (prefixWord ++ tailWord_2830948) baseStart_2830948 baseEnd_2830948 := by
    simpa [prefixWord, tailWord_2830948, baseEnd_2830948] using wordTrace_append hprefix tailTrace_2830948
  have hstable : (prefixWord ++ tailWord_2830948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830948).length < 2 ^ (prefixWord ++ tailWord_2830948).sum := by decide
  have hdescent : baseEnd_2830948 < baseStart_2830948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830951 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 1, 9]
def baseStart_2830951 : Nat := 118140960795 + 2830951 * 2 ^ 59
def prefixEnd_2830951 : Nat := 4983230072969 + 3 ^ 40 * 2830951 * 2
def baseEnd_2830951 : Nat := 484546190775486208297733

theorem tailTrace_2830951 : CollatzResearch.WordTrace tailWord_2830951 prefixEnd_2830951 484546190775486208297733 := by
  unfold tailWord_2830951
  simp only [CollatzResearch.WordTrace]
  refine ⟨103253265566955489783468707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68835510377970326522312471 103253265566955489783468707)
  ·
    refine ⟨154879898350433234675203061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103253265566955489783468707 154879898350433234675203061)
    ·
      refine ⟨14519990470353115750800287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154879898350433234675203061 14519990470353115750800287)
      ·
        refine ⟨21779985705529673626200431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14519990470353115750800287 21779985705529673626200431)
        ·
          refine ⟨32669978558294510439300647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21779985705529673626200431 32669978558294510439300647)
          ·
            refine ⟨49004967837441765658950971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32669978558294510439300647 49004967837441765658950971)
            ·
              refine ⟨73507451756162648488426457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49004967837441765658950971 73507451756162648488426457)
              ·
                refine ⟨55130588817121986366319843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73507451756162648488426457 55130588817121986366319843)
                ·
                  refine ⟨82695883225682979549479765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55130588817121986366319843 82695883225682979549479765)
                  ·
                    refine ⟨484546190775486208297733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 82695883225682979549479765 484546190775486208297733)
                    ·
                      rfl

theorem cell23_2830951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_2830951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830951 prefixEnd_2830951 := by exact prefixLift 2830951
  have htrace : WordTrace (prefixWord ++ tailWord_2830951) baseStart_2830951 baseEnd_2830951 := by
    simpa [prefixWord, tailWord_2830951, baseEnd_2830951] using wordTrace_append hprefix tailTrace_2830951
  have hstable : (prefixWord ++ tailWord_2830951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830951).length < 2 ^ (prefixWord ++ tailWord_2830951).sum := by decide
  have hdescent : baseEnd_2830951 < baseStart_2830951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830966 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2]
def baseStart_2830966 : Nat := 118140960795 + 2830966 * 2 ^ 59
def prefixEnd_2830966 : Nat := 4983230072969 + 3 ^ 40 * 2830966 * 2
def baseEnd_2830966 : Nat := 1453646274536276066205631

theorem tailTrace_2830966 : CollatzResearch.WordTrace tailWord_2830966 prefixEnd_2830966 1453646274536276066205631 := by
  unfold tailWord_2830966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6453363291368821709079047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68835875107934098230176501 6453363291368821709079047)
  ·
    refine ⟨9680044937053232563618571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6453363291368821709079047 9680044937053232563618571)
    ·
      refine ⟨14520067405579848845427857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9680044937053232563618571 14520067405579848845427857)
      ·
        refine ⟨10890050554184886634070893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14520067405579848845427857 10890050554184886634070893)
        ·
          refine ⟨4083768957819332487776585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10890050554184886634070893 4083768957819332487776585)
          ·
            refine ⟨3062826718364499365832439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4083768957819332487776585 3062826718364499365832439)
            ·
              refine ⟨4594240077546749048748659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062826718364499365832439 4594240077546749048748659)
              ·
                refine ⟨6891360116320123573122989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4594240077546749048748659 6891360116320123573122989)
                ·
                  refine ⟨2584260043620046339921121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6891360116320123573122989 2584260043620046339921121)
                  ·
                    refine ⟨1938195032715034754940841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2584260043620046339921121 1938195032715034754940841)
                    ·
                      refine ⟨1453646274536276066205631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1938195032715034754940841 1453646274536276066205631)
                      ·
                        rfl

theorem cell23_2830966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_2830966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830966 prefixEnd_2830966 := by exact prefixLift 2830966
  have htrace : WordTrace (prefixWord ++ tailWord_2830966) baseStart_2830966 baseEnd_2830966 := by
    simpa [prefixWord, tailWord_2830966, baseEnd_2830966] using wordTrace_append hprefix tailTrace_2830966
  have hstable : (prefixWord ++ tailWord_2830966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830966).length < 2 ^ (prefixWord ++ tailWord_2830966).sum := by decide
  have hdescent : baseEnd_2830966 < baseStart_2830966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830991 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 5]
def baseStart_2830991 : Nat := 118140960795 + 2830991 * 2 ^ 59
def prefixEnd_2830991 : Nat := 4983230072969 + 3 ^ 40 * 2830991 * 2
def baseEnd_2830991 : Nat := 1453659111552638468393015

theorem tailTrace_2830991 : CollatzResearch.WordTrace tailWord_2830991 prefixEnd_2830991 1453659111552638468393015 := by
  unfold tailWord_2830991
  simp only [CollatzResearch.WordTrace]
  refine ⟨103254724486810576614924827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68836482991207051076616551 103254724486810576614924827)
  ·
    refine ⟨154882086730215864922387241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103254724486810576614924827 154882086730215864922387241)
    ·
      refine ⟨116161565047661898691790431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154882086730215864922387241 116161565047661898691790431)
      ·
        refine ⟨174242347571492848037685647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116161565047661898691790431 174242347571492848037685647)
        ·
          refine ⟨261363521357239272056528471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174242347571492848037685647 261363521357239272056528471)
          ·
            refine ⟨392045282035858908084792707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261363521357239272056528471 392045282035858908084792707)
            ·
              refine ⟨588067923053788362127189061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392045282035858908084792707 588067923053788362127189061)
              ·
                refine ⟨110262735572585317898847949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 588067923053788362127189061 110262735572585317898847949)
                ·
                  refine ⟨41348525839719494212067981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110262735572585317898847949 41348525839719494212067981)
                  ·
                    refine ⟨15505697189894810329525493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41348525839719494212067981 15505697189894810329525493)
                    ·
                      refine ⟨1453659111552638468393015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15505697189894810329525493 1453659111552638468393015)
                      ·
                        rfl

theorem cell23_2830991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_2830991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2830991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2830991 prefixEnd_2830991 := by exact prefixLift 2830991
  have htrace : WordTrace (prefixWord ++ tailWord_2830991) baseStart_2830991 baseEnd_2830991 := by
    simpa [prefixWord, tailWord_2830991, baseEnd_2830991] using wordTrace_append hprefix tailTrace_2830991
  have hstable : (prefixWord ++ tailWord_2830991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830991).length < 2 ^ (prefixWord ++ tailWord_2830991).sum := by decide
  have hdescent : baseEnd_2830991 < baseStart_2830991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831005 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 3, 4, 2]
def baseStart_2831005 : Nat := 118140960795 + 2831005 * 2 ^ 59
def prefixEnd_2831005 : Nat := 4983230072969 + 3 ^ 40 * 2831005 * 2
def baseEnd_2831005 : Nat := 1453666300281801413617951

theorem tailTrace_2831005 : CollatzResearch.WordTrace tailWord_2831005 prefixEnd_2831005 1453666300281801413617951 := by
  unfold tailWord_2831005
  simp only [CollatzResearch.WordTrace]
  refine ⟨103255235108759857005934469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68836823405839904670622979 103255235108759857005934469)
  ·
    refine ⟨19360356582892473188612713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103255235108759857005934469 19360356582892473188612713)
    ·
      refine ⟨14520267437169354891459535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19360356582892473188612713 14520267437169354891459535)
      ·
        refine ⟨21780401155754032337189303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14520267437169354891459535 21780401155754032337189303)
        ·
          refine ⟨32670601733631048505783955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21780401155754032337189303 32670601733631048505783955)
          ·
            refine ⟨49005902600446572758675933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32670601733631048505783955 49005902600446572758675933)
            ·
              refine ⟨18377213475167464784503475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49005902600446572758675933 18377213475167464784503475)
              ·
                refine ⟨27565820212751197176755213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18377213475167464784503475 27565820212751197176755213)
                ·
                  refine ⟨10337182579781698941283205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27565820212751197176755213 10337182579781698941283205)
                  ·
                    refine ⟨1938221733709068551490601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10337182579781698941283205 1938221733709068551490601)
                    ·
                      refine ⟨1453666300281801413617951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1938221733709068551490601 1453666300281801413617951)
                      ·
                        rfl

theorem cell23_2831005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_2831005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831005 prefixEnd_2831005 := by exact prefixLift 2831005
  have htrace : WordTrace (prefixWord ++ tailWord_2831005) baseStart_2831005 baseEnd_2831005 := by
    simpa [prefixWord, tailWord_2831005, baseEnd_2831005] using wordTrace_append hprefix tailTrace_2831005
  have hstable : (prefixWord ++ tailWord_2831005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831005).length < 2 ^ (prefixWord ++ tailWord_2831005).sum := by decide
  have hdescent : baseEnd_2831005 < baseStart_2831005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831011 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 11]
def baseStart_2831011 : Nat := 118140960795 + 2831011 * 2 ^ 59
def prefixEnd_2831011 : Nat := 4983230072969 + 3 ^ 40 * 2831011 * 2
def baseEnd_2831011 : Nat := 161518820129525376682547

theorem tailTrace_2831011 : CollatzResearch.WordTrace tailWord_2831011 prefixEnd_2831011 161518820129525376682547 := by
  unfold tailWord_2831011
  simp only [CollatzResearch.WordTrace]
  refine ⟨103255453946738120030652887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68836969297825413353768591 103255453946738120030652887)
  ·
    refine ⟨154883180920107180045979331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103255453946738120030652887 154883180920107180045979331)
    ·
      refine ⟨232324771380160770068968997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154883180920107180045979331 232324771380160770068968997)
      ·
        refine ⟨43560894633780144387931687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232324771380160770068968997 43560894633780144387931687)
        ·
          refine ⟨65341341950670216581897531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43560894633780144387931687 65341341950670216581897531)
          ·
            refine ⟨98012012926005324872846297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65341341950670216581897531 98012012926005324872846297)
            ·
              refine ⟨73509009694503993654634723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98012012926005324872846297 73509009694503993654634723)
              ·
                refine ⟨110263514541755990481952085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73509009694503993654634723 110263514541755990481952085)
                ·
                  refine ⟨161518820129525376682547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 110263514541755990481952085 161518820129525376682547)
                  ·
                    rfl

theorem cell23_2831011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 11].length) (baseStart_2831011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831011 prefixEnd_2831011 := by exact prefixLift 2831011
  have htrace : WordTrace (prefixWord ++ tailWord_2831011) baseStart_2831011 baseEnd_2831011 := by
    simpa [prefixWord, tailWord_2831011, baseEnd_2831011] using wordTrace_append hprefix tailTrace_2831011
  have hstable : (prefixWord ++ tailWord_2831011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831011).length < 2 ^ (prefixWord ++ tailWord_2831011).sum := by decide
  have hdescent : baseEnd_2831011 < baseStart_2831011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831115 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 3]
def baseStart_2831115 : Nat := 118140960795 + 2831115 * 2 ^ 59
def prefixEnd_2831115 : Nat := 4983230072969 + 3 ^ 40 * 2831115 * 2
def baseEnd_2831115 : Nat := 1453722783153795983242445

theorem tailTrace_2831115 : CollatzResearch.WordTrace tailWord_2831115 prefixEnd_2831115 1453722783153795983242445 := by
  unfold tailWord_2831115
  simp only [CollatzResearch.WordTrace]
  refine ⟨103259247138361345792438799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68839498092240897194959199 103259247138361345792438799)
  ·
    refine ⟨154888870707542018688658199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103259247138361345792438799 154888870707542018688658199)
    ·
      refine ⟨232333306061313028032987299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154888870707542018688658199 232333306061313028032987299)
      ·
        refine ⟨348499959091969542049480949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232333306061313028032987299 348499959091969542049480949)
        ·
          refine ⟨32671871164872144567138839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 348499959091969542049480949 32671871164872144567138839)
          ·
            refine ⟨49007806747308216850708259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32671871164872144567138839 49007806747308216850708259)
            ·
              refine ⟨73511710120962325276062389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49007806747308216850708259 73511710120962325276062389)
              ·
                refine ⟨6891722823840217994630849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73511710120962325276062389 6891722823840217994630849)
                ·
                  refine ⟨5168792117880163495973137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6891722823840217994630849 5168792117880163495973137)
                  ·
                    refine ⟨3876594088410122621979853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5168792117880163495973137 3876594088410122621979853)
                    ·
                      refine ⟨1453722783153795983242445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3876594088410122621979853 1453722783153795983242445)
                      ·
                        rfl

theorem cell23_2831115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 3].length) (baseStart_2831115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831115 prefixEnd_2831115 := by exact prefixLift 2831115
  have htrace : WordTrace (prefixWord ++ tailWord_2831115) baseStart_2831115 baseEnd_2831115 := by
    simpa [prefixWord, tailWord_2831115, baseEnd_2831115] using wordTrace_append hprefix tailTrace_2831115
  have hstable : (prefixWord ++ tailWord_2831115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831115).length < 2 ^ (prefixWord ++ tailWord_2831115).sum := by decide
  have hdescent : baseEnd_2831115 < baseStart_2831115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831132 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_2831132 : Nat := 118140960795 + 2831132 * 2 ^ 59
def prefixEnd_2831132 : Nat := 4983230072969 + 3 ^ 40 * 2831132 * 2
def baseEnd_2831132 : Nat := 1453731512324922416729867

theorem tailTrace_2831132 : CollatzResearch.WordTrace tailWord_2831132 prefixEnd_2831132 1453731512324922416729867 := by
  unfold tailWord_2831132
  simp only [CollatzResearch.WordTrace]
  refine ⟨51629933589649878847903825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68839911452866505130538433 51629933589649878847903825)
  ·
    refine ⟨38722450192237409135927869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51629933589649878847903825 38722450192237409135927869)
    ·
      refine ⟨14520918822089028425972951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38722450192237409135927869 14520918822089028425972951)
      ·
        refine ⟨21781378233133542638959427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14520918822089028425972951 21781378233133542638959427)
        ·
          refine ⟨32672067349700313958439141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21781378233133542638959427 32672067349700313958439141)
          ·
            refine ⟨6126012628068808867207339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32672067349700313958439141 6126012628068808867207339)
            ·
              refine ⟨9189018942103213300811009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6126012628068808867207339 9189018942103213300811009)
              ·
                refine ⟨6891764206577409975608257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9189018942103213300811009 6891764206577409975608257)
                ·
                  refine ⟨5168823154933057481706193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6891764206577409975608257 5168823154933057481706193)
                  ·
                    refine ⟨3876617366199793111279645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5168823154933057481706193 3876617366199793111279645)
                    ·
                      refine ⟨1453731512324922416729867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3876617366199793111279645 1453731512324922416729867)
                      ·
                        rfl

theorem cell23_2831132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_2831132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831132 prefixEnd_2831132 := by exact prefixLift 2831132
  have htrace : WordTrace (prefixWord ++ tailWord_2831132) baseStart_2831132 baseEnd_2831132 := by
    simpa [prefixWord, tailWord_2831132, baseEnd_2831132] using wordTrace_append hprefix tailTrace_2831132
  have hstable : (prefixWord ++ tailWord_2831132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831132).length < 2 ^ (prefixWord ++ tailWord_2831132).sum := by decide
  have hdescent : baseEnd_2831132 < baseStart_2831132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831205 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 1, 1, 5]
def baseStart_2831205 : Nat := 118140960795 + 2831205 * 2 ^ 59
def prefixEnd_2831205 : Nat := 4983230072969 + 3 ^ 40 * 2831205 * 2
def baseEnd_2831205 : Nat := 1453768996412700631117031

theorem tailTrace_2831205 : CollatzResearch.WordTrace tailWord_2831205 prefixEnd_2831205 1453768996412700631117031 := by
  unfold tailWord_2831205
  simp only [CollatzResearch.WordTrace]
  refine ⟨103262529708035291163215069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68841686472023527442143379 103262529708035291163215069)
  ·
    refine ⟨38723448640513234186205651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103262529708035291163215069 38723448640513234186205651)
    ·
      refine ⟨58085172960769851279308477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38723448640513234186205651 58085172960769851279308477)
      ·
        refine ⟨21781939860288694229740679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58085172960769851279308477 21781939860288694229740679)
        ·
          refine ⟨32672909790433041344611019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21781939860288694229740679 32672909790433041344611019)
          ·
            refine ⟨49009364685649562016916529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32672909790433041344611019 49009364685649562016916529)
            ·
              refine ⟨36757023514237171512687397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49009364685649562016916529 36757023514237171512687397)
              ·
                refine ⟨6891941908919469658628887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36757023514237171512687397 6891941908919469658628887)
                ·
                  refine ⟨10337912863379204487943331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6891941908919469658628887 10337912863379204487943331)
                  ·
                    refine ⟨15506869295068806731914997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10337912863379204487943331 15506869295068806731914997)
                    ·
                      refine ⟨1453768996412700631117031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15506869295068806731914997 1453768996412700631117031)
                      ·
                        rfl

theorem cell23_2831205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_2831205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831205 prefixEnd_2831205 := by exact prefixLift 2831205
  have htrace : WordTrace (prefixWord ++ tailWord_2831205) baseStart_2831205 baseEnd_2831205 := by
    simpa [prefixWord, tailWord_2831205, baseEnd_2831205] using wordTrace_append hprefix tailTrace_2831205
  have hstable : (prefixWord ++ tailWord_2831205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831205).length < 2 ^ (prefixWord ++ tailWord_2831205).sum := by decide
  have hdescent : baseEnd_2831205 < baseStart_2831205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831212 : List Nat := [2, 2, 1, 1, 4, 1, 1, 5, 2, 4]
def baseStart_2831212 : Nat := 118140960795 + 2831212 * 2 ^ 59
def prefixEnd_2831212 : Nat := 4983230072969 + 3 ^ 40 * 2831212 * 2
def baseEnd_2831212 : Nat := 484590863592427367909833

theorem tailTrace_2831212 : CollatzResearch.WordTrace tailWord_2831212 prefixEnd_2831212 484590863592427367909833 := by
  unfold tailWord_2831212
  simp only [CollatzResearch.WordTrace]
  refine ⟨51631392509504965679359945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68841856679339954239146593 51631392509504965679359945)
  ·
    refine ⟨38723544382128724259519959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51631392509504965679359945 38723544382128724259519959)
    ·
      refine ⟨58085316573193086389279939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38723544382128724259519959 58085316573193086389279939)
      ·
        refine ⟨87127974859789629583919909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58085316573193086389279939 87127974859789629583919909)
        ·
          refine ⟨16336495286210555546984983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87127974859789629583919909 16336495286210555546984983)
          ·
            refine ⟨24504742929315833320477475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16336495286210555546984983 24504742929315833320477475)
            ·
              refine ⟨36757114393973749980716213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24504742929315833320477475 36757114393973749980716213)
              ·
                refine ⟨3445979474435039060692145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36757114393973749980716213 3445979474435039060692145)
                ·
                  refine ⟨2584484605826279295519109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3445979474435039060692145 2584484605826279295519109)
                  ·
                    refine ⟨484590863592427367909833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2584484605826279295519109 484590863592427367909833)
                    ·
                      rfl

theorem cell23_2831212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_2831212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831212 prefixEnd_2831212 := by exact prefixLift 2831212
  have htrace : WordTrace (prefixWord ++ tailWord_2831212) baseStart_2831212 baseEnd_2831212 := by
    simpa [prefixWord, tailWord_2831212, baseEnd_2831212] using wordTrace_append hprefix tailTrace_2831212
  have hstable : (prefixWord ++ tailWord_2831212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831212).length < 2 ^ (prefixWord ++ tailWord_2831212).sum := by decide
  have hdescent : baseEnd_2831212 < baseStart_2831212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831230 : List Nat := [4, 2, 3, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_2831230 : Nat := 118140960795 + 2831230 * 2 ^ 59
def prefixEnd_2831230 : Nat := 4983230072969 + 3 ^ 40 * 2831230 * 2
def baseEnd_2831230 : Nat := 1453781833429063033304417

theorem tailTrace_2831230 : CollatzResearch.WordTrace tailWord_2831230 prefixEnd_2831230 1453781833429063033304417 := by
  unfold tailWord_2831230
  simp only [CollatzResearch.WordTrace]
  refine ⟨12907930191618090054109393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68842294355296480288583429 12907930191618090054109393)
  ·
    refine ⟨9680947643713567540582045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12907930191618090054109393 9680947643713567540582045)
    ·
      refine ⟨3630355366392587827718267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9680947643713567540582045 3630355366392587827718267)
      ·
        refine ⟨5445533049588881741577401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3630355366392587827718267 5445533049588881741577401)
        ·
          refine ⟨4084149787191661306183051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5445533049588881741577401 4084149787191661306183051)
          ·
            refine ⟨6126224680787491959274577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4084149787191661306183051 6126224680787491959274577)
            ·
              refine ⟨4594668510590618969455933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6126224680787491959274577 4594668510590618969455933)
              ·
                refine ⟨1723000691471482113545975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4594668510590618969455933 1723000691471482113545975)
                ·
                  refine ⟨2584501037207223170318963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1723000691471482113545975 2584501037207223170318963)
                  ·
                    refine ⟨3876751555810834755478445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2584501037207223170318963 3876751555810834755478445)
                    ·
                      refine ⟨1453781833429063033304417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3876751555810834755478445 1453781833429063033304417)
                      ·
                        rfl

theorem cell23_2831230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_2831230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831230 prefixEnd_2831230 := by exact prefixLift 2831230
  have htrace : WordTrace (prefixWord ++ tailWord_2831230) baseStart_2831230 baseEnd_2831230 := by
    simpa [prefixWord, tailWord_2831230, baseEnd_2831230] using wordTrace_append hprefix tailTrace_2831230
  have hstable : (prefixWord ++ tailWord_2831230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831230).length < 2 ^ (prefixWord ++ tailWord_2831230).sum := by decide
  have hdescent : baseEnd_2831230 < baseStart_2831230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831239 : List Nat := [1, 1, 4, 2, 3, 2, 1, 3, 1, 2, 3]
def baseStart_2831239 : Nat := 118140960795 + 2831239 * 2 ^ 59
def prefixEnd_2831239 : Nat := 4983230072969 + 3 ^ 40 * 2831239 * 2
def baseEnd_2831239 : Nat := 1453786454754953498091875

theorem tailTrace_2831239 : CollatzResearch.WordTrace tailWord_2831239 prefixEnd_2831239 1453786454754953498091875 := by
  unfold tailWord_2831239
  simp only [CollatzResearch.WordTrace]
  refine ⟨103263769789912114969952771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68842513193274743313301847 103263769789912114969952771)
  ·
    refine ⟨154895654684868172454929157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103263769789912114969952771 154895654684868172454929157)
    ·
      refine ⟨29042935253412782335299217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154895654684868172454929157 29042935253412782335299217)
      ·
        refine ⟨21782201440059586751474413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29042935253412782335299217 21782201440059586751474413)
        ·
          refine ⟨8168325540022345031802905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21782201440059586751474413 8168325540022345031802905)
          ·
            refine ⟨6126244155016758773852179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8168325540022345031802905 6126244155016758773852179)
            ·
              refine ⟨9189366232525138160778269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6126244155016758773852179 9189366232525138160778269)
              ·
                refine ⟨3446012337196926810291851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9189366232525138160778269 3446012337196926810291851)
                ·
                  refine ⟨5169018505795390215437777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3446012337196926810291851 5169018505795390215437777)
                  ·
                    refine ⟨3876763879346542661578333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5169018505795390215437777 3876763879346542661578333)
                    ·
                      refine ⟨1453786454754953498091875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3876763879346542661578333 1453786454754953498091875)
                      ·
                        rfl

theorem cell23_2831239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_2831239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831239 prefixEnd_2831239 := by exact prefixLift 2831239
  have htrace : WordTrace (prefixWord ++ tailWord_2831239) baseStart_2831239 baseEnd_2831239 := by
    simpa [prefixWord, tailWord_2831239, baseEnd_2831239] using wordTrace_append hprefix tailTrace_2831239
  have hstable : (prefixWord ++ tailWord_2831239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831239).length < 2 ^ (prefixWord ++ tailWord_2831239).sum := by decide
  have hdescent : baseEnd_2831239 < baseStart_2831239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831330 : List Nat := [3, 3, 3, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_2831330 : Nat := 118140960795 + 2831330 * 2 ^ 59
def prefixEnd_2831330 : Nat := 4983230072969 + 3 ^ 40 * 2831330 * 2
def baseEnd_2831330 : Nat := 1453833181494512642053957

theorem tailTrace_2831330 : CollatzResearch.WordTrace tailWord_2831330 prefixEnd_2831330 1453833181494512642053957 := by
  unfold tailWord_2831330
  simp only [CollatzResearch.WordTrace]
  refine ⟨25816772208145609377878861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68844725888388291674343629 25816772208145609377878861)
  ·
    refine ⟨9681289578054603516704573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25816772208145609377878861 9681289578054603516704573)
    ·
      refine ⟨3630483591770476318764215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9681289578054603516704573 3630483591770476318764215)
      ·
        refine ⟨5445725387655714478146323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3630483591770476318764215 5445725387655714478146323)
        ·
          refine ⟨8168588081483571717219485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5445725387655714478146323 8168588081483571717219485)
          ·
            refine ⟨3063220530556339393957307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8168588081483571717219485 3063220530556339393957307)
            ·
              refine ⟨4594830795834509090935961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3063220530556339393957307 4594830795834509090935961)
              ·
                refine ⟨3446123096875881818201971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4594830795834509090935961 3446123096875881818201971)
                ·
                  refine ⟨5169184645313822727302957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3446123096875881818201971 5169184645313822727302957)
                  ·
                    refine ⟨1938444241992683522738609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5169184645313822727302957 1938444241992683522738609)
                    ·
                      refine ⟨1453833181494512642053957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1938444241992683522738609 1453833181494512642053957)
                      ·
                        rfl

theorem cell23_2831330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_2831330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831330 prefixEnd_2831330 := by exact prefixLift 2831330
  have htrace : WordTrace (prefixWord ++ tailWord_2831330) baseStart_2831330 baseEnd_2831330 := by
    simpa [prefixWord, tailWord_2831330, baseEnd_2831330] using wordTrace_append hprefix tailTrace_2831330
  have hstable : (prefixWord ++ tailWord_2831330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831330).length < 2 ^ (prefixWord ++ tailWord_2831330).sum := by decide
  have hdescent : baseEnd_2831330 < baseStart_2831330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831372 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 1, 2, 5]
def baseStart_2831372 : Nat := 118140960795 + 2831372 * 2 ^ 59
def prefixEnd_2831372 : Nat := 4983230072969 + 3 ^ 40 * 2831372 * 2
def baseEnd_2831372 : Nat := 1453854747682001477728763

theorem tailTrace_2831372 : CollatzResearch.WordTrace tailWord_2831372 prefixEnd_2831372 1453854747682001477728763 := by
  unfold tailWord_2831372
  simp only [CollatzResearch.WordTrace]
  refine ⟨51634310349215139342272185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68845747132286852456362913 51634310349215139342272185)
  ·
    refine ⟨38725732761911354506704139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51634310349215139342272185 38725732761911354506704139)
    ·
      refine ⟨58088599142867031760056209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38725732761911354506704139 58088599142867031760056209)
      ·
        refine ⟨43566449357150273820042157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58088599142867031760056209 43566449357150273820042157)
        ·
          refine ⟨16337418508931352682515809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43566449357150273820042157 16337418508931352682515809)
          ·
            refine ⟨12253063881698514511886857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16337418508931352682515809 12253063881698514511886857)
            ·
              refine ⟨9189797911273885883915143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12253063881698514511886857 9189797911273885883915143)
              ·
                refine ⟨13784696866910828825872715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9189797911273885883915143 13784696866910828825872715)
                ·
                  refine ⟨20677045300366243238809073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13784696866910828825872715 20677045300366243238809073)
                  ·
                    refine ⟨15507783975274682429106805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20677045300366243238809073 15507783975274682429106805)
                    ·
                      refine ⟨1453854747682001477728763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15507783975274682429106805 1453854747682001477728763)
                      ·
                        rfl

theorem cell23_2831372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_2831372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831372 prefixEnd_2831372 := by exact prefixLift 2831372
  have htrace : WordTrace (prefixWord ++ tailWord_2831372) baseStart_2831372 baseEnd_2831372 := by
    simpa [prefixWord, tailWord_2831372, baseEnd_2831372] using wordTrace_append hprefix tailTrace_2831372
  have hstable : (prefixWord ++ tailWord_2831372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831372).length < 2 ^ (prefixWord ++ tailWord_2831372).sum := by decide
  have hdescent : baseEnd_2831372 < baseStart_2831372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831396 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 2, 5]
def baseStart_2831396 : Nat := 118140960795 + 2831396 * 2 ^ 59
def prefixEnd_2831396 : Nat := 4983230072969 + 3 ^ 40 * 2831396 * 2
def baseEnd_2831396 : Nat := 484622357072569794609551

theorem tailTrace_2831396 : CollatzResearch.WordTrace tailWord_2831396 prefixEnd_2831396 484622357072569794609551 := by
  unfold tailWord_2831396
  simp only [CollatzResearch.WordTrace]
  refine ⟨51634748025171665391709021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68846330700228887188945361 51634748025171665391709021)
  ·
    refine ⟨19363030509439374521890883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51634748025171665391709021 19363030509439374521890883)
    ·
      refine ⟨29044545764159061782836325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19363030509439374521890883 29044545764159061782836325)
      ·
        refine ⟨5445852330779824084281811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29044545764159061782836325 5445852330779824084281811)
        ·
          refine ⟨8168778496169736126422717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5445852330779824084281811 8168778496169736126422717)
          ·
            refine ⟨3063291936063651047408519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8168778496169736126422717 3063291936063651047408519)
            ·
              refine ⟨4594937904095476571112779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3063291936063651047408519 4594937904095476571112779)
              ·
                refine ⟨6892406856143214856669169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4594937904095476571112779 6892406856143214856669169)
                ·
                  refine ⟨5169305142107411142501877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6892406856143214856669169 5169305142107411142501877)
                  ·
                    refine ⟨484622357072569794609551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5169305142107411142501877 484622357072569794609551)
                    ·
                      rfl

theorem cell23_2831396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_2831396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831396 prefixEnd_2831396 := by exact prefixLift 2831396
  have htrace : WordTrace (prefixWord ++ tailWord_2831396) baseStart_2831396 baseEnd_2831396 := by
    simpa [prefixWord, tailWord_2831396, baseEnd_2831396] using wordTrace_append hprefix tailTrace_2831396
  have hstable : (prefixWord ++ tailWord_2831396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831396).length < 2 ^ (prefixWord ++ tailWord_2831396).sum := by decide
  have hdescent : baseEnd_2831396 < baseStart_2831396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831449 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 5, 1, 3]
def baseStart_2831449 : Nat := 118140960795 + 2831449 * 2 ^ 59
def prefixEnd_2831449 : Nat := 4983230072969 + 3 ^ 40 * 2831449 * 2
def baseEnd_2831449 : Nat := 1453894285692397676465909

theorem tailTrace_2831449 : CollatzResearch.WordTrace tailWord_2831449 prefixEnd_2831449 1453894285692397676465909 := by
  unfold tailWord_2831449
  simp only [CollatzResearch.WordTrace]
  refine ⟨103271429119151320835097401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68847619412767547223398267 103271429119151320835097401)
  ·
    refine ⟨77453571839363490626323051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103271429119151320835097401 77453571839363490626323051)
    ·
      refine ⟨116180357759045235939484577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77453571839363490626323051 116180357759045235939484577)
      ·
        refine ⟨87135268319283926954613433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116180357759045235939484577 87135268319283926954613433)
        ·
          refine ⟨65351451239462945215960075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87135268319283926954613433 65351451239462945215960075)
          ·
            refine ⟨98027176859194417823940113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65351451239462945215960075 98027176859194417823940113)
            ·
              refine ⟨73520382644395813367955085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98027176859194417823940113 73520382644395813367955085)
              ·
                refine ⟨27570143491648430012983157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73520382644395813367955085 27570143491648430012983157)
                ·
                  refine ⟨2584700952342040313717171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27570143491648430012983157 2584700952342040313717171)
                  ·
                    refine ⟨3877051428513060470575757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2584700952342040313717171 3877051428513060470575757)
                    ·
                      refine ⟨1453894285692397676465909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3877051428513060470575757 1453894285692397676465909)
                      ·
                        rfl

theorem cell23_2831449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_2831449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831449 prefixEnd_2831449 := by exact prefixLift 2831449
  have htrace : WordTrace (prefixWord ++ tailWord_2831449) baseStart_2831449 baseEnd_2831449 := by
    simpa [prefixWord, tailWord_2831449, baseEnd_2831449] using wordTrace_append hprefix tailTrace_2831449
  have hstable : (prefixWord ++ tailWord_2831449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831449).length < 2 ^ (prefixWord ++ tailWord_2831449).sum := by decide
  have hdescent : baseEnd_2831449 < baseStart_2831449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831477 : List Nat := [1, 3, 4, 3, 1, 1, 3, 2, 1, 4]
def baseStart_2831477 : Nat := 118140960795 + 2831477 * 2 ^ 59
def prefixEnd_2831477 : Nat := 4983230072969 + 3 ^ 40 * 2831477 * 2
def baseEnd_2831477 : Nat := 484636221050241188971927

theorem tailTrace_2831477 : CollatzResearch.WordTrace tailWord_2831477 prefixEnd_2831477 484636221050241188971927 := by
  unfold tailWord_2831477
  simp only [CollatzResearch.WordTrace]
  refine ⟨103272450363049881617116685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68848300242033254411411123 103272450363049881617116685)
  ·
    refine ⟨38727168886143705606418757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103272450363049881617116685 38727168886143705606418757)
    ·
      refine ⟨7261344166151944801203517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38727168886143705606418757 7261344166151944801203517)
      ·
        refine ⟨2723004062306979300451319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7261344166151944801203517 2723004062306979300451319)
        ·
          refine ⟨4084506093460468950676979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2723004062306979300451319 4084506093460468950676979)
          ·
            refine ⟨6126759140190703426015469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4084506093460468950676979 6126759140190703426015469)
            ·
              refine ⟨2297534677571513784755801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6126759140190703426015469 2297534677571513784755801)
              ·
                refine ⟨1723151008178635338566851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2297534677571513784755801 1723151008178635338566851)
                ·
                  refine ⟨2584726512267953007850277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1723151008178635338566851 2584726512267953007850277)
                  ·
                    refine ⟨484636221050241188971927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2584726512267953007850277 484636221050241188971927)
                    ·
                      rfl

theorem cell23_2831477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_2831477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831477 prefixEnd_2831477 := by exact prefixLift 2831477
  have htrace : WordTrace (prefixWord ++ tailWord_2831477) baseStart_2831477 baseEnd_2831477 := by
    simpa [prefixWord, tailWord_2831477, baseEnd_2831477] using wordTrace_append hprefix tailTrace_2831477
  have hstable : (prefixWord ++ tailWord_2831477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831477).length < 2 ^ (prefixWord ++ tailWord_2831477).sum := by decide
  have hdescent : baseEnd_2831477 < baseStart_2831477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831506 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_2831506 : Nat := 118140960795 + 2831506 * 2 ^ 59
def prefixEnd_2831506 : Nat := 4983230072969 + 3 ^ 40 * 2831506 * 2
def baseEnd_2831506 : Nat := 1453923554089703953453147

theorem tailTrace_2831506 : CollatzResearch.WordTrace tailWord_2831506 prefixEnd_2831506 1453923554089703953453147 := by
  unfold tailWord_2831506
  simp only [CollatzResearch.WordTrace]
  refine ⟨25818377019986204892480593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68849005386629879713281581 25818377019986204892480593)
  ·
    refine ⟨19363782764989653669360445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25818377019986204892480593 19363782764989653669360445)
    ·
      refine ⟨7261418536871120126010167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19363782764989653669360445 7261418536871120126010167)
      ·
        refine ⟨10892127805306680189015251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7261418536871120126010167 10892127805306680189015251)
        ·
          refine ⟨16338191707960020283522877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10892127805306680189015251 16338191707960020283522877)
          ·
            refine ⟨6126821890485007606321079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16338191707960020283522877 6126821890485007606321079)
            ·
              refine ⟨9190232835727511409481619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6126821890485007606321079 9190232835727511409481619)
              ·
                refine ⟨13785349253591267114222429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9190232835727511409481619 13785349253591267114222429)
                ·
                  refine ⟨5169505970096725167833411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13785349253591267114222429 5169505970096725167833411)
                  ·
                    refine ⟨7754258955145087751750117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5169505970096725167833411 7754258955145087751750117)
                    ·
                      refine ⟨1453923554089703953453147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7754258955145087751750117 1453923554089703953453147)
                      ·
                        rfl

theorem cell23_2831506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_2831506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831506 prefixEnd_2831506 := by exact prefixLift 2831506
  have htrace : WordTrace (prefixWord ++ tailWord_2831506) baseStart_2831506 baseEnd_2831506 := by
    simpa [prefixWord, tailWord_2831506, baseEnd_2831506] using wordTrace_append hprefix tailTrace_2831506
  have hstable : (prefixWord ++ tailWord_2831506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831506).length < 2 ^ (prefixWord ++ tailWord_2831506).sum := by decide
  have hdescent : baseEnd_2831506 < baseStart_2831506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831532 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 6]
def baseStart_2831532 : Nat := 118140960795 + 2831532 * 2 ^ 59
def prefixEnd_2831532 : Nat := 4983230072969 + 3 ^ 40 * 2831532 * 2
def baseEnd_2831532 : Nat := 1453936904586720851728027

theorem tailTrace_2831532 : CollatzResearch.WordTrace tailWord_2831532 prefixEnd_2831532 1453936904586720851728027 := by
  unfold tailWord_2831532
  simp only [CollatzResearch.WordTrace]
  refine ⟨51637228188925313005184425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68849637585233750673579233 51637228188925313005184425)
  ·
    refine ⟨38727921141693984753888319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51637228188925313005184425 38727921141693984753888319)
    ·
      refine ⟨58091881712540977130832479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38727921141693984753888319 58091881712540977130832479)
      ·
        refine ⟨87137822568811465696248719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58091881712540977130832479 87137822568811465696248719)
        ·
          refine ⟨130706733853217198544373079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87137822568811465696248719 130706733853217198544373079)
          ·
            refine ⟨196060100779825797816559619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130706733853217198544373079 196060100779825797816559619)
            ·
              refine ⟨294090151169738696724839429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196060100779825797816559619 294090151169738696724839429)
              ·
                refine ⟨55141903344326005635907393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 294090151169738696724839429 55141903344326005635907393)
                ·
                  refine ⟨41356427508244504226930545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55141903344326005635907393 41356427508244504226930545)
                  ·
                    refine ⟨31017320631183378170197909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41356427508244504226930545 31017320631183378170197909)
                    ·
                      refine ⟨1453936904586720851728027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31017320631183378170197909 1453936904586720851728027)
                      ·
                        rfl

theorem cell23_2831532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_2831532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831532 prefixEnd_2831532 := by exact prefixLift 2831532
  have htrace : WordTrace (prefixWord ++ tailWord_2831532) baseStart_2831532 baseEnd_2831532 := by
    simpa [prefixWord, tailWord_2831532, baseEnd_2831532] using wordTrace_append hprefix tailTrace_2831532
  have hstable : (prefixWord ++ tailWord_2831532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831532).length < 2 ^ (prefixWord ++ tailWord_2831532).sum := by decide
  have hdescent : baseEnd_2831532 < baseStart_2831532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831553 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_2831553 : Nat := 118140960795 + 2831553 * 2 ^ 59
def prefixEnd_2831553 : Nat := 4983230072969 + 3 ^ 40 * 2831553 * 2
def baseEnd_2831553 : Nat := 1453947687680465269565431

theorem tailTrace_2831553 : CollatzResearch.WordTrace tailWord_2831553 prefixEnd_2831553 1453947687680465269565431 := by
  unfold tailWord_2831553
  simp only [CollatzResearch.WordTrace]
  refine ⟨103275222310774546596883313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68850148207183031064588875 103275222310774546596883313)
  ·
    refine ⟨77456416733080909947662485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103275222310774546596883313 77456416733080909947662485)
    ·
      refine ⟨3630769534363167653796679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77456416733080909947662485 3630769534363167653796679)
      ·
        refine ⟨5446154301544751480695019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3630769534363167653796679 5446154301544751480695019)
        ·
          refine ⟨8169231452317127221042529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5446154301544751480695019 8169231452317127221042529)
          ·
            refine ⟨6126923589237845415781897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8169231452317127221042529 6126923589237845415781897)
            ·
              refine ⟨4595192691928384061836423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6126923589237845415781897 4595192691928384061836423)
              ·
                refine ⟨6892789037892576092754635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4595192691928384061836423 6892789037892576092754635)
                ·
                  refine ⟨10339183556838864139131953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6892789037892576092754635 10339183556838864139131953)
                  ·
                    refine ⟨7754387667629148104348965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10339183556838864139131953 7754387667629148104348965)
                    ·
                      refine ⟨1453947687680465269565431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7754387667629148104348965 1453947687680465269565431)
                      ·
                        rfl

theorem cell23_2831553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_2831553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831553 prefixEnd_2831553 := by exact prefixLift 2831553
  have htrace : WordTrace (prefixWord ++ tailWord_2831553) baseStart_2831553 baseEnd_2831553 := by
    simpa [prefixWord, tailWord_2831553, baseEnd_2831553] using wordTrace_append hprefix tailTrace_2831553
  have hstable : (prefixWord ++ tailWord_2831553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831553).length < 2 ^ (prefixWord ++ tailWord_2831553).sum := by decide
  have hdescent : baseEnd_2831553 < baseStart_2831553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831574 : List Nat := [5, 2, 1, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_2831574 : Nat := 118140960795 + 2831574 * 2 ^ 59
def prefixEnd_2831574 : Nat := 4983230072969 + 3 ^ 40 * 2831574 * 2
def baseEnd_2831574 : Nat := 1453958470774209687402835

theorem tailTrace_2831574 : CollatzResearch.WordTrace tailWord_2831574 prefixEnd_2831574 1453958470774209687402835 := by
  unfold tailWord_2831574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6454749265231154198962361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68850658829132311455598517 6454749265231154198962361)
  ·
    refine ⟨4841061948923365649221771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6454749265231154198962361 4841061948923365649221771)
    ·
      refine ⟨7261592923385048473832657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4841061948923365649221771 7261592923385048473832657)
      ·
        refine ⟨5446194692538786355374493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7261592923385048473832657 5446194692538786355374493)
        ·
          refine ⟨2042323009702044883265435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5446194692538786355374493 2042323009702044883265435)
          ·
            refine ⟨3063484514553067324898153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2042323009702044883265435 3063484514553067324898153)
            ·
              refine ⟨2297613385914800493673615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3063484514553067324898153 2297613385914800493673615)
              ·
                refine ⟨3446420078872200740510423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2297613385914800493673615 3446420078872200740510423)
                ·
                  refine ⟨5169630118308301110765635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3446420078872200740510423 5169630118308301110765635)
                  ·
                    refine ⟨7754445177462451666148453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5169630118308301110765635 7754445177462451666148453)
                    ·
                      refine ⟨1453958470774209687402835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7754445177462451666148453 1453958470774209687402835)
                      ·
                        rfl

theorem cell23_2831574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_2831574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831574 prefixEnd_2831574 := by exact prefixLift 2831574
  have htrace : WordTrace (prefixWord ++ tailWord_2831574) baseStart_2831574 baseEnd_2831574 := by
    simpa [prefixWord, tailWord_2831574, baseEnd_2831574] using wordTrace_append hprefix tailTrace_2831574
  have hstable : (prefixWord ++ tailWord_2831574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831574).length < 2 ^ (prefixWord ++ tailWord_2831574).sum := by decide
  have hdescent : baseEnd_2831574 < baseStart_2831574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831604 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_2831604 : Nat := 118140960795 + 2831604 * 2 ^ 59
def prefixEnd_2831604 : Nat := 4983230072969 + 3 ^ 40 * 2831604 * 2
def baseEnd_2831604 : Nat := 1453973875193844570027697

theorem tailTrace_2831604 : CollatzResearch.WordTrace tailWord_2831604 prefixEnd_2831604 1453973875193844570027697 := by
  unfold tailWord_2831604
  simp only [CollatzResearch.WordTrace]
  refine ⟨51638541216794891153494933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68851388289059854871326577 51638541216794891153494933)
  ·
    refine ⟨2420556619537260522820075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51638541216794891153494933 2420556619537260522820075)
    ·
      refine ⟨3630834929305890784230113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2420556619537260522820075 3630834929305890784230113)
      ·
        refine ⟨2723126196979418088172585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3630834929305890784230113 2723126196979418088172585)
        ·
          refine ⟨2042344647734563566129439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2723126196979418088172585 2042344647734563566129439)
          ·
            refine ⟨3063516971601845349194159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2042344647734563566129439 3063516971601845349194159)
            ·
              refine ⟨4595275457402768023791239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3063516971601845349194159 4595275457402768023791239)
              ·
                refine ⟨6892913186104152035686859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4595275457402768023791239 6892913186104152035686859)
                ·
                  refine ⟨10339369779156228053530289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6892913186104152035686859 10339369779156228053530289)
                  ·
                    refine ⟨7754527334367171040147717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10339369779156228053530289 7754527334367171040147717)
                    ·
                      refine ⟨1453973875193844570027697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7754527334367171040147717 1453973875193844570027697)
                      ·
                        rfl

theorem cell23_2831604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_2831604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831604 prefixEnd_2831604 := by exact prefixLift 2831604
  have htrace : WordTrace (prefixWord ++ tailWord_2831604) baseStart_2831604 baseEnd_2831604 := by
    simpa [prefixWord, tailWord_2831604, baseEnd_2831604] using wordTrace_append hprefix tailTrace_2831604
  have hstable : (prefixWord ++ tailWord_2831604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831604).length < 2 ^ (prefixWord ++ tailWord_2831604).sum := by decide
  have hdescent : baseEnd_2831604 < baseStart_2831604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831609 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 2, 2, 4]
def baseStart_2831609 : Nat := 118140960795 + 2831609 * 2 ^ 59
def prefixEnd_2831609 : Nat := 4983230072969 + 3 ^ 40 * 2831609 * 2
def baseEnd_2831609 : Nat := 1453976442597117050465173

theorem tailTrace_2831609 : CollatzResearch.WordTrace tailWord_2831609 prefixEnd_2831609 1453976442597117050465173 := by
  unfold tailWord_2831609
  simp only [CollatzResearch.WordTrace]
  refine ⟨103277264798571668160921881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68851509865714445440614587 103277264798571668160921881)
  ·
    refine ⟨77457948598928751120691411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103277264798571668160921881 77457948598928751120691411)
    ·
      refine ⟨116186922898393126681037117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77457948598928751120691411 116186922898393126681037117)
      ·
        refine ⟨43570096086897422505388919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116186922898393126681037117 43570096086897422505388919)
        ·
          refine ⟨65355144130346133758083379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43570096086897422505388919 65355144130346133758083379)
          ·
            refine ⟨98032716195519200637125069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65355144130346133758083379 98032716195519200637125069)
            ·
              refine ⟨36762268573319700238921901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98032716195519200637125069 36762268573319700238921901)
              ·
                refine ⟨13785850714994887589595713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36762268573319700238921901 13785850714994887589595713)
                ·
                  refine ⟨10339388036246165692196785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13785850714994887589595713 10339388036246165692196785)
                  ·
                    refine ⟨7754541027184624269147589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10339388036246165692196785 7754541027184624269147589)
                    ·
                      refine ⟨1453976442597117050465173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7754541027184624269147589 1453976442597117050465173)
                      ·
                        rfl

theorem cell23_2831609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_2831609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831609 prefixEnd_2831609 := by exact prefixLift 2831609
  have htrace : WordTrace (prefixWord ++ tailWord_2831609) baseStart_2831609 baseEnd_2831609 := by
    simpa [prefixWord, tailWord_2831609, baseEnd_2831609] using wordTrace_append hprefix tailTrace_2831609
  have hstable : (prefixWord ++ tailWord_2831609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831609).length < 2 ^ (prefixWord ++ tailWord_2831609).sum := by decide
  have hdescent : baseEnd_2831609 < baseStart_2831609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831619 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 7]
def baseStart_2831619 : Nat := 118140960795 + 2831619 * 2 ^ 59
def prefixEnd_2831619 : Nat := 4983230072969 + 3 ^ 40 * 2831619 * 2
def baseEnd_2831619 : Nat := 161553508600406890148903

theorem tailTrace_2831619 : CollatzResearch.WordTrace tailWord_2831619 prefixEnd_2831619 161553508600406890148903 := by
  unfold tailWord_2831619
  simp only [CollatzResearch.WordTrace]
  refine ⟨103277629528535439868785911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68851753019023626579190607 103277629528535439868785911)
  ·
    refine ⟨154916444292803159803178867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103277629528535439868785911 154916444292803159803178867)
    ·
      refine ⟨232374666439204739704768301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154916444292803159803178867 232374666439204739704768301)
      ·
        refine ⟨87140499914701777389288113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232374666439204739704768301 87140499914701777389288113)
        ·
          refine ⟨65355374936026333041966085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87140499914701777389288113 65355374936026333041966085)
          ·
            refine ⟨12254132800504937445368641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65355374936026333041966085 12254132800504937445368641)
            ·
              refine ⟨9190599600378703084026481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12254132800504937445368641 9190599600378703084026481)
              ·
                refine ⟨6892949700284027313019861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9190599600378703084026481 6892949700284027313019861)
                ·
                  refine ⟨161553508600406890148903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6892949700284027313019861 161553508600406890148903)
                  ·
                    rfl

theorem cell23_2831619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 7].length) (baseStart_2831619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831619 prefixEnd_2831619 := by exact prefixLift 2831619
  have htrace : WordTrace (prefixWord ++ tailWord_2831619) baseStart_2831619 baseEnd_2831619 := by
    simpa [prefixWord, tailWord_2831619, baseEnd_2831619] using wordTrace_append hprefix tailTrace_2831619
  have hstable : (prefixWord ++ tailWord_2831619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831619).length < 2 ^ (prefixWord ++ tailWord_2831619).sum := by decide
  have hdescent : baseEnd_2831619 < baseStart_2831619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831699 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 6]
def baseStart_2831699 : Nat := 118140960795 + 2831699 * 2 ^ 59
def prefixEnd_2831699 : Nat := 4983230072969 + 3 ^ 40 * 2831699 * 2
def baseEnd_2831699 : Nat := 1454022655856021698339759

theorem tailTrace_2831699 : CollatzResearch.WordTrace tailWord_2831699 prefixEnd_2831699 1454022655856021698339759 := by
  unfold tailWord_2831699
  simp only [CollatzResearch.WordTrace]
  refine ⟨103280547368245613531698151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68853698245497075687798767 103280547368245613531698151)
  ·
    refine ⟨154920821052368420297547227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103280547368245613531698151 154920821052368420297547227)
    ·
      refine ⟨232381231578552630446320841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154920821052368420297547227 232381231578552630446320841)
      ·
        refine ⟨174285923683914472834740631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232381231578552630446320841 174285923683914472834740631)
        ·
          refine ⟨261428885525871709252110947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174285923683914472834740631 261428885525871709252110947)
          ·
            refine ⟨392143328288807563878166421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261428885525871709252110947 392143328288807563878166421)
            ·
              refine ⟨18381718513537854556789051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 392143328288807563878166421 18381718513537854556789051)
              ·
                refine ⟨27572577770306781835183577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18381718513537854556789051 27572577770306781835183577)
                ·
                  refine ⟨20679433327730086376387683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27572577770306781835183577 20679433327730086376387683)
                  ·
                    refine ⟨31019149991595129564581525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20679433327730086376387683 31019149991595129564581525)
                    ·
                      refine ⟨1454022655856021698339759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31019149991595129564581525 1454022655856021698339759)
                      ·
                        rfl

theorem cell23_2831699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_2831699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831699 prefixEnd_2831699 := by exact prefixLift 2831699
  have htrace : WordTrace (prefixWord ++ tailWord_2831699) baseStart_2831699 baseEnd_2831699 := by
    simpa [prefixWord, tailWord_2831699, baseEnd_2831699] using wordTrace_append hprefix tailTrace_2831699
  have hstable : (prefixWord ++ tailWord_2831699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831699).length < 2 ^ (prefixWord ++ tailWord_2831699).sum := by decide
  have hdescent : baseEnd_2831699 < baseStart_2831699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831720 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 2, 4, 2]
def baseStart_2831720 : Nat := 118140960795 + 2831720 * 2 ^ 59
def prefixEnd_2831720 : Nat := 4983230072969 + 3 ^ 40 * 2831720 * 2
def baseEnd_2831720 : Nat := 1454033438949766116177163

theorem tailTrace_2831720 : CollatzResearch.WordTrace tailWord_2831720 prefixEnd_2831720 1454033438949766116177163 := by
  unfold tailWord_2831720
  simp only [CollatzResearch.WordTrace]
  refine ⟨51640656650584767059106307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68854208867446356078808409 51640656650584767059106307)
  ·
    refine ⟨77460984975877150588659461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51640656650584767059106307 77460984975877150588659461)
    ·
      refine ⟨14523934682976965735373649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77460984975877150588659461 14523934682976965735373649)
      ·
        refine ⟨10892951012232724301530237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14523934682976965735373649 10892951012232724301530237)
        ·
          refine ⟨4084856629587271613073839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10892951012232724301530237 4084856629587271613073839)
          ·
            refine ⟨6127284944380907419610759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4084856629587271613073839 6127284944380907419610759)
            ·
              refine ⟨9190927416571361129416139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6127284944380907419610759 9190927416571361129416139)
              ·
                refine ⟨13786391124857041694124209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9190927416571361129416139 13786391124857041694124209)
                ·
                  refine ⟨10339793343642781270593157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13786391124857041694124209 10339793343642781270593157)
                  ·
                    refine ⟨1938711251933021488236217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10339793343642781270593157 1938711251933021488236217)
                    ·
                      refine ⟨1454033438949766116177163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1938711251933021488236217 1454033438949766116177163)
                      ·
                        rfl

theorem cell23_2831720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_2831720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831720 prefixEnd_2831720 := by exact prefixLift 2831720
  have htrace : WordTrace (prefixWord ++ tailWord_2831720) baseStart_2831720 baseEnd_2831720 := by
    simpa [prefixWord, tailWord_2831720, baseEnd_2831720] using wordTrace_append hprefix tailTrace_2831720
  have hstable : (prefixWord ++ tailWord_2831720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831720).length < 2 ^ (prefixWord ++ tailWord_2831720).sum := by decide
  have hdescent : baseEnd_2831720 < baseStart_2831720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831770 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3]
def baseStart_2831770 : Nat := 118140960795 + 2831770 * 2 ^ 59
def prefixEnd_2831770 : Nat := 4983230072969 + 3 ^ 40 * 2831770 * 2
def baseEnd_2831770 : Nat := 1454059112982490920551933

theorem tailTrace_2831770 : CollatzResearch.WordTrace tailWord_2831770 prefixEnd_2831770 1454059112982490920551933 := by
  unfold tailWord_2831770
  simp only [CollatzResearch.WordTrace]
  refine ⟨25820784237747098164383191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68855424633992261771688509 25820784237747098164383191)
  ·
    refine ⟨38731176356620647246574787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25820784237747098164383191 38731176356620647246574787)
    ·
      refine ⟨58096764534930970869862181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38731176356620647246574787 58096764534930970869862181)
      ·
        refine ⟨10893143350299557038099159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58096764534930970869862181 10893143350299557038099159)
        ·
          refine ⟨16339715025449335557148739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10893143350299557038099159 16339715025449335557148739)
          ·
            refine ⟨24509572538174003335723109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16339715025449335557148739 24509572538174003335723109)
            ·
              refine ⟨4595544850907625625448083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24509572538174003335723109 4595544850907625625448083)
              ·
                refine ⟨6893317276361438438172125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4595544850907625625448083 6893317276361438438172125)
                ·
                  refine ⟨2584993978635539414314547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6893317276361438438172125 2584993978635539414314547)
                  ·
                    refine ⟨3877490967953309121471821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2584993978635539414314547 3877490967953309121471821)
                    ·
                      refine ⟨1454059112982490920551933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3877490967953309121471821 1454059112982490920551933)
                      ·
                        rfl

theorem cell23_2831770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_2831770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831770 prefixEnd_2831770 := by exact prefixLift 2831770
  have htrace : WordTrace (prefixWord ++ tailWord_2831770) baseStart_2831770 baseEnd_2831770 := by
    simpa [prefixWord, tailWord_2831770, baseEnd_2831770] using wordTrace_append hprefix tailTrace_2831770
  have hstable : (prefixWord ++ tailWord_2831770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831770).length < 2 ^ (prefixWord ++ tailWord_2831770).sum := by decide
  have hdescent : baseEnd_2831770 < baseStart_2831770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831793 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 2, 6, 2]
def baseStart_2831793 : Nat := 118140960795 + 2831793 * 2 ^ 59
def prefixEnd_2831793 : Nat := 4983230072969 + 3 ^ 40 * 2831793 * 2
def baseEnd_2831793 : Nat := 1454070923037544330564327

theorem tailTrace_2831793 : CollatzResearch.WordTrace tailWord_2831793 prefixEnd_2831793 1454070923037544330564327 := by
  unfold tailWord_2831793
  simp only [CollatzResearch.WordTrace]
  refine ⟨103283975829905067585620033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68855983886603378390413355 103283975829905067585620033)
  ·
    refine ⟨77462981872428800689215025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103283975829905067585620033 77462981872428800689215025)
    ·
      refine ⟨58097236404321600516911269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77462981872428800689215025 58097236404321600516911269)
      ·
        refine ⟨10893231825810300096920863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58097236404321600516911269 10893231825810300096920863)
        ·
          refine ⟨16339847738715450145381295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10893231825810300096920863 16339847738715450145381295)
          ·
            refine ⟨24509771608073175218071943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16339847738715450145381295 24509771608073175218071943)
            ·
              refine ⟨36764657412109762827107915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24509771608073175218071943 36764657412109762827107915)
              ·
                refine ⟨55146986118164644240661873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36764657412109762827107915 55146986118164644240661873)
                ·
                  refine ⟨41360239588623483180496405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55146986118164644240661873 41360239588623483180496405)
                  ·
                    refine ⟨1938761230716725774085769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41360239588623483180496405 1938761230716725774085769)
                    ·
                      refine ⟨1454070923037544330564327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1938761230716725774085769 1454070923037544330564327)
                      ·
                        rfl

theorem cell23_2831793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_2831793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831793 prefixEnd_2831793 := by exact prefixLift 2831793
  have htrace : WordTrace (prefixWord ++ tailWord_2831793) baseStart_2831793 baseEnd_2831793 := by
    simpa [prefixWord, tailWord_2831793, baseEnd_2831793] using wordTrace_append hprefix tailTrace_2831793
  have hstable : (prefixWord ++ tailWord_2831793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831793).length < 2 ^ (prefixWord ++ tailWord_2831793).sum := by decide
  have hdescent : baseEnd_2831793 < baseStart_2831793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831830 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_2831830 : Nat := 118140960795 + 2831830 * 2 ^ 59
def prefixEnd_2831830 : Nat := 4983230072969 + 3 ^ 40 * 2831830 * 2
def baseEnd_2831830 : Nat := 1454089921821760685801657

theorem tailTrace_2831830 : CollatzResearch.WordTrace tailWord_2831830 prefixEnd_2831830 1454089921821760685801657 := by
  unfold tailWord_2831830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6455332833173188931544809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68856883553847348603144629 6455332833173188931544809)
  ·
    refine ⟨4841499624879891698658607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6455332833173188931544809 4841499624879891698658607)
    ·
      refine ⟨7262249437319837547987911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4841499624879891698658607 7262249437319837547987911)
      ·
        refine ⟨10893374155979756321981867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7262249437319837547987911 10893374155979756321981867)
        ·
          refine ⟨16340061233969634482972801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10893374155979756321981867 16340061233969634482972801)
          ·
            refine ⟨12255045925477225862229601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16340061233969634482972801 12255045925477225862229601)
            ·
              refine ⟨9191284444107919396672201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12255045925477225862229601 9191284444107919396672201)
              ·
                refine ⟨6893463333080939547504151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9191284444107919396672201 6893463333080939547504151)
                ·
                  refine ⟨10340194999621409321256227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6893463333080939547504151 10340194999621409321256227)
                  ·
                    refine ⟨15510292499432113981884341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10340194999621409321256227 15510292499432113981884341)
                    ·
                      refine ⟨1454089921821760685801657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15510292499432113981884341 1454089921821760685801657)
                      ·
                        rfl

theorem cell23_2831830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_2831830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831830 prefixEnd_2831830 := by exact prefixLift 2831830
  have htrace : WordTrace (prefixWord ++ tailWord_2831830) baseStart_2831830 baseEnd_2831830 := by
    simpa [prefixWord, tailWord_2831830, baseEnd_2831830] using wordTrace_append hprefix tailTrace_2831830
  have hstable : (prefixWord ++ tailWord_2831830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831830).length < 2 ^ (prefixWord ++ tailWord_2831830).sum := by decide
  have hdescent : baseEnd_2831830 < baseStart_2831830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831837 : List Nat := [1, 4, 3, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2831837 : Nat := 118140960795 + 2831837 * 2 ^ 59
def prefixEnd_2831837 : Nat := 4983230072969 + 3 ^ 40 * 2831837 * 2
def baseEnd_2831837 : Nat := 484697838728780719471375

theorem tailTrace_2831837 : CollatzResearch.WordTrace tailWord_2831837 prefixEnd_2831837 484697838728780719471375 := by
  unfold tailWord_2831837
  simp only [CollatzResearch.WordTrace]
  refine ⟨103285580641745663100221765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68857053761163775400147843 103285580641745663100221765)
  ·
    refine ⟨19366046370327311831291581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103285580641745663100221765 19366046370327311831291581)
    ·
      refine ⟨7262267388872741936734343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19366046370327311831291581 7262267388872741936734343)
      ·
        refine ⟨10893401083309112905101515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7262267388872741936734343 10893401083309112905101515)
        ·
          refine ⟨16340101624963669357652273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10893401083309112905101515 16340101624963669357652273)
          ·
            refine ⟨12255076218722752018239205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16340101624963669357652273 12255076218722752018239205)
            ·
              refine ⟨2297826791010516003419851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12255076218722752018239205 2297826791010516003419851)
              ·
                refine ⟨3446740186515774005129777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2297826791010516003419851 3446740186515774005129777)
                ·
                  refine ⟨2585055139886830503847333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3446740186515774005129777 2585055139886830503847333)
                  ·
                    refine ⟨484697838728780719471375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2585055139886830503847333 484697838728780719471375)
                    ·
                      rfl

theorem cell23_2831837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2831837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831837 prefixEnd_2831837 := by exact prefixLift 2831837
  have htrace : WordTrace (prefixWord ++ tailWord_2831837) baseStart_2831837 baseEnd_2831837 := by
    simpa [prefixWord, tailWord_2831837, baseEnd_2831837] using wordTrace_append hprefix tailTrace_2831837
  have hstable : (prefixWord ++ tailWord_2831837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831837).length < 2 ^ (prefixWord ++ tailWord_2831837).sum := by decide
  have hdescent : baseEnd_2831837 < baseStart_2831837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831847 : List Nat := [1, 1, 5, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_2831847 : Nat := 118140960795 + 2831847 * 2 ^ 59
def prefixEnd_2831847 : Nat := 4983230072969 + 3 ^ 40 * 2831847 * 2
def baseEnd_2831847 : Nat := 1454098650992887119289079

theorem tailTrace_2831847 : CollatzResearch.WordTrace tailWord_2831847 prefixEnd_2831847 1454098650992887119289079 := by
  unfold tailWord_2831847
  simp only [CollatzResearch.WordTrace]
  refine ⟨103285945371709434808085795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68857296914472956538723863 103285945371709434808085795)
  ·
    refine ⟨154928918057564152212128693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103285945371709434808085795 154928918057564152212128693)
    ·
      refine ⟨14524586067896639269887065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154928918057564152212128693 14524586067896639269887065)
      ·
        refine ⟨10893439550922479452415299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14524586067896639269887065 10893439550922479452415299)
        ·
          refine ⟨16340159326383719178622949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10893439550922479452415299 16340159326383719178622949)
          ·
            refine ⟨3063779873696947345991803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16340159326383719178622949 3063779873696947345991803)
            ·
              refine ⟨4595669810545421018987705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3063779873696947345991803 4595669810545421018987705)
              ·
                refine ⟨3446752357909065764240779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4595669810545421018987705 3446752357909065764240779)
                ·
                  refine ⟨5170128536863598646361169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3446752357909065764240779 5170128536863598646361169)
                  ·
                    refine ⟨3877596402647698984770877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5170128536863598646361169 3877596402647698984770877)
                    ·
                      refine ⟨1454098650992887119289079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3877596402647698984770877 1454098650992887119289079)
                      ·
                        rfl

theorem cell23_2831847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_2831847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831847 prefixEnd_2831847 := by exact prefixLift 2831847
  have htrace : WordTrace (prefixWord ++ tailWord_2831847) baseStart_2831847 baseEnd_2831847 := by
    simpa [prefixWord, tailWord_2831847, baseEnd_2831847] using wordTrace_append hprefix tailTrace_2831847
  have hstable : (prefixWord ++ tailWord_2831847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831847).length < 2 ^ (prefixWord ++ tailWord_2831847).sum := by decide
  have hdescent : baseEnd_2831847 < baseStart_2831847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831893 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 2, 6]
def baseStart_2831893 : Nat := 118140960795 + 2831893 * 2 ^ 59
def prefixEnd_2831893 : Nat := 4983230072969 + 3 ^ 40 * 2831893 * 2
def baseEnd_2831893 : Nat := 484707423700997979771289

theorem tailTrace_2831893 : CollatzResearch.WordTrace tailWord_2831893 prefixEnd_2831893 484707423700997979771289 := by
  unfold tailWord_2831893
  simp only [CollatzResearch.WordTrace]
  refine ⟨103287623129542784664260333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68858415419695189776173555 103287623129542784664260333)
  ·
    refine ⟨38732858673578544249097625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103287623129542784664260333 38732858673578544249097625)
    ·
      refine ⟨29049644005183908186823219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38732858673578544249097625 29049644005183908186823219)
      ·
        refine ⟨43574466007775862280234829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29049644005183908186823219 43574466007775862280234829)
        ·
          refine ⟨16340424752915948355088061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43574466007775862280234829 16340424752915948355088061)
          ·
            refine ⟨6127659282343480633158023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16340424752915948355088061 6127659282343480633158023)
            ·
              refine ⟨9191488923515220949737035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6127659282343480633158023 9191488923515220949737035)
              ·
                refine ⟨13787233385272831424605553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9191488923515220949737035 13787233385272831424605553)
                ·
                  refine ⟨10340425038954623568454165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13787233385272831424605553 10340425038954623568454165)
                  ·
                    refine ⟨484707423700997979771289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10340425038954623568454165 484707423700997979771289)
                    ·
                      rfl

theorem cell23_2831893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_2831893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831893 prefixEnd_2831893 := by exact prefixLift 2831893
  have htrace : WordTrace (prefixWord ++ tailWord_2831893) baseStart_2831893 baseEnd_2831893 := by
    simpa [prefixWord, tailWord_2831893, baseEnd_2831893] using wordTrace_append hprefix tailTrace_2831893
  have hstable : (prefixWord ++ tailWord_2831893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831893).length < 2 ^ (prefixWord ++ tailWord_2831893).sum := by decide
  have hdescent : baseEnd_2831893 < baseStart_2831893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831916 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 7]
def baseStart_2831916 : Nat := 118140960795 + 2831916 * 2 ^ 59
def prefixEnd_2831916 : Nat := 4983230072969 + 3 ^ 40 * 2831916 * 2
def baseEnd_2831916 : Nat := 1454134081158047349326261

theorem tailTrace_2831916 : CollatzResearch.WordTrace tailWord_2831916 prefixEnd_2831916 1454134081158047349326261 := by
  unfold tailWord_2831916
  simp only [CollatzResearch.WordTrace]
  refine ⟨51644231004229729796173801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68858974672306306394898401 51644231004229729796173801)
  ·
    refine ⟨38733173253172297347130351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51644231004229729796173801 38733173253172297347130351)
    ·
      refine ⟨58099759879758446020695527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38733173253172297347130351 58099759879758446020695527)
      ·
        refine ⟨87149639819637669031043291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58099759879758446020695527 87149639819637669031043291)
        ·
          refine ⟨130724459729456503546564937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87149639819637669031043291 130724459729456503546564937)
          ·
            refine ⟨98043344797092377659923703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130724459729456503546564937 98043344797092377659923703)
            ·
              refine ⟨147065017195638566489885555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98043344797092377659923703 147065017195638566489885555)
              ·
                refine ⟨220597525793457849734828333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147065017195638566489885555 220597525793457849734828333)
                ·
                  refine ⟨82724072172546693650560625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220597525793457849734828333 82724072172546693650560625)
                  ·
                    refine ⟨62043054129410020237920469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82724072172546693650560625 62043054129410020237920469)
                    ·
                      refine ⟨1454134081158047349326261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62043054129410020237920469 1454134081158047349326261)
                      ·
                        rfl

theorem cell23_2831916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_2831916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2831916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2831916 prefixEnd_2831916 := by exact prefixLift 2831916
  have htrace : WordTrace (prefixWord ++ tailWord_2831916) baseStart_2831916 baseEnd_2831916 := by
    simpa [prefixWord, tailWord_2831916, baseEnd_2831916] using wordTrace_append hprefix tailTrace_2831916
  have hstable : (prefixWord ++ tailWord_2831916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831916).length < 2 ^ (prefixWord ++ tailWord_2831916).sum := by decide
  have hdescent : baseEnd_2831916 < baseStart_2831916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832060 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 3, 5]
def baseStart_2832060 : Nat := 118140960795 + 2832060 * 2 ^ 59
def prefixEnd_2832060 : Nat := 4983230072969 + 3 ^ 40 * 2832060 * 2
def baseEnd_2832060 : Nat := 484736007457431595308533

theorem tailTrace_2832060 : CollatzResearch.WordTrace tailWord_2832060 prefixEnd_2832060 484736007457431595308533 := by
  unfold tailWord_2832060
  simp only [CollatzResearch.WordTrace]
  refine ⟨51646857059968886092794817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68862476079958514790393089 51646857059968886092794817)
  ·
    refine ⟨38735142794976664569596113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51646857059968886092794817 38735142794976664569596113)
    ·
      refine ⟨29051357096232498427197085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38735142794976664569596113 29051357096232498427197085)
      ·
        refine ⟨10894258911087186910198907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29051357096232498427197085 10894258911087186910198907)
        ·
          refine ⟨16341388366630780365298361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10894258911087186910198907 16341388366630780365298361)
          ·
            refine ⟨12256041274973085273973771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16341388366630780365298361 12256041274973085273973771)
            ·
              refine ⟨18384061912459627910960657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12256041274973085273973771 18384061912459627910960657)
              ·
                refine ⟨13788046434344720933220493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18384061912459627910960657 13788046434344720933220493)
                ·
                  refine ⟨5170517412879270349957685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13788046434344720933220493 5170517412879270349957685)
                  ·
                    refine ⟨484736007457431595308533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5170517412879270349957685 484736007457431595308533)
                    ·
                      rfl

theorem cell23_2832060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_2832060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832060 prefixEnd_2832060 := by exact prefixLift 2832060
  have htrace : WordTrace (prefixWord ++ tailWord_2832060) baseStart_2832060 baseEnd_2832060 := by
    simpa [prefixWord, tailWord_2832060, baseEnd_2832060] using wordTrace_append hprefix tailTrace_2832060
  have hstable : (prefixWord ++ tailWord_2832060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832060).length < 2 ^ (prefixWord ++ tailWord_2832060).sum := by decide
  have hdescent : baseEnd_2832060 < baseStart_2832060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832074 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 3, 1, 3]
def baseStart_2832074 : Nat := 118140960795 + 2832074 * 2 ^ 59
def prefixEnd_2832074 : Nat := 4983230072969 + 3 ^ 40 * 2832074 * 2
def baseEnd_2832074 : Nat := 1454215211101457731150535

theorem tailTrace_2832074 : CollatzResearch.WordTrace tailWord_2832074 prefixEnd_2832074 1454215211101457731150535 := by
  unfold tailWord_2832074
  simp only [CollatzResearch.WordTrace]
  refine ⟨25823556185471763144149819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68862816494591368384399517 25823556185471763144149819)
  ·
    refine ⟨38735334278207644716224729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25823556185471763144149819 38735334278207644716224729)
    ·
      refine ⟨29051500708655733537168547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38735334278207644716224729 29051500708655733537168547)
      ·
        refine ⟨43577251062983600305752821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29051500708655733537168547 43577251062983600305752821)
        ·
          refine ⟨4085367287154712528664327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43577251062983600305752821 4085367287154712528664327)
          ·
            refine ⟨6128050930732068792996491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4085367287154712528664327 6128050930732068792996491)
            ·
              refine ⟨9192076396098103189494737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6128050930732068792996491 9192076396098103189494737)
              ·
                refine ⟨6894057297073577392121053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9192076396098103189494737 6894057297073577392121053)
                ·
                  refine ⟨2585271486402591522045395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6894057297073577392121053 2585271486402591522045395)
                  ·
                    refine ⟨3877907229603887283068093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2585271486402591522045395 3877907229603887283068093)
                    ·
                      refine ⟨1454215211101457731150535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3877907229603887283068093 1454215211101457731150535)
                      ·
                        rfl

theorem cell23_2832074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_2832074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832074 prefixEnd_2832074 := by exact prefixLift 2832074
  have htrace : WordTrace (prefixWord ++ tailWord_2832074) baseStart_2832074 baseEnd_2832074 := by
    simpa [prefixWord, tailWord_2832074, baseEnd_2832074] using wordTrace_append hprefix tailTrace_2832074
  have hstable : (prefixWord ++ tailWord_2832074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832074).length < 2 ^ (prefixWord ++ tailWord_2832074).sum := by decide
  have hdescent : baseEnd_2832074 < baseStart_2832074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832080 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 1, 8, 2]
def baseStart_2832080 : Nat := 118140960795 + 2832080 * 2 ^ 59
def prefixEnd_2832080 : Nat := 4983230072969 + 3 ^ 40 * 2832080 * 2
def baseEnd_2832080 : Nat := 1454218291985384707675507

theorem tailTrace_2832080 : CollatzResearch.WordTrace tailWord_2832080 prefixEnd_2832080 1454218291985384707675507 := by
  unfold tailWord_2832080
  simp only [CollatzResearch.WordTrace]
  refine ⟨51647221789932657800658847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68862962386576877067545129 51647221789932657800658847)
  ·
    refine ⟨77470832684898986700988271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51647221789932657800658847 77470832684898986700988271)
    ·
      refine ⟨116206249027348480051482407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77470832684898986700988271 116206249027348480051482407)
      ·
        refine ⟨174309373541022720077223611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116206249027348480051482407 174309373541022720077223611)
        ·
          refine ⟨261464060311534080115835417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174309373541022720077223611 261464060311534080115835417)
          ·
            refine ⟨196098045233650560086876563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261464060311534080115835417 196098045233650560086876563)
            ·
              refine ⟨294147067850475840130314845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196098045233650560086876563 294147067850475840130314845)
              ·
                refine ⟨110305150443928440048868067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294147067850475840130314845 110305150443928440048868067)
                ·
                  refine ⟨165457725665892660073302101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110305150443928440048868067 165457725665892660073302101)
                  ·
                    refine ⟨1938957722647179610234009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 165457725665892660073302101 1938957722647179610234009)
                    ·
                      refine ⟨1454218291985384707675507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1938957722647179610234009 1454218291985384707675507)
                      ·
                        rfl

theorem cell23_2832080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 8, 2].length) (baseStart_2832080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832080 prefixEnd_2832080 := by exact prefixLift 2832080
  have htrace : WordTrace (prefixWord ++ tailWord_2832080) baseStart_2832080 baseEnd_2832080 := by
    simpa [prefixWord, tailWord_2832080, baseEnd_2832080] using wordTrace_append hprefix tailTrace_2832080
  have hstable : (prefixWord ++ tailWord_2832080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832080).length < 2 ^ (prefixWord ++ tailWord_2832080).sum := by decide
  have hdescent : baseEnd_2832080 < baseStart_2832080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832084 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 1, 5, 2]
def baseStart_2832084 : Nat := 118140960795 + 2832084 * 2 ^ 59
def prefixEnd_2832084 : Nat := 4983230072969 + 3 ^ 40 * 2832084 * 2
def baseEnd_2832084 : Nat := 1454220345908002692025489

theorem tailTrace_2832084 : CollatzResearch.WordTrace tailWord_2832084 prefixEnd_2832084 1454220345908002692025489 := by
  unfold tailWord_2832084
  simp only [CollatzResearch.WordTrace]
  refine ⟨51647294735925412142231653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68863059647900549522975537 51647294735925412142231653)
  ·
    refine ⟨9683867762986014776668435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51647294735925412142231653 9683867762986014776668435)
    ·
      refine ⟨14525801644479022165002653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9683867762986014776668435 14525801644479022165002653)
      ·
        refine ⟨5447175616679633311875995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14525801644479022165002653 5447175616679633311875995)
        ·
          refine ⟨8170763425019449967813993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5447175616679633311875995 8170763425019449967813993)
          ·
            refine ⟨6128072568764587475860495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8170763425019449967813993 6128072568764587475860495)
            ·
              refine ⟨9192108853146881213790743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6128072568764587475860495 9192108853146881213790743)
              ·
                refine ⟨13788163279720321820686115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9192108853146881213790743 13788163279720321820686115)
                ·
                  refine ⟨20682244919580482731029173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13788163279720321820686115 20682244919580482731029173)
                  ·
                    refine ⟨1938960461210670256033985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20682244919580482731029173 1938960461210670256033985)
                    ·
                      refine ⟨1454220345908002692025489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1938960461210670256033985 1454220345908002692025489)
                      ·
                        rfl

theorem cell23_2832084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_2832084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832084 prefixEnd_2832084 := by exact prefixLift 2832084
  have htrace : WordTrace (prefixWord ++ tailWord_2832084) baseStart_2832084 baseEnd_2832084 := by
    simpa [prefixWord, tailWord_2832084, baseEnd_2832084] using wordTrace_append hprefix tailTrace_2832084
  have hstable : (prefixWord ++ tailWord_2832084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832084).length < 2 ^ (prefixWord ++ tailWord_2832084).sum := by decide
  have hdescent : baseEnd_2832084 < baseStart_2832084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832090 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 1, 6]
def baseStart_2832090 : Nat := 118140960795 + 2832090 * 2 ^ 59
def prefixEnd_2832090 : Nat := 4983230072969 + 3 ^ 40 * 2832090 * 2
def baseEnd_2832090 : Nat := 484741142263976556183487

theorem tailTrace_2832090 : CollatzResearch.WordTrace tailWord_2832090 prefixEnd_2832090 484741142263976556183487 := by
  unfold tailWord_2832090
  simp only [CollatzResearch.WordTrace]
  refine ⟨25823702077457271827295431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68863205539886058206121149 25823702077457271827295431)
  ·
    refine ⟨38735553116185907740943147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25823702077457271827295431 38735553116185907740943147)
    ·
      refine ⟨58103329674278861611414721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38735553116185907740943147 58103329674278861611414721)
      ·
        refine ⟨43577497255709146208561041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58103329674278861611414721 43577497255709146208561041)
        ·
          refine ⟨32683122941781859656420781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43577497255709146208561041 32683122941781859656420781)
          ·
            refine ⟨12256171103168197371157793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32683122941781859656420781 12256171103168197371157793)
            ·
              refine ⟨9192128327376148028368345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12256171103168197371157793 9192128327376148028368345)
              ·
                refine ⟨6894096245532111021276259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9192128327376148028368345 6894096245532111021276259)
                ·
                  refine ⟨10341144368298166531914389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6894096245532111021276259 10341144368298166531914389)
                  ·
                    refine ⟨484741142263976556183487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10341144368298166531914389 484741142263976556183487)
                    ·
                      rfl

theorem cell23_2832090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_2832090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832090 prefixEnd_2832090 := by exact prefixLift 2832090
  have htrace : WordTrace (prefixWord ++ tailWord_2832090) baseStart_2832090 baseEnd_2832090 := by
    simpa [prefixWord, tailWord_2832090, baseEnd_2832090] using wordTrace_append hprefix tailTrace_2832090
  have hstable : (prefixWord ++ tailWord_2832090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832090).length < 2 ^ (prefixWord ++ tailWord_2832090).sum := by decide
  have hdescent : baseEnd_2832090 < baseStart_2832090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832100 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_2832100 : Nat := 118140960795 + 2832100 * 2 ^ 59
def prefixEnd_2832100 : Nat := 4983230072969 + 3 ^ 40 * 2832100 * 2
def baseEnd_2832100 : Nat := 1454228561598474629425415

theorem tailTrace_2832100 : CollatzResearch.WordTrace tailWord_2832100 prefixEnd_2832100 1454228561598474629425415 := by
  unfold tailWord_2832100
  simp only [CollatzResearch.WordTrace]
  refine ⟨51647586519896429508522877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68863448693195239344697169 51647586519896429508522877)
  ·
    refine ⟨19367844944961161065696079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51647586519896429508522877 19367844944961161065696079)
    ·
      refine ⟨29051767417441741598544119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19367844944961161065696079 29051767417441741598544119)
      ·
        refine ⟨43577651126162612397816179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29051767417441741598544119 43577651126162612397816179)
        ·
          refine ⟨65366476689243918596724269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43577651126162612397816179 65366476689243918596724269)
          ·
            refine ⟨24512428758466469473771601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65366476689243918596724269 24512428758466469473771601)
            ·
              refine ⟨18384321568849852105328701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24512428758466469473771601 18384321568849852105328701)
              ·
                refine ⟨6894120588318694539498263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18384321568849852105328701 6894120588318694539498263)
                ·
                  refine ⟨10341180882478041809247395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6894120588318694539498263 10341180882478041809247395)
                  ·
                    refine ⟨15511771323717062713871093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10341180882478041809247395 15511771323717062713871093)
                    ·
                      refine ⟨1454228561598474629425415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15511771323717062713871093 1454228561598474629425415)
                      ·
                        rfl

theorem cell23_2832100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_2832100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832100 prefixEnd_2832100 := by exact prefixLift 2832100
  have htrace : WordTrace (prefixWord ++ tailWord_2832100) baseStart_2832100 baseEnd_2832100 := by
    simpa [prefixWord, tailWord_2832100, baseEnd_2832100] using wordTrace_append hprefix tailTrace_2832100
  have hstable : (prefixWord ++ tailWord_2832100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832100).length < 2 ^ (prefixWord ++ tailWord_2832100).sum := by decide
  have hdescent : baseEnd_2832100 < baseStart_2832100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832107 : List Nat := [1, 1, 1, 1, 2, 4, 5, 2, 2, 4]
def baseStart_2832107 : Nat := 118140960795 + 2832107 * 2 ^ 59
def prefixEnd_2832107 : Nat := 4983230072969 + 3 ^ 40 * 2832107 * 2
def baseEnd_2832107 : Nat := 484744051987685367345961

theorem tailTrace_2832107 : CollatzResearch.WordTrace tailWord_2832107 prefixEnd_2832107 484744051987685367345961 := by
  unfold tailWord_2832107
  simp only [CollatzResearch.WordTrace]
  refine ⟨103295428350767499212550575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68863618900511666141700383 103295428350767499212550575)
  ·
    refine ⟨154943142526151248818825863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103295428350767499212550575 154943142526151248818825863)
    ·
      refine ⟨232414713789226873228238795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154943142526151248818825863 232414713789226873228238795)
      ·
        refine ⟨348622070683840309842358193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232414713789226873228238795 348622070683840309842358193)
        ·
          refine ⟨261466553012880232381768645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348622070683840309842358193 261466553012880232381768645)
          ·
            refine ⟨49024978689915043571581621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 261466553012880232381768645 49024978689915043571581621)
            ·
              refine ⟨4596091752179535334835777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49024978689915043571581621 4596091752179535334835777)
              ·
                refine ⟨3447068814134651501126833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4596091752179535334835777 3447068814134651501126833)
                ·
                  refine ⟨2585301610600988625845125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3447068814134651501126833 2585301610600988625845125)
                  ·
                    refine ⟨484744051987685367345961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2585301610600988625845125 484744051987685367345961)
                    ·
                      rfl

theorem cell23_2832107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 4].length) (baseStart_2832107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832107 prefixEnd_2832107 := by exact prefixLift 2832107
  have htrace : WordTrace (prefixWord ++ tailWord_2832107) baseStart_2832107 baseEnd_2832107 := by
    simpa [prefixWord, tailWord_2832107, baseEnd_2832107] using wordTrace_append hprefix tailTrace_2832107
  have hstable : (prefixWord ++ tailWord_2832107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832107).length < 2 ^ (prefixWord ++ tailWord_2832107).sum := by decide
  have hdescent : baseEnd_2832107 < baseStart_2832107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832110 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_2832110 : Nat := 118140960795 + 2832110 * 2 ^ 59
def prefixEnd_2832110 : Nat := 4983230072969 + 3 ^ 40 * 2832110 * 2
def baseEnd_2832110 : Nat := 1454233696405019590300369

theorem tailTrace_2832110 : CollatzResearch.WordTrace tailWord_2832110 prefixEnd_2832110 1454233696405019590300369 := by
  unfold tailWord_2832110
  simp only [CollatzResearch.WordTrace]
  refine ⟨12911942221219578840613723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68863691846504420483273189 12911942221219578840613723)
  ·
    refine ⟨19367913331829368260920585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12911942221219578840613723 19367913331829368260920585)
    ·
      refine ⟨14525934998872026195690439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19367913331829368260920585 14525934998872026195690439)
      ·
        refine ⟨21788902498308039293535659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14525934998872026195690439 21788902498308039293535659)
        ·
          refine ⟨32683353747462058940303489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21788902498308039293535659 32683353747462058940303489)
          ·
            refine ⟨24512515310596544205227617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32683353747462058940303489 24512515310596544205227617)
            ·
              refine ⟨18384386482947408153920713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24512515310596544205227617 18384386482947408153920713)
              ·
                refine ⟨13788289862210556115440535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18384386482947408153920713 13788289862210556115440535)
                ·
                  refine ⟨20682434793315834173160803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13788289862210556115440535 20682434793315834173160803)
                  ·
                    refine ⟨31023652189973751259741205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20682434793315834173160803 31023652189973751259741205)
                    ·
                      refine ⟨1454233696405019590300369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31023652189973751259741205 1454233696405019590300369)
                      ·
                        rfl

theorem cell23_2832110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_2832110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832110 prefixEnd_2832110 := by exact prefixLift 2832110
  have htrace : WordTrace (prefixWord ++ tailWord_2832110) baseStart_2832110 baseEnd_2832110 := by
    simpa [prefixWord, tailWord_2832110, baseEnd_2832110] using wordTrace_append hprefix tailTrace_2832110
  have hstable : (prefixWord ++ tailWord_2832110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832110).length < 2 ^ (prefixWord ++ tailWord_2832110).sum := by decide
  have hdescent : baseEnd_2832110 < baseStart_2832110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832123 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 6]
def baseStart_2832123 : Nat := 118140960795 + 2832123 * 2 ^ 59
def prefixEnd_2832123 : Nat := 4983230072969 + 3 ^ 40 * 2832123 * 2
def baseEnd_2832123 : Nat := 1454240371653528039437809

theorem tailTrace_2832123 : CollatzResearch.WordTrace tailWord_2832123 prefixEnd_2832123 1454240371653528039437809 := by
  unfold tailWord_2832123
  simp only [CollatzResearch.WordTrace]
  refine ⟨103296011918709533945133023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68864007945806355963422015 103296011918709533945133023)
  ·
    refine ⟨154944017878064300917699535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103296011918709533945133023 154944017878064300917699535)
    ·
      refine ⟨232416026817096451376549303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154944017878064300917699535 232416026817096451376549303)
      ·
        refine ⟨348624040225644677064823955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232416026817096451376549303 348624040225644677064823955)
        ·
          refine ⟨522936060338467015597235933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348624040225644677064823955 522936060338467015597235933)
          ·
            refine ⟨196101022626925130848963475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 522936060338467015597235933 196101022626925130848963475)
            ·
              refine ⟨294151533940387696273445213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196101022626925130848963475 294151533940387696273445213)
              ·
                refine ⟨110306825227645386102541955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294151533940387696273445213 110306825227645386102541955)
                ·
                  refine ⟨165460237841468079153812933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110306825227645386102541955 165460237841468079153812933)
                  ·
                    refine ⟨31023794595275264841339925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 165460237841468079153812933 31023794595275264841339925)
                    ·
                      refine ⟨1454240371653528039437809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31023794595275264841339925 1454240371653528039437809)
                      ·
                        rfl

theorem cell23_2832123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 6].length) (baseStart_2832123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832123 prefixEnd_2832123 := by exact prefixLift 2832123
  have htrace : WordTrace (prefixWord ++ tailWord_2832123) baseStart_2832123 baseEnd_2832123 := by
    simpa [prefixWord, tailWord_2832123, baseEnd_2832123] using wordTrace_append hprefix tailTrace_2832123
  have hstable : (prefixWord ++ tailWord_2832123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832123).length < 2 ^ (prefixWord ++ tailWord_2832123).sum := by decide
  have hdescent : baseEnd_2832123 < baseStart_2832123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832124 : List Nat := [2, 2, 2, 1, 3, 1, 5, 1, 2, 4]
def baseStart_2832124 : Nat := 118140960795 + 2832124 * 2 ^ 59
def prefixEnd_2832124 : Nat := 4983230072969 + 3 ^ 40 * 2832124 * 2
def baseEnd_2832124 : Nat := 484746961711394178508435

theorem tailTrace_2832124 : CollatzResearch.WordTrace tailWord_2832124 prefixEnd_2832124 484746961711394178508435 := by
  unfold tailWord_2832124
  simp only [CollatzResearch.WordTrace]
  refine ⟨51648024195852955557959713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68864032261137274077279617 51648024195852955557959713)
  ·
    refine ⟨38736018146889716668469785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51648024195852955557959713 38736018146889716668469785)
    ·
      refine ⟨29052013610167287501352339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38736018146889716668469785 29052013610167287501352339)
      ·
        refine ⟨43578020415250931252028509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29052013610167287501352339 43578020415250931252028509)
        ·
          refine ⟨16341757655719099219510691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43578020415250931252028509 16341757655719099219510691)
          ·
            refine ⟨24512636483578648829266037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16341757655719099219510691 24512636483578648829266037)
            ·
              refine ⟨2298059670335498327743691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24512636483578648829266037 2298059670335498327743691)
              ·
                refine ⟨3447089505503247491615537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298059670335498327743691 3447089505503247491615537)
                ·
                  refine ⟨2585317129127435618711653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3447089505503247491615537 2585317129127435618711653)
                  ·
                    refine ⟨484746961711394178508435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2585317129127435618711653 484746961711394178508435)
                    ·
                      rfl

theorem cell23_2832124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_2832124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832124 prefixEnd_2832124 := by exact prefixLift 2832124
  have htrace : WordTrace (prefixWord ++ tailWord_2832124) baseStart_2832124 baseEnd_2832124 := by
    simpa [prefixWord, tailWord_2832124, baseEnd_2832124] using wordTrace_append hprefix tailTrace_2832124
  have hstable : (prefixWord ++ tailWord_2832124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832124).length < 2 ^ (prefixWord ++ tailWord_2832124).sum := by decide
  have hdescent : baseEnd_2832124 < baseStart_2832124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832160 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2832160 : Nat := 118140960795 + 2832160 * 2 ^ 59
def prefixEnd_2832160 : Nat := 4983230072969 + 3 ^ 40 * 2832160 * 2
def baseEnd_2832160 : Nat := 1454259370437744394675139

theorem tailTrace_2832160 : CollatzResearch.WordTrace tailWord_2832160 prefixEnd_2832160 1454259370437744394675139 := by
  unfold tailWord_2832160
  simp only [CollatzResearch.WordTrace]
  refine ⟨51648680709787744632114967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68864907613050326176153289 51648680709787744632114967)
  ·
    refine ⟨77473021064681616948172451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51648680709787744632114967 77473021064681616948172451)
    ·
      refine ⟨116209531597022425422258677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77473021064681616948172451 116209531597022425422258677)
      ·
        refine ⟨10894643587220852383336751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116209531597022425422258677 10894643587220852383336751)
        ·
          refine ⟨16341965380831278575005127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10894643587220852383336751 16341965380831278575005127)
          ·
            refine ⟨24512948071246917862507691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16341965380831278575005127 24512948071246917862507691)
            ·
              refine ⟨36769422106870376793761537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24512948071246917862507691 36769422106870376793761537)
              ·
                refine ⟨27577066580152782595321153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36769422106870376793761537 27577066580152782595321153)
                ·
                  refine ⟨20682799935114586946490865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27577066580152782595321153 20682799935114586946490865)
                  ·
                    refine ⟨15512099951335940209868149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20682799935114586946490865 15512099951335940209868149)
                    ·
                      refine ⟨1454259370437744394675139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15512099951335940209868149 1454259370437744394675139)
                      ·
                        rfl

theorem cell23_2832160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2832160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832160 prefixEnd_2832160 := by exact prefixLift 2832160
  have htrace : WordTrace (prefixWord ++ tailWord_2832160) baseStart_2832160 baseEnd_2832160 := by
    simpa [prefixWord, tailWord_2832160, baseEnd_2832160] using wordTrace_append hprefix tailTrace_2832160
  have hstable : (prefixWord ++ tailWord_2832160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832160).length < 2 ^ (prefixWord ++ tailWord_2832160).sum := by decide
  have hdescent : baseEnd_2832160 < baseStart_2832160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832164 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 4, 1, 3]
def baseStart_2832164 : Nat := 118140960795 + 2832164 * 2 ^ 59
def prefixEnd_2832164 : Nat := 4983230072969 + 3 ^ 40 * 2832164 * 2
def baseEnd_2832164 : Nat := 1454261424360362379025121

theorem tailTrace_2832164 : CollatzResearch.WordTrace tailWord_2832164 prefixEnd_2832164 1454261424360362379025121 := by
  unfold tailWord_2832164
  simp only [CollatzResearch.WordTrace]
  refine ⟨51648753655780498973687773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68865004874373998631583697 51648753655780498973687773)
  ·
    refine ⟨19368282620917687115132915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51648753655780498973687773 19368282620917687115132915)
    ·
      refine ⟨29052423931376530672699373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19368282620917687115132915 29052423931376530672699373)
      ·
        refine ⟨10894658974266199002262265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29052423931376530672699373 10894658974266199002262265)
        ·
          refine ⟨8170994230699649251696699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10894658974266199002262265 8170994230699649251696699)
          ·
            refine ⟨12256491346049473877545049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8170994230699649251696699 12256491346049473877545049)
            ·
              refine ⟨9192368509537105408158787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12256491346049473877545049 9192368509537105408158787)
              ·
                refine ⟨13788552764305658112238181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9192368509537105408158787 13788552764305658112238181)
                ·
                  refine ⟨2585353643307310896044659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13788552764305658112238181 2585353643307310896044659)
                  ·
                    refine ⟨3878030464960966344066989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2585353643307310896044659 3878030464960966344066989)
                    ·
                      refine ⟨1454261424360362379025121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3878030464960966344066989 1454261424360362379025121)
                      ·
                        rfl

theorem cell23_2832164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_2832164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832164 prefixEnd_2832164 := by exact prefixLift 2832164
  have htrace : WordTrace (prefixWord ++ tailWord_2832164) baseStart_2832164 baseEnd_2832164 := by
    simpa [prefixWord, tailWord_2832164, baseEnd_2832164] using wordTrace_append hprefix tailTrace_2832164
  have hstable : (prefixWord ++ tailWord_2832164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832164).length < 2 ^ (prefixWord ++ tailWord_2832164).sum := by decide
  have hdescent : baseEnd_2832164 < baseStart_2832164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832181 : List Nat := [1, 3, 3, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_2832181 : Nat := 118140960795 + 2832181 * 2 ^ 59
def prefixEnd_2832181 : Nat := 4983230072969 + 3 ^ 40 * 2832181 * 2
def baseEnd_2832181 : Nat := 1454270153531488812512543

theorem tailTrace_2832181 : CollatzResearch.WordTrace tailWord_2832181 prefixEnd_2832181 1454270153531488812512543 := by
  unfold tailWord_2832181
  simp only [CollatzResearch.WordTrace]
  refine ⟨103298127352499409850744397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68865418234999606567162931 103298127352499409850744397)
  ·
    refine ⟨38736797757187278694029149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103298127352499409850744397 38736797757187278694029149)
    ·
      refine ⟨14526299158945229510260931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38736797757187278694029149 14526299158945229510260931)
      ·
        refine ⟨21789448738417844265391397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14526299158945229510260931 21789448738417844265391397)
        ·
          refine ⟨4085521638453345799760887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21789448738417844265391397 4085521638453345799760887)
          ·
            refine ⟨6128282457680018699641331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4085521638453345799760887 6128282457680018699641331)
            ·
              refine ⟨9192423686520028049461997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6128282457680018699641331 9192423686520028049461997)
              ·
                refine ⟨3447158882445010518548249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9192423686520028049461997 3447158882445010518548249)
                ·
                  refine ⟨2585369161833757888911187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3447158882445010518548249 2585369161833757888911187)
                  ·
                    refine ⟨3878053742750636833366781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2585369161833757888911187 3878053742750636833366781)
                    ·
                      refine ⟨1454270153531488812512543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3878053742750636833366781 1454270153531488812512543)
                      ·
                        rfl

theorem cell23_2832181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_2832181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832181 prefixEnd_2832181 := by exact prefixLift 2832181
  have htrace : WordTrace (prefixWord ++ tailWord_2832181) baseStart_2832181 baseEnd_2832181 := by
    simpa [prefixWord, tailWord_2832181, baseEnd_2832181] using wordTrace_append hprefix tailTrace_2832181
  have hstable : (prefixWord ++ tailWord_2832181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832181).length < 2 ^ (prefixWord ++ tailWord_2832181).sum := by decide
  have hdescent : baseEnd_2832181 < baseStart_2832181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832237 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_2832237 : Nat := 118140960795 + 2832237 * 2 ^ 59
def prefixEnd_2832237 : Nat := 4983230072969 + 3 ^ 40 * 2832237 * 2
def baseEnd_2832237 : Nat := 1454298908448140593412285

theorem tailTrace_2832237 : CollatzResearch.WordTrace tailWord_2832237 prefixEnd_2832237 1454298908448140593412285 := by
  unfold tailWord_2832237
  simp only [CollatzResearch.WordTrace]
  refine ⟨103300169840296531414782965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68866779893531020943188643 103300169840296531414782965)
  ·
    refine ⟨9684390922527799820135903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103300169840296531414782965 9684390922527799820135903)
    ·
      refine ⟨14526586383791699730203855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9684390922527799820135903 14526586383791699730203855)
      ·
        refine ⟨21789879575687549595305783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14526586383791699730203855 21789879575687549595305783)
        ·
          refine ⟨32684819363531324392958675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21789879575687549595305783 32684819363531324392958675)
          ·
            refine ⟨49027229045296986589438013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32684819363531324392958675 49027229045296986589438013)
            ·
              refine ⟨18385210891986369971039255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49027229045296986589438013 18385210891986369971039255)
              ·
                refine ⟨27577816337979554956558883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18385210891986369971039255 27577816337979554956558883)
                ·
                  refine ⟨41366724506969332434838325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27577816337979554956558883 41366724506969332434838325)
                  ·
                    refine ⟨3878130422528374915766093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41366724506969332434838325 3878130422528374915766093)
                    ·
                      refine ⟨1454298908448140593412285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3878130422528374915766093 1454298908448140593412285)
                      ·
                        rfl

theorem cell23_2832237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_2832237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832237 prefixEnd_2832237 := by exact prefixLift 2832237
  have htrace : WordTrace (prefixWord ++ tailWord_2832237) baseStart_2832237 baseEnd_2832237 := by
    simpa [prefixWord, tailWord_2832237, baseEnd_2832237] using wordTrace_append hprefix tailTrace_2832237
  have hstable : (prefixWord ++ tailWord_2832237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832237).length < 2 ^ (prefixWord ++ tailWord_2832237).sum := by decide
  have hdescent : baseEnd_2832237 < baseStart_2832237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832238 : List Nat := [4, 1, 2, 3, 1, 1, 2, 3, 2, 2, 2]
def baseStart_2832238 : Nat := 118140960795 + 2832238 * 2 ^ 59
def prefixEnd_2832238 : Nat := 4983230072969 + 3 ^ 40 * 2832238 * 2
def baseEnd_2832238 : Nat := 1454299421928795089499781

theorem tailTrace_2832238 : CollatzResearch.WordTrace tailWord_2832238 prefixEnd_2832238 1454299421928795089499781 := by
  unfold tailWord_2832238
  simp only [CollatzResearch.WordTrace]
  refine ⟨12912525789161613573196171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68866804208861939057046245 12912525789161613573196171)
  ·
    refine ⟨19368788683742420359794257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12912525789161613573196171 19368788683742420359794257)
    ·
      refine ⟨14526591512806815269845693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19368788683742420359794257 14526591512806815269845693)
      ·
        refine ⟨5447471817302555726192135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14526591512806815269845693 5447471817302555726192135)
        ·
          refine ⟨8171207725953833589288203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5447471817302555726192135 8171207725953833589288203)
          ·
            refine ⟨12256811588930750383932305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8171207725953833589288203 12256811588930750383932305)
            ·
              refine ⟨9192608691698062787949229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12256811588930750383932305 9192608691698062787949229)
              ·
                refine ⟨3447228259386773545480961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9192608691698062787949229 3447228259386773545480961)
                ·
                  refine ⟨2585421194540080159110721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3447228259386773545480961 2585421194540080159110721)
                  ·
                    refine ⟨1939065895905060119333041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2585421194540080159110721 1939065895905060119333041)
                    ·
                      refine ⟨1454299421928795089499781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1939065895905060119333041 1454299421928795089499781)
                      ·
                        rfl

theorem cell23_2832238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_2832238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832238 prefixEnd_2832238 := by exact prefixLift 2832238
  have htrace : WordTrace (prefixWord ++ tailWord_2832238) baseStart_2832238 baseEnd_2832238 := by
    simpa [prefixWord, tailWord_2832238, baseEnd_2832238] using wordTrace_append hprefix tailTrace_2832238
  have hstable : (prefixWord ++ tailWord_2832238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832238).length < 2 ^ (prefixWord ++ tailWord_2832238).sum := by decide
  have hdescent : baseEnd_2832238 < baseStart_2832238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832240 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 1, 7]
def baseStart_2832240 : Nat := 118140960795 + 2832240 * 2 ^ 59
def prefixEnd_2832240 : Nat := 4983230072969 + 3 ^ 40 * 2832240 * 2
def baseEnd_2832240 : Nat := 484766816296701360558257

theorem tailTrace_2832240 : CollatzResearch.WordTrace tailWord_2832240 prefixEnd_2832240 484766816296701360558257 := by
  unfold tailWord_2832240
  simp only [CollatzResearch.WordTrace]
  refine ⟨51650139629642831463571087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68866852839523775284761449 51650139629642831463571087)
  ·
    refine ⟨77475209444464247195356631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51650139629642831463571087 77475209444464247195356631)
    ·
      refine ⟨116212814166696370793034947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77475209444464247195356631 116212814166696370793034947)
      ·
        refine ⟨174319221250044556189552421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116212814166696370793034947 174319221250044556189552421)
        ·
          refine ⟨32684853984383354285541079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174319221250044556189552421 32684853984383354285541079)
          ·
            refine ⟨49027280976575031428311619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32684853984383354285541079 49027280976575031428311619)
            ·
              refine ⟨73540921464862547142467429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49027280976575031428311619 73540921464862547142467429)
              ·
                refine ⟨13788922774661727589212643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73540921464862547142467429 13788922774661727589212643)
                ·
                  refine ⟨20683384161992591383818965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13788922774661727589212643 20683384161992591383818965)
                  ·
                    refine ⟨484766816296701360558257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20683384161992591383818965 484766816296701360558257)
                    ·
                      rfl

theorem cell23_2832240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 1, 7].length) (baseStart_2832240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832240 prefixEnd_2832240 := by exact prefixLift 2832240
  have htrace : WordTrace (prefixWord ++ tailWord_2832240) baseStart_2832240 baseEnd_2832240 := by
    simpa [prefixWord, tailWord_2832240, baseEnd_2832240] using wordTrace_append hprefix tailTrace_2832240
  have hstable : (prefixWord ++ tailWord_2832240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832240).length < 2 ^ (prefixWord ++ tailWord_2832240).sum := by decide
  have hdescent : baseEnd_2832240 < baseStart_2832240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832250 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7]
def baseStart_2832250 : Nat := 118140960795 + 2832250 * 2 ^ 59
def prefixEnd_2832250 : Nat := 4983230072969 + 3 ^ 40 * 2832250 * 2
def baseEnd_2832250 : Nat := 1454305583696649042549725

theorem tailTrace_2832250 : CollatzResearch.WordTrace tailWord_2832250 prefixEnd_2832250 1454305583696649042549725 := by
  unfold tailWord_2832250
  simp only [CollatzResearch.WordTrace]
  refine ⟨25825160997312358658751551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68867095992832956423337469 25825160997312358658751551)
  ·
    refine ⟨38737741495968537988127327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25825160997312358658751551 38737741495968537988127327)
    ·
      refine ⟨58106612243952806982190991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38737741495968537988127327 58106612243952806982190991)
      ·
        refine ⟨87159918365929210473286487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58106612243952806982190991 87159918365929210473286487)
        ·
          refine ⟨130739877548893815709929731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87159918365929210473286487 130739877548893815709929731)
          ·
            refine ⟨196109816323340723564894597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130739877548893815709929731 196109816323340723564894597)
            ·
              refine ⟨36770590560626385668417737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196109816323340723564894597 36770590560626385668417737)
              ·
                refine ⟨27577942920469789251313303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36770590560626385668417737 27577942920469789251313303)
                ·
                  refine ⟨41366914380704683876969955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27577942920469789251313303 41366914380704683876969955)
                  ·
                    refine ⟨62050371571057025815454933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41366914380704683876969955 62050371571057025815454933)
                    ·
                      refine ⟨1454305583696649042549725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62050371571057025815454933 1454305583696649042549725)
                      ·
                        rfl

theorem cell23_2832250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_2832250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832250 prefixEnd_2832250 := by exact prefixLift 2832250
  have htrace : WordTrace (prefixWord ++ tailWord_2832250) baseStart_2832250 baseEnd_2832250 := by
    simpa [prefixWord, tailWord_2832250, baseEnd_2832250] using wordTrace_append hprefix tailTrace_2832250
  have hstable : (prefixWord ++ tailWord_2832250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832250).length < 2 ^ (prefixWord ++ tailWord_2832250).sum := by decide
  have hdescent : baseEnd_2832250 < baseStart_2832250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832277 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_2832277 : Nat := 118140960795 + 2832277 * 2 ^ 59
def prefixEnd_2832277 : Nat := 4983230072969 + 3 ^ 40 * 2832277 * 2
def baseEnd_2832277 : Nat := 1454319447674320436912101

theorem tailTrace_2832277 : CollatzResearch.WordTrace tailWord_2832277 prefixEnd_2832277 1454319447674320436912101 := by
  unfold tailWord_2832277
  simp only [CollatzResearch.WordTrace]
  refine ⟨103301628760151618246239085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68867752506767745497492723 103301628760151618246239085)
  ·
    refine ⟨38738110785056856842339657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103301628760151618246239085 38738110785056856842339657)
    ·
      refine ⟨29053583088792642631754743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38738110785056856842339657 29053583088792642631754743)
      ·
        refine ⟨43580374633188963947632115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29053583088792642631754743 43580374633188963947632115)
        ·
          refine ⟨65370561949783445921448173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43580374633188963947632115 65370561949783445921448173)
          ·
            refine ⟨24513960731168792220543065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65370561949783445921448173 24513960731168792220543065)
            ·
              refine ⟨18385470548376594165407299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24513960731168792220543065 18385470548376594165407299)
              ·
                refine ⟨27578205822564891248110949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18385470548376594165407299 27578205822564891248110949)
                ·
                  refine ⟨5170913591730917109020803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27578205822564891248110949 5170913591730917109020803)
                  ·
                    refine ⟨7756370387596375663531205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5170913591730917109020803 7756370387596375663531205)
                    ·
                      refine ⟨1454319447674320436912101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7756370387596375663531205 1454319447674320436912101)
                      ·
                        rfl

theorem cell23_2832277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_2832277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832277 prefixEnd_2832277 := by exact prefixLift 2832277
  have htrace : WordTrace (prefixWord ++ tailWord_2832277) baseStart_2832277 baseEnd_2832277 := by
    simpa [prefixWord, tailWord_2832277, baseEnd_2832277] using wordTrace_append hprefix tailTrace_2832277
  have hstable : (prefixWord ++ tailWord_2832277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832277).length < 2 ^ (prefixWord ++ tailWord_2832277).sum := by decide
  have hdescent : baseEnd_2832277 < baseStart_2832277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832278 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 7]
def baseStart_2832278 : Nat := 118140960795 + 2832278 * 2 ^ 59
def prefixEnd_2832278 : Nat := 4983230072969 + 3 ^ 40 * 2832278 * 2
def baseEnd_2832278 : Nat := 161591106794997214777733

theorem tailTrace_2832278 : CollatzResearch.WordTrace tailWord_2832278 prefixEnd_2832278 161591106794997214777733 := by
  unfold tailWord_2832278
  simp only [CollatzResearch.WordTrace]
  refine ⟨6456354077071749713564093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68867776822098663611350325 6456354077071749713564093)
  ·
    refine ⟨2421132778901906142586535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6456354077071749713564093 2421132778901906142586535)
    ·
      refine ⟨3631699168352859213879803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2421132778901906142586535 3631699168352859213879803)
      ·
        refine ⟨5447548752529288820819705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3631699168352859213879803 5447548752529288820819705)
        ·
          refine ⟨4085661564396966615614779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5447548752529288820819705 4085661564396966615614779)
          ·
            refine ⟨6128492346595449923422169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4085661564396966615614779 6128492346595449923422169)
            ·
              refine ⟨4596369259946587442566627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6128492346595449923422169 4596369259946587442566627)
              ·
                refine ⟨6894553889919881163849941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4596369259946587442566627 6894553889919881163849941)
                ·
                  refine ⟨161591106794997214777733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6894553889919881163849941 161591106794997214777733)
                  ·
                    rfl

theorem cell23_2832278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_2832278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832278 prefixEnd_2832278 := by exact prefixLift 2832278
  have htrace : WordTrace (prefixWord ++ tailWord_2832278) baseStart_2832278 baseEnd_2832278 := by
    simpa [prefixWord, tailWord_2832278, baseEnd_2832278] using wordTrace_append hprefix tailTrace_2832278
  have hstable : (prefixWord ++ tailWord_2832278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832278).length < 2 ^ (prefixWord ++ tailWord_2832278).sum := by decide
  have hdescent : baseEnd_2832278 < baseStart_2832278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832297 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 6, 2, 3]
def baseStart_2832297 : Nat := 118140960795 + 2832297 * 2 ^ 59
def prefixEnd_2832297 : Nat := 4983230072969 + 3 ^ 40 * 2832297 * 2
def baseEnd_2832297 : Nat := 1454329717287410358662009

theorem tailTrace_2832297 : CollatzResearch.WordTrace tailWord_2832297 prefixEnd_2832297 1454329717287410358662009 := by
  unfold tailWord_2832297
  simp only [CollatzResearch.WordTrace]
  refine ⟨103302358220079161661967145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68868238813386107774644763 103302358220079161661967145)
  ·
    refine ⟨77476768665059371246475359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103302358220079161661967145 77476768665059371246475359)
    ·
      refine ⟨116215152997589056869713039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77476768665059371246475359 116215152997589056869713039)
      ·
        refine ⟨174322729496383585304569559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116215152997589056869713039 174322729496383585304569559)
        ·
          refine ⟨261484094244575377956854339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174322729496383585304569559 261484094244575377956854339)
          ·
            refine ⟨392226141366863066935281509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261484094244575377956854339 392226141366863066935281509)
            ·
              refine ⟨73542401506286825050365283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 392226141366863066935281509 73542401506286825050365283)
              ·
                refine ⟨110313602259430237575547925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73542401506286825050365283 110313602259430237575547925)
                ·
                  refine ⟨5170950105910792386353809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110313602259430237575547925 5170950105910792386353809)
                  ·
                    refine ⟨3878212579433094289765357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5170950105910792386353809 3878212579433094289765357)
                    ·
                      refine ⟨1454329717287410358662009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3878212579433094289765357 1454329717287410358662009)
                      ·
                        rfl

theorem cell23_2832297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 2, 3].length) (baseStart_2832297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832297 prefixEnd_2832297 := by exact prefixLift 2832297
  have htrace : WordTrace (prefixWord ++ tailWord_2832297) baseStart_2832297 baseEnd_2832297 := by
    simpa [prefixWord, tailWord_2832297, baseEnd_2832297] using wordTrace_append hprefix tailTrace_2832297
  have hstable : (prefixWord ++ tailWord_2832297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832297).length < 2 ^ (prefixWord ++ tailWord_2832297).sum := by decide
  have hdescent : baseEnd_2832297 < baseStart_2832297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832300 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 12]
def baseStart_2832300 : Nat := 118140960795 + 2832300 * 2 ^ 59
def prefixEnd_2832300 : Nat := 4983230072969 + 3 ^ 40 * 2832300 * 2
def baseEnd_2832300 : Nat := 161592361969930427436055

theorem tailTrace_2832300 : CollatzResearch.WordTrace tailWord_2832300 prefixEnd_2832300 161592361969930427436055 := by
  unfold tailWord_2832300
  simp only [CollatzResearch.WordTrace]
  refine ⟨51651233819534146587163177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68868311759378862116217569 51651233819534146587163177)
  ·
    refine ⟨38738425364650609940372383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51651233819534146587163177 38738425364650609940372383)
    ·
      refine ⟨58107638046975914910558575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38738425364650609940372383 58107638046975914910558575)
      ·
        refine ⟨87161457070463872365837863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58107638046975914910558575 87161457070463872365837863)
        ·
          refine ⟨130742185605695808548756795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87161457070463872365837863 130742185605695808548756795)
          ·
            refine ⟨196113278408543712823135193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130742185605695808548756795 196113278408543712823135193)
            ·
              refine ⟨147084958806407784617351395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196113278408543712823135193 147084958806407784617351395)
              ·
                refine ⟨220627438209611676926027093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147084958806407784617351395 220627438209611676926027093)
                ·
                  refine ⟨161592361969930427436055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 220627438209611676926027093 161592361969930427436055)
                  ·
                    rfl

theorem cell23_2832300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 12].length) (baseStart_2832300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832300 prefixEnd_2832300 := by exact prefixLift 2832300
  have htrace : WordTrace (prefixWord ++ tailWord_2832300) baseStart_2832300 baseEnd_2832300 := by
    simpa [prefixWord, tailWord_2832300, baseEnd_2832300] using wordTrace_append hprefix tailTrace_2832300
  have hstable : (prefixWord ++ tailWord_2832300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832300).length < 2 ^ (prefixWord ++ tailWord_2832300).sum := by decide
  have hdescent : baseEnd_2832300 < baseStart_2832300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832317 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 8]
def baseStart_2832317 : Nat := 118140960795 + 2832317 * 2 ^ 59
def prefixEnd_2832317 : Nat := 4983230072969 + 3 ^ 40 * 2832317 * 2
def baseEnd_2832317 : Nat := 161593331877833364490213

theorem tailTrace_2832317 : CollatzResearch.WordTrace tailWord_2832317 prefixEnd_2832317 161593331877833364490213 := by
  unfold tailWord_2832317
  simp only [CollatzResearch.WordTrace]
  refine ⟨103303087680006705077695205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68868725120004470051796803 103303087680006705077695205)
  ·
    refine ⟨19369328940001257202067851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103303087680006705077695205 19369328940001257202067851)
    ·
      refine ⟨29053993410001885803101777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19369328940001257202067851 29053993410001885803101777)
      ·
        refine ⟨21790495057501414352326333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29053993410001885803101777 21790495057501414352326333)
        ·
          refine ⟨8171435646563030382122375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21790495057501414352326333 8171435646563030382122375)
          ·
            refine ⟨12257153469844545573183563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8171435646563030382122375 12257153469844545573183563)
            ·
              refine ⟨18385730204766818359775345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12257153469844545573183563 18385730204766818359775345)
              ·
                refine ⟨13789297653575113769831509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18385730204766818359775345 13789297653575113769831509)
                ·
                  refine ⟨161593331877833364490213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13789297653575113769831509 161593331877833364490213)
                  ·
                    rfl

theorem cell23_2832317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_2832317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832317 prefixEnd_2832317 := by exact prefixLift 2832317
  have htrace : WordTrace (prefixWord ++ tailWord_2832317) baseStart_2832317 baseEnd_2832317 := by
    simpa [prefixWord, tailWord_2832317, baseEnd_2832317] using wordTrace_append hprefix tailTrace_2832317
  have hstable : (prefixWord ++ tailWord_2832317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832317).length < 2 ^ (prefixWord ++ tailWord_2832317).sum := by decide
  have hdescent : baseEnd_2832317 < baseStart_2832317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832338 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 3, 4]
def baseStart_2832338 : Nat := 118140960795 + 2832338 * 2 ^ 59
def prefixEnd_2832338 : Nat := 4983230072969 + 3 ^ 40 * 2832338 * 2
def baseEnd_2832338 : Nat := 484783589998081566083107

theorem tailTrace_2832338 : CollatzResearch.WordTrace tailWord_2832338 prefixEnd_2832338 484783589998081566083107 := by
  unfold tailWord_2832338
  simp only [CollatzResearch.WordTrace]
  refine ⟨25825963403232656416052417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68869235741953750442806445 25825963403232656416052417)
  ·
    refine ⟨19369472552424492312039313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25825963403232656416052417 19369472552424492312039313)
    ·
      refine ⟨14527104414318369234029485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19369472552424492312039313 14527104414318369234029485)
      ·
        refine ⟨5447664155369388462761057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14527104414318369234029485 5447664155369388462761057)
        ·
          refine ⟨4085748116527041347070793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5447664155369388462761057 4085748116527041347070793)
          ·
            refine ⟨3064311087395281010303095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4085748116527041347070793 3064311087395281010303095)
            ·
              refine ⟨4596466631092921515454643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3064311087395281010303095 4596466631092921515454643)
              ·
                refine ⟨6894699946639382273181965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4596466631092921515454643 6894699946639382273181965)
                ·
                  refine ⟨2585512479989768352443237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6894699946639382273181965 2585512479989768352443237)
                  ·
                    refine ⟨484783589998081566083107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2585512479989768352443237 484783589998081566083107)
                    ·
                      rfl

theorem cell23_2832338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_2832338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832338 prefixEnd_2832338 := by exact prefixLift 2832338
  have htrace : WordTrace (prefixWord ++ tailWord_2832338) baseStart_2832338 baseEnd_2832338 := by
    simpa [prefixWord, tailWord_2832338, baseEnd_2832338] using wordTrace_append hprefix tailTrace_2832338
  have hstable : (prefixWord ++ tailWord_2832338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832338).length < 2 ^ (prefixWord ++ tailWord_2832338).sum := by decide
  have hdescent : baseEnd_2832338 < baseStart_2832338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832351 : List Nat := [1, 1, 2, 3, 4, 3, 2, 1, 6]
def baseStart_2832351 : Nat := 118140960795 + 2832351 * 2 ^ 59
def prefixEnd_2832351 : Nat := 4983230072969 + 3 ^ 40 * 2832351 * 2
def baseEnd_2832351 : Nat := 161595271693639238598529

theorem tailTrace_2832351 : CollatzResearch.WordTrace tailWord_2832351 prefixEnd_2832351 161595271693639238598529 := by
  unfold tailWord_2832351
  simp only [CollatzResearch.WordTrace]
  refine ⟨103304327761883528884432907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68869551841255685922955271 103304327761883528884432907)
  ·
    refine ⟨154956491642825293326649361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103304327761883528884432907 154956491642825293326649361)
    ·
      refine ⟨116217368732118969994987021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154956491642825293326649361 116217368732118969994987021)
      ·
        refine ⟨43581513274544613748120133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116217368732118969994987021 43581513274544613748120133)
        ·
          refine ⟨8171533738977115077772525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43581513274544613748120133 8171533738977115077772525)
          ·
            refine ⟨3064325152116418154164697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8171533738977115077772525 3064325152116418154164697)
            ·
              refine ⟨2298243864087313615623523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3064325152116418154164697 2298243864087313615623523)
              ·
                refine ⟨3447365796130970423435285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298243864087313615623523 3447365796130970423435285)
                ·
                  refine ⟨161595271693639238598529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3447365796130970423435285 161595271693639238598529)
                  ·
                    rfl

theorem cell23_2832351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 6].length) (baseStart_2832351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832351 prefixEnd_2832351 := by exact prefixLift 2832351
  have htrace : WordTrace (prefixWord ++ tailWord_2832351) baseStart_2832351 baseEnd_2832351 := by
    simpa [prefixWord, tailWord_2832351, baseEnd_2832351] using wordTrace_append hprefix tailTrace_2832351
  have hstable : (prefixWord ++ tailWord_2832351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832351).length < 2 ^ (prefixWord ++ tailWord_2832351).sum := by decide
  have hdescent : baseEnd_2832351 < baseStart_2832351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832377 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 3, 6]
def baseStart_2832377 : Nat := 118140960795 + 2832377 * 2 ^ 59
def prefixEnd_2832377 : Nat := 4983230072969 + 3 ^ 40 * 2832377 * 2
def baseEnd_2832377 : Nat := 484790265246590015220547

theorem tailTrace_2832377 : CollatzResearch.WordTrace tailWord_2832377 prefixEnd_2832377 484790265246590015220547 := by
  unfold tailWord_2832377
  simp only [CollatzResearch.WordTrace]
  refine ⟨103305276059789335324879385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68870184039859556883252923 103305276059789335324879385)
  ·
    refine ⟨77478957044842001493659539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103305276059789335324879385 77478957044842001493659539)
    ·
      refine ⟨116218435567263002240489309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77478957044842001493659539 116218435567263002240489309)
      ·
        refine ⟨43581913337723625840183491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116218435567263002240489309 43581913337723625840183491)
        ·
          refine ⟨65372870006585438760275237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43581913337723625840183491 65372870006585438760275237)
          ·
            refine ⟨12257413126234769767551607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65372870006585438760275237 12257413126234769767551607)
            ·
              refine ⟨18386119689352154651327411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12257413126234769767551607 18386119689352154651327411)
              ·
                refine ⟨27579179534028231976991117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18386119689352154651327411 27579179534028231976991117)
                ·
                  refine ⟨10342192325260586991371669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27579179534028231976991117 10342192325260586991371669)
                  ·
                    refine ⟨484790265246590015220547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10342192325260586991371669 484790265246590015220547)
                    ·
                      rfl

theorem cell23_2832377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 6].length) (baseStart_2832377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832377 prefixEnd_2832377 := by exact prefixLift 2832377
  have htrace : WordTrace (prefixWord ++ tailWord_2832377) baseStart_2832377 baseEnd_2832377 := by
    simpa [prefixWord, tailWord_2832377, baseEnd_2832377] using wordTrace_append hprefix tailTrace_2832377
  have hstable : (prefixWord ++ tailWord_2832377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832377).length < 2 ^ (prefixWord ++ tailWord_2832377).sum := by decide
  have hdescent : baseEnd_2832377 < baseStart_2832377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832418 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 3, 2, 2]
def baseStart_2832418 : Nat := 118140960795 + 2832418 * 2 ^ 59
def prefixEnd_2832418 : Nat := 4983230072969 + 3 ^ 40 * 2832418 * 2
def baseEnd_2832418 : Nat := 1454391848446604385248953

theorem tailTrace_2832418 : CollatzResearch.WordTrace tailWord_2832418 prefixEnd_2832418 1454391848446604385248953 := by
  unfold tailWord_2832418
  simp only [CollatzResearch.WordTrace]
  refine ⟨25826692863160199831780477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68871180968427199551414605 25826692863160199831780477)
  ·
    refine ⟨9685009823685074936917679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25826692863160199831780477 9685009823685074936917679)
    ·
      refine ⟨14527514735527612405376519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9685009823685074936917679 14527514735527612405376519)
      ·
        refine ⟨21791272103291418608064779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14527514735527612405376519 21791272103291418608064779)
        ·
          refine ⟨32686908154937127912097169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21791272103291418608064779 32686908154937127912097169)
          ·
            refine ⟨24515181116202845934072877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32686908154937127912097169 24515181116202845934072877)
            ·
              refine ⟨9193192918576067225277329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24515181116202845934072877 9193192918576067225277329)
              ·
                refine ⟨6894894688932050418957997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9193192918576067225277329 6894894688932050418957997)
                ·
                  refine ⟨2585585508349518907109249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6894894688932050418957997 2585585508349518907109249)
                  ·
                    refine ⟨1939189131262139180331937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2585585508349518907109249 1939189131262139180331937)
                    ·
                      refine ⟨1454391848446604385248953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1939189131262139180331937 1454391848446604385248953)
                      ·
                        rfl

theorem cell23_2832418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_2832418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832418 prefixEnd_2832418 := by exact prefixLift 2832418
  have htrace : WordTrace (prefixWord ++ tailWord_2832418) baseStart_2832418 baseEnd_2832418 := by
    simpa [prefixWord, tailWord_2832418, baseEnd_2832418] using wordTrace_append hprefix tailTrace_2832418
  have hstable : (prefixWord ++ tailWord_2832418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832418).length < 2 ^ (prefixWord ++ tailWord_2832418).sum := by decide
  have hdescent : baseEnd_2832418 < baseStart_2832418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832438 : List Nat := [5, 1, 2, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_2832438 : Nat := 118140960795 + 2832438 * 2 ^ 59
def prefixEnd_2832438 : Nat := 4983230072969 + 3 ^ 40 * 2832438 * 2
def baseEnd_2832438 : Nat := 1454402118059694306998861

theorem tailTrace_2832438 : CollatzResearch.WordTrace tailWord_2832438 prefixEnd_2832438 1454402118059694306998861 := by
  unfold tailWord_2832438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6456718807035521421428123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68871667275045561828566645 6456718807035521421428123)
  ·
    refine ⟨9685078210553282132142185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6456718807035521421428123 9685078210553282132142185)
    ·
      refine ⟨7263808657914961599106639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9685078210553282132142185 7263808657914961599106639)
      ·
        refine ⟨10895712986872442398659959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7263808657914961599106639 10895712986872442398659959)
        ·
          refine ⟨16343569480308663597989939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10895712986872442398659959 16343569480308663597989939)
          ·
            refine ⟨24515354220462995396984909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16343569480308663597989939 24515354220462995396984909)
            ·
              refine ⟨9193257832673623273869341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24515354220462995396984909 9193257832673623273869341)
              ·
                refine ⟨3447471687252608727701003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9193257832673623273869341 3447471687252608727701003)
                ·
                  refine ⟨5171207530878913091551505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3447471687252608727701003 5171207530878913091551505)
                  ·
                    refine ⟨3878405648159184818663629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5171207530878913091551505 3878405648159184818663629)
                    ·
                      refine ⟨1454402118059694306998861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3878405648159184818663629 1454402118059694306998861)
                      ·
                        rfl

theorem cell23_2832438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_2832438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832438 prefixEnd_2832438 := by exact prefixLift 2832438
  have htrace : WordTrace (prefixWord ++ tailWord_2832438) baseStart_2832438 baseEnd_2832438 := by
    simpa [prefixWord, tailWord_2832438, baseEnd_2832438] using wordTrace_append hprefix tailTrace_2832438
  have hstable : (prefixWord ++ tailWord_2832438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832438).length < 2 ^ (prefixWord ++ tailWord_2832438).sum := by decide
  have hdescent : baseEnd_2832438 < baseStart_2832438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832451 : List Nat := [1, 1, 1, 3, 1, 2, 2, 6, 2, 1, 3]
def baseStart_2832451 : Nat := 118140960795 + 2832451 * 2 ^ 59
def prefixEnd_2832451 : Nat := 4983230072969 + 3 ^ 40 * 2832451 * 2
def baseEnd_2832451 : Nat := 1454408793308202756136301

theorem tailTrace_2832451 : CollatzResearch.WordTrace tailWord_2832451 prefixEnd_2832451 1454408793308202756136301 := by
  unfold tailWord_2832451
  simp only [CollatzResearch.WordTrace]
  refine ⟨103307975061521245963073207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68871983374347497308715471 103307975061521245963073207)
  ·
    refine ⟨154961962592281868944609811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103307975061521245963073207 154961962592281868944609811)
    ·
      refine ⟨232442943888422803416914717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154961962592281868944609811 232442943888422803416914717)
      ·
        refine ⟨87166103958158551281343019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232442943888422803416914717 87166103958158551281343019)
        ·
          refine ⟨130749155937237826922014529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87166103958158551281343019 130749155937237826922014529)
          ·
            refine ⟨98061866952928370191510897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130749155937237826922014529 98061866952928370191510897)
            ·
              refine ⟨73546400214696277643633173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98061866952928370191510897 73546400214696277643633173)
              ·
                refine ⟨3447487510063888014545305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73546400214696277643633173 3447487510063888014545305)
                ·
                  refine ⟨2585615632547916010908979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3447487510063888014545305 2585615632547916010908979)
                  ·
                    refine ⟨3878423448821874016363469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2585615632547916010908979 3878423448821874016363469)
                    ·
                      refine ⟨1454408793308202756136301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3878423448821874016363469 1454408793308202756136301)
                      ·
                        rfl

theorem cell23_2832451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_2832451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832451 prefixEnd_2832451 := by exact prefixLift 2832451
  have htrace : WordTrace (prefixWord ++ tailWord_2832451) baseStart_2832451 baseEnd_2832451 := by
    simpa [prefixWord, tailWord_2832451, baseEnd_2832451] using wordTrace_append hprefix tailTrace_2832451
  have hstable : (prefixWord ++ tailWord_2832451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832451).length < 2 ^ (prefixWord ++ tailWord_2832451).sum := by decide
  have hdescent : baseEnd_2832451 < baseStart_2832451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832467 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 6, 6]
def baseStart_2832467 : Nat := 118140960795 + 2832467 * 2 ^ 59
def prefixEnd_2832467 : Nat := 4983230072969 + 3 ^ 40 * 2832467 * 2
def baseEnd_2832467 : Nat := 484805669666224897845409

theorem tailTrace_2832467 : CollatzResearch.WordTrace tailWord_2832467 prefixEnd_2832467 484805669666224897845409 := by
  unfold tailWord_2832467
  simp only [CollatzResearch.WordTrace]
  refine ⟨103308558629463280695655655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68872372419642187130437103 103308558629463280695655655)
  ·
    refine ⟨154962837944194921043483483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103308558629463280695655655 154962837944194921043483483)
    ·
      refine ⟨232444256916292381565225225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154962837944194921043483483 232444256916292381565225225)
      ·
        refine ⟨174333192687219286173918919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232444256916292381565225225 174333192687219286173918919)
        ·
          refine ⟨261499789030828929260878379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174333192687219286173918919 261499789030828929260878379)
          ·
            refine ⟨392249683546243393891317569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261499789030828929260878379 392249683546243393891317569)
            ·
              refine ⟨294187262659682545418488177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 392249683546243393891317569 294187262659682545418488177)
              ·
                refine ⟨220640446994761909063866133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294187262659682545418488177 220640446994761909063866133)
                ·
                  refine ⟨10342520952879464487368725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 220640446994761909063866133 10342520952879464487368725)
                  ·
                    refine ⟨484805669666224897845409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10342520952879464487368725 484805669666224897845409)
                    ·
                      rfl

theorem cell23_2832467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 6].length) (baseStart_2832467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832467 prefixEnd_2832467 := by exact prefixLift 2832467
  have htrace : WordTrace (prefixWord ++ tailWord_2832467) baseStart_2832467 baseEnd_2832467 := by
    simpa [prefixWord, tailWord_2832467, baseEnd_2832467] using wordTrace_append hprefix tailTrace_2832467
  have hstable : (prefixWord ++ tailWord_2832467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832467).length < 2 ^ (prefixWord ++ tailWord_2832467).sum := by decide
  have hdescent : baseEnd_2832467 < baseStart_2832467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832508 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 4, 2, 2]
def baseStart_2832508 : Nat := 118140960795 + 2832508 * 2 ^ 59
def prefixEnd_2832508 : Nat := 4983230072969 + 3 ^ 40 * 2832508 * 2
def baseEnd_2832508 : Nat := 1454438061705509033123539

theorem tailTrace_2832508 : CollatzResearch.WordTrace tailWord_2832508 prefixEnd_2832508 1454438061705509033123539 := by
  unfold tailWord_2832508
  simp only [CollatzResearch.WordTrace]
  refine ⟨51655027011157372348949089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68873369348209829798598785 51655027011157372348949089)
  ·
    refine ⟨38741270258368029261711817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51655027011157372348949089 38741270258368029261711817)
    ·
      refine ⟨29055952693776021946283863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38741270258368029261711817 29055952693776021946283863)
      ·
        refine ⟨43583929040664032919425795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29055952693776021946283863 43583929040664032919425795)
        ·
          refine ⟨65375893560996049379138693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43583929040664032919425795 65375893560996049379138693)
          ·
            refine ⟨12257980042686759258588505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65375893560996049379138693 12257980042686759258588505)
            ·
              refine ⟨9193485032015069443941379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12257980042686759258588505 9193485032015069443941379)
              ·
                refine ⟨13790227548022604165912069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9193485032015069443941379 13790227548022604165912069)
                ·
                  refine ⟨2585667665254238281108513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13790227548022604165912069 2585667665254238281108513)
                  ·
                    refine ⟨1939250748940678710831385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2585667665254238281108513 1939250748940678710831385)
                    ·
                      refine ⟨1454438061705509033123539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1939250748940678710831385 1454438061705509033123539)
                      ·
                        rfl

theorem cell23_2832508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_2832508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832508 prefixEnd_2832508 := by exact prefixLift 2832508
  have htrace : WordTrace (prefixWord ++ tailWord_2832508) baseStart_2832508 baseEnd_2832508 := by
    simpa [prefixWord, tailWord_2832508, baseEnd_2832508] using wordTrace_append hprefix tailTrace_2832508
  have hstable : (prefixWord ++ tailWord_2832508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832508).length < 2 ^ (prefixWord ++ tailWord_2832508).sum := by decide
  have hdescent : baseEnd_2832508 < baseStart_2832508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832565 : List Nat := [1, 3, 3, 4, 1, 1, 1, 4, 5]
def baseStart_2832565 : Nat := 118140960795 + 2832565 * 2 ^ 59
def prefixEnd_2832565 : Nat := 4983230072969 + 3 ^ 40 * 2832565 * 2
def baseEnd_2832565 : Nat := 161607481122535034456753

theorem tailTrace_2832565 : CollatzResearch.WordTrace tailWord_2832565 prefixEnd_2832565 161607481122535034456753 := by
  unfold tailWord_2832565
  simp only [CollatzResearch.WordTrace]
  refine ⟨103312132983108243432723149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68874755322072162288482099 103312132983108243432723149)
  ·
    refine ⟨38742049868665591287271181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103312132983108243432723149 38742049868665591287271181)
    ·
      refine ⟨14528268700749596732726693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38742049868665591287271181 14528268700749596732726693)
      ·
        refine ⟨2724050381390549387386255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14528268700749596732726693 2724050381390549387386255)
        ·
          refine ⟨4086075572085824081079383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2724050381390549387386255 4086075572085824081079383)
          ·
            refine ⟨6129113358128736121619075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4086075572085824081079383 6129113358128736121619075)
            ·
              refine ⟨9193670037193104182428613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6129113358128736121619075 9193670037193104182428613)
              ·
                refine ⟨1723813131973707034205365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9193670037193104182428613 1723813131973707034205365)
                ·
                  refine ⟨161607481122535034456753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1723813131973707034205365 161607481122535034456753)
                  ·
                    rfl

theorem cell23_2832565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 5].length) (baseStart_2832565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832565 prefixEnd_2832565 := by exact prefixLift 2832565
  have htrace : WordTrace (prefixWord ++ tailWord_2832565) baseStart_2832565 baseEnd_2832565 := by
    simpa [prefixWord, tailWord_2832565, baseEnd_2832565] using wordTrace_append hprefix tailTrace_2832565
  have hstable : (prefixWord ++ tailWord_2832565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832565).length < 2 ^ (prefixWord ++ tailWord_2832565).sum := by decide
  have hdescent : baseEnd_2832565 < baseStart_2832565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832581 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 1, 6, 2]
def baseStart_2832581 : Nat := 118140960795 + 2832581 * 2 ^ 59
def prefixEnd_2832581 : Nat := 4983230072969 + 3 ^ 40 * 2832581 * 2
def baseEnd_2832581 : Nat := 1454475545793287247510703

theorem tailTrace_2832581 : CollatzResearch.WordTrace tailWord_2832581 prefixEnd_2832581 1454475545793287247510703 := by
  unfold tailWord_2832581
  simp only [CollatzResearch.WordTrace]
  refine ⟨103312716551050278165305597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68875144367366852110203731 103312716551050278165305597)
  ·
    refine ⟨38742268706643854311989599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103312716551050278165305597 38742268706643854311989599)
    ·
      refine ⟨58113403059965781467984399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38742268706643854311989599 58113403059965781467984399)
      ·
        refine ⟨87170104589948672201976599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58113403059965781467984399 87170104589948672201976599)
        ·
          refine ⟨130755156884923008302964899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87170104589948672201976599 130755156884923008302964899)
          ·
            refine ⟨196132735327384512454447349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130755156884923008302964899 196132735327384512454447349)
            ·
              refine ⟨18387443936942298042604439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 196132735327384512454447349 18387443936942298042604439)
              ·
                refine ⟨27581165905413447063906659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18387443936942298042604439 27581165905413447063906659)
                ·
                  refine ⟨41371748858120170595859989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27581165905413447063906659 41371748858120170595859989)
                  ·
                    refine ⟨1939300727724382996680937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41371748858120170595859989 1939300727724382996680937)
                    ·
                      refine ⟨1454475545793287247510703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1939300727724382996680937 1454475545793287247510703)
                      ·
                        rfl

theorem cell23_2832581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 6, 2].length) (baseStart_2832581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832581 prefixEnd_2832581 := by exact prefixLift 2832581
  have htrace : WordTrace (prefixWord ++ tailWord_2832581) baseStart_2832581 baseEnd_2832581 := by
    simpa [prefixWord, tailWord_2832581, baseEnd_2832581] using wordTrace_append hprefix tailTrace_2832581
  have hstable : (prefixWord ++ tailWord_2832581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832581).length < 2 ^ (prefixWord ++ tailWord_2832581).sum := by decide
  have hdescent : baseEnd_2832581 < baseStart_2832581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832591 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 3, 4]
def baseStart_2832591 : Nat := 118140960795 + 2832591 * 2 ^ 59
def prefixEnd_2832591 : Nat := 4983230072969 + 3 ^ 40 * 2832591 * 2
def baseEnd_2832591 : Nat := 484826893533277402795219

theorem tailTrace_2832591 : CollatzResearch.WordTrace tailWord_2832591 prefixEnd_2832591 484826893533277402795219 := by
  unfold tailWord_2832591
  simp only [CollatzResearch.WordTrace]
  refine ⟨103313081281014049873169627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68875387520676033248779751 103313081281014049873169627)
  ·
    refine ⟨154969621921521074809754441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103313081281014049873169627 154969621921521074809754441)
    ·
      refine ⟨116227216441140806107315831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154969621921521074809754441 116227216441140806107315831)
      ·
        refine ⟨174340824661711209160973747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116227216441140806107315831 174340824661711209160973747)
        ·
          refine ⟨261511236992566813741460621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174340824661711209160973747 261511236992566813741460621)
          ·
            refine ⟨98066713872212555153047733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261511236992566813741460621 98066713872212555153047733)
            ·
              refine ⟨9193754425519927045598225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98066713872212555153047733 9193754425519927045598225)
              ·
                refine ⟨6895315819139945284198669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9193754425519927045598225 6895315819139945284198669)
                ·
                  refine ⟨2585743432177479481574501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6895315819139945284198669 2585743432177479481574501)
                  ·
                    refine ⟨484826893533277402795219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2585743432177479481574501 484826893533277402795219)
                    ·
                      rfl

theorem cell23_2832591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 4].length) (baseStart_2832591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832591 prefixEnd_2832591 := by exact prefixLift 2832591
  have htrace : WordTrace (prefixWord ++ tailWord_2832591) baseStart_2832591 baseEnd_2832591 := by
    simpa [prefixWord, tailWord_2832591, baseEnd_2832591] using wordTrace_append hprefix tailTrace_2832591
  have hstable : (prefixWord ++ tailWord_2832591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832591).length < 2 ^ (prefixWord ++ tailWord_2832591).sum := by decide
  have hdescent : baseEnd_2832591 < baseStart_2832591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832691 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 5]
def baseStart_2832691 : Nat := 118140960795 + 2832691 * 2 ^ 59
def prefixEnd_2832691 : Nat := 4983230072969 + 3 ^ 40 * 2832691 * 2
def baseEnd_2832691 : Nat := 1454532028665281817135197

theorem tailTrace_2832691 : CollatzResearch.WordTrace tailWord_2832691 prefixEnd_2832691 1454532028665281817135197 := by
  unfold tailWord_2832691
  simp only [CollatzResearch.WordTrace]
  refine ⟨103316728580651766951809927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68877819053767844634539951 103316728580651766951809927)
  ·
    refine ⟨154975092870977650427714891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103316728580651766951809927 154975092870977650427714891)
    ·
      refine ⟨232462639306466475641572337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154975092870977650427714891 232462639306466475641572337)
      ·
        refine ⟨174346979479849856731179253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232462639306466475641572337 174346979479849856731179253)
        ·
          refine ⟨16345029326235924068548055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174346979479849856731179253 16345029326235924068548055)
          ·
            refine ⟨24517543989353886102822083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16345029326235924068548055 24517543989353886102822083)
            ·
              refine ⟨36776315984030829154233125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24517543989353886102822083 36776315984030829154233125)
              ·
                refine ⟨6895559247005780466418711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36776315984030829154233125 6895559247005780466418711)
                ·
                  refine ⟨10343338870508670699628067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6895559247005780466418711 10343338870508670699628067)
                  ·
                    refine ⟨15515008305763006049442101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10343338870508670699628067 15515008305763006049442101)
                    ·
                      refine ⟨1454532028665281817135197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15515008305763006049442101 1454532028665281817135197)
                      ·
                        rfl

theorem cell23_2832691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_2832691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832691 prefixEnd_2832691 := by exact prefixLift 2832691
  have htrace : WordTrace (prefixWord ++ tailWord_2832691) baseStart_2832691 baseEnd_2832691 := by
    simpa [prefixWord, tailWord_2832691, baseEnd_2832691] using wordTrace_append hprefix tailTrace_2832691
  have hstable : (prefixWord ++ tailWord_2832691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832691).length < 2 ^ (prefixWord ++ tailWord_2832691).sum := by decide
  have hdescent : baseEnd_2832691 < baseStart_2832691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832705 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2832705 : Nat := 118140960795 + 2832705 * 2 ^ 59
def prefixEnd_2832705 : Nat := 4983230072969 + 3 ^ 40 * 2832705 * 2
def baseEnd_2832705 : Nat := 1454539217394444762360133

theorem tailTrace_2832705 : CollatzResearch.WordTrace tailWord_2832705 prefixEnd_2832705 1454539217394444762360133 := by
  unfold tailWord_2832705
  simp only [CollatzResearch.WordTrace]
  refine ⟨103317239202601047342819569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68878159468400698228546379 103317239202601047342819569)
  ·
    refine ⟨77487929401950785507114677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103317239202601047342819569 77487929401950785507114677)
    ·
      refine ⟨7264493381432886141292001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77487929401950785507114677 7264493381432886141292001)
      ·
        refine ⟨5448370036074664605969001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7264493381432886141292001 5448370036074664605969001)
        ·
          refine ⟨4086277527055998454476751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5448370036074664605969001 4086277527055998454476751)
          ·
            refine ⟨6129416290583997681715127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4086277527055998454476751 6129416290583997681715127)
            ·
              refine ⟨9194124435875996522572691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6129416290583997681715127 9194124435875996522572691)
              ·
                refine ⟨13791186653813994783859037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9194124435875996522572691 13791186653813994783859037)
                ·
                  refine ⟨5171694995180248043947139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13791186653813994783859037 5171694995180248043947139)
                  ·
                    refine ⟨7757542492770372065920709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5171694995180248043947139 7757542492770372065920709)
                    ·
                      refine ⟨1454539217394444762360133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7757542492770372065920709 1454539217394444762360133)
                      ·
                        rfl

theorem cell23_2832705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2832705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832705 prefixEnd_2832705 := by exact prefixLift 2832705
  have htrace : WordTrace (prefixWord ++ tailWord_2832705) baseStart_2832705 baseEnd_2832705 := by
    simpa [prefixWord, tailWord_2832705, baseEnd_2832705] using wordTrace_append hprefix tailTrace_2832705
  have hstable : (prefixWord ++ tailWord_2832705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832705).length < 2 ^ (prefixWord ++ tailWord_2832705).sum := by decide
  have hdescent : baseEnd_2832705 < baseStart_2832705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832725 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 1, 1, 5]
def baseStart_2832725 : Nat := 118140960795 + 2832725 * 2 ^ 59
def prefixEnd_2832725 : Nat := 4983230072969 + 3 ^ 40 * 2832725 * 2
def baseEnd_2832725 : Nat := 1454549487007534684110041

theorem tailTrace_2832725 : CollatzResearch.WordTrace tailWord_2832725 prefixEnd_2832725 1454549487007534684110041 := by
  unfold tailWord_2832725
  simp only [CollatzResearch.WordTrace]
  refine ⟨103317968662528590758547629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68878645775019060505698419 103317968662528590758547629)
  ·
    refine ⟨38744238248448221534455361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103317968662528590758547629 38744238248448221534455361)
    ·
      refine ⟨29058178686336166150841521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38744238248448221534455361 29058178686336166150841521)
      ·
        refine ⟨21793634014752124613131141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29058178686336166150841521 21793634014752124613131141)
        ·
          refine ⟨4086306377766023364962089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21793634014752124613131141 4086306377766023364962089)
          ·
            refine ⟨3064729783324517523721567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4086306377766023364962089 3064729783324517523721567)
            ·
              refine ⟨4597094674986776285582351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3064729783324517523721567 4597094674986776285582351)
              ·
                refine ⟨6895642012480164428373527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4597094674986776285582351 6895642012480164428373527)
                ·
                  refine ⟨10343463018720246642560291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6895642012480164428373527 10343463018720246642560291)
                  ·
                    refine ⟨15515194528080369963840437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10343463018720246642560291 15515194528080369963840437)
                    ·
                      refine ⟨1454549487007534684110041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15515194528080369963840437 1454549487007534684110041)
                      ·
                        rfl

theorem cell23_2832725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_2832725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832725 prefixEnd_2832725 := by exact prefixLift 2832725
  have htrace : WordTrace (prefixWord ++ tailWord_2832725) baseStart_2832725 baseEnd_2832725 := by
    simpa [prefixWord, tailWord_2832725, baseEnd_2832725] using wordTrace_append hprefix tailTrace_2832725
  have hstable : (prefixWord ++ tailWord_2832725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832725).length < 2 ^ (prefixWord ++ tailWord_2832725).sum := by decide
  have hdescent : baseEnd_2832725 < baseStart_2832725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832741 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 2, 7]
def baseStart_2832741 : Nat := 118140960795 + 2832741 * 2 ^ 59
def prefixEnd_2832741 : Nat := 4983230072969 + 3 ^ 40 * 2832741 * 2
def baseEnd_2832741 : Nat := 484852567566002207169989

theorem tailTrace_2832741 : CollatzResearch.WordTrace tailWord_2832741 prefixEnd_2832741 484852567566002207169989 := by
  unfold tailWord_2832741
  simp only [CollatzResearch.WordTrace]
  refine ⟨103318552230470625491130077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68879034820313750327420051 103318552230470625491130077)
  ·
    refine ⟨38744457086426484559173779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103318552230470625491130077 38744457086426484559173779)
    ·
      refine ⟨58116685629639726838760669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38744457086426484559173779 58116685629639726838760669)
      ·
        refine ⟨21793757111114897564535251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58116685629639726838760669 21793757111114897564535251)
        ·
          refine ⟨32690635666672346346802877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21793757111114897564535251 32690635666672346346802877)
          ·
            refine ⟨12258988375002129880051079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32690635666672346346802877 12258988375002129880051079)
            ·
              refine ⟨18388482562503194820076619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12258988375002129880051079 18388482562503194820076619)
              ·
                refine ⟨27582723843754792230114929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18388482562503194820076619 27582723843754792230114929)
                ·
                  refine ⟨20687042882816094172586197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27582723843754792230114929 20687042882816094172586197)
                  ·
                    refine ⟨484852567566002207169989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20687042882816094172586197 484852567566002207169989)
                    ·
                      rfl

theorem cell23_2832741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_2832741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832741 prefixEnd_2832741 := by exact prefixLift 2832741
  have htrace : WordTrace (prefixWord ++ tailWord_2832741) baseStart_2832741 baseEnd_2832741 := by
    simpa [prefixWord, tailWord_2832741, baseEnd_2832741] using wordTrace_append hprefix tailTrace_2832741
  have hstable : (prefixWord ++ tailWord_2832741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832741).length < 2 ^ (prefixWord ++ tailWord_2832741).sum := by decide
  have hdescent : baseEnd_2832741 < baseStart_2832741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832761 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 4, 3, 4]
def baseStart_2832761 : Nat := 118140960795 + 2832761 * 2 ^ 59
def prefixEnd_2832761 : Nat := 4983230072969 + 3 ^ 40 * 2832761 * 2
def baseEnd_2832761 : Nat := 1454567972311096543259875

theorem tailTrace_2832761 : CollatzResearch.WordTrace tailWord_2832761 prefixEnd_2832761 1454567972311096543259875 := by
  unfold tailWord_2832761
  simp only [CollatzResearch.WordTrace]
  refine ⟨103319281690398168906858137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68879521126932112604572091 103319281690398168906858137)
  ·
    refine ⟨77489461267798626680143603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103319281690398168906858137 77489461267798626680143603)
    ·
      refine ⟨116234191901697940020215405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77489461267798626680143603 116234191901697940020215405)
      ·
        refine ⟨43587821963136727507580777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116234191901697940020215405 43587821963136727507580777)
        ·
          refine ⟨32690866472352545630685583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43587821963136727507580777 32690866472352545630685583)
          ·
            refine ⟨49036299708528818446028375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32690866472352545630685583 49036299708528818446028375)
            ·
              refine ⟨73554449562793227669042563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49036299708528818446028375 73554449562793227669042563)
              ·
                refine ⟨110331674344189841503563845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73554449562793227669042563 110331674344189841503563845)
                ·
                  refine ⟨20687188939535595281918221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110331674344189841503563845 20687188939535595281918221)
                  ·
                    refine ⟨7757695852325848230719333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20687188939535595281918221 7757695852325848230719333)
                    ·
                      refine ⟨1454567972311096543259875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7757695852325848230719333 1454567972311096543259875)
                      ·
                        rfl

theorem cell23_2832761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_2832761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832761 prefixEnd_2832761 := by exact prefixLift 2832761
  have htrace : WordTrace (prefixWord ++ tailWord_2832761) baseStart_2832761 baseEnd_2832761 := by
    simpa [prefixWord, tailWord_2832761, baseEnd_2832761] using wordTrace_append hprefix tailTrace_2832761
  have hstable : (prefixWord ++ tailWord_2832761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832761).length < 2 ^ (prefixWord ++ tailWord_2832761).sum := by decide
  have hdescent : baseEnd_2832761 < baseStart_2832761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832765 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 3, 3, 2]
def baseStart_2832765 : Nat := 118140960795 + 2832765 * 2 ^ 59
def prefixEnd_2832765 : Nat := 4983230072969 + 3 ^ 40 * 2832765 * 2
def baseEnd_2832765 : Nat := 1454570026233714527609857

theorem tailTrace_2832765 : CollatzResearch.WordTrace tailWord_2832765 prefixEnd_2832765 1454570026233714527609857 := by
  unfold tailWord_2832765
  simp only [CollatzResearch.WordTrace]
  refine ⟨103319427582383677590003749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68879618388255785060002499 103319427582383677590003749)
  ·
    refine ⟨19372392671696939548125703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103319427582383677590003749 19372392671696939548125703)
    ·
      refine ⟨29058589007545409322188555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19372392671696939548125703 29058589007545409322188555)
      ·
        refine ⟨43587883511318113983282833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29058589007545409322188555 43587883511318113983282833)
        ·
          refine ⟨32690912633488585487462125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43587883511318113983282833 32690912633488585487462125)
          ·
            refine ⟨12259092237558219557798297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32690912633488585487462125 12259092237558219557798297)
            ·
              refine ⟨9194319178168664668348723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12259092237558219557798297 9194319178168664668348723)
              ·
                refine ⟨13791478767252997002523085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9194319178168664668348723 13791478767252997002523085)
                ·
                  refine ⟨5171804537719873875946157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13791478767252997002523085 5171804537719873875946157)
                  ·
                    refine ⟨1939426701644952703479809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5171804537719873875946157 1939426701644952703479809)
                    ·
                      refine ⟨1454570026233714527609857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1939426701644952703479809 1454570026233714527609857)
                      ·
                        rfl

theorem cell23_2832765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_2832765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2832765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2832765 prefixEnd_2832765 := by exact prefixLift 2832765
  have htrace : WordTrace (prefixWord ++ tailWord_2832765) baseStart_2832765 baseEnd_2832765 := by
    simpa [prefixWord, tailWord_2832765, baseEnd_2832765] using wordTrace_append hprefix tailTrace_2832765
  have hstable : (prefixWord ++ tailWord_2832765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832765).length < 2 ^ (prefixWord ++ tailWord_2832765).sum := by decide
  have hdescent : baseEnd_2832765 < baseStart_2832765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
